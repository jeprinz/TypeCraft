module TypeCraft.Purescript.Unification where

import Prelude
import Data.Tuple.Nested (type (/\), (/\))
import Prim hiding (Type)
import Control.Monad.Except as Except
import Control.Monad.State as State
import Data.Map as Map
import TypeCraft.Purescript.Grammar
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.List as List
import Data.List ((:))
import Data.Either (Either(..))
import Data.Foldable (and, traverse_)
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Util (hole')
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Context

-- * unification
type Unify a
  -- = StateT Sub (Except String) a
  = Except.ExceptT String (State.State Sub) a

type Sub
  = { subTypeVars :: Map.Map TypeVarID Type
    , subTHoles :: Map.Map TypeHoleID Type
    }

applySubType :: Sub -> Type -> Type
applySubType sub = case _ of
  Arrow md ty1 ty2 -> Arrow md (applySubType sub ty1) (applySubType sub ty2)
  -- Note from Jacob: this former version of the line was causing an infinite loop
--  ty@(THole md hid) -> applySubType sub $ maybe ty identity (Map.lookup hid sub.subTHoles)
  ty@(THole md hid) -> maybe ty identity (Map.lookup hid sub.subTHoles)
  -- Question from Jacob: Why is there a special case for Nil?
--  ty@(TNeu md id List.Nil) -> applySubType sub $ maybe ty identity (Map.lookup id sub.subTypeVars)
  ty@(TNeu md id List.Nil) -> maybe ty identity (Map.lookup id sub.subTypeVars)
  TNeu md id args -> TNeu md id ((\(TypeArg md ty) -> TypeArg md (applySubType sub ty)) <$> args)

subTypeArg :: Sub -> TypeArg -> TypeArg
subTypeArg sub (TypeArg md ty) = TypeArg md (applySubType sub ty)

applySubChange :: Sub -> Change -> Change
applySubChange sub = case _ of
  CArrow ty1 ty2 -> CArrow (applySubChange sub ty1) (applySubChange sub ty2)
  ty@(CHole hid) -> maybe ty tyInject (Map.lookup hid sub.subTHoles)
  -- Question from Jacob: Why is there a special case for Nil?
  -- Note from Jacob: this former version of the line was causing an infinite loop
--  ty@(CNeu id List.Nil) -> applySubChange sub $ maybe ty tyInject (Map.lookup id sub.subTypeVars)
  ty@(CNeu id List.Nil) -> maybe ty tyInject (Map.lookup id sub.subTHoles)
  CNeu id args -> CNeu id (applySubChangeParam sub <$> args)
  Replace ty1 ty2 -> Replace (applySubType sub ty1) (applySubType sub ty2)
  Plus ty ch -> Plus (applySubType sub ty) (applySubChange sub ch)
  Minus ty ch -> Minus (applySubType sub ty) (applySubChange sub ch)
--data ChangeParam
--  = ChangeParam Change
--  | PlusParam Type
--  | MinusParam Type
applySubChangeParam :: Sub -> ChangeParam -> ChangeParam
applySubChangeParam sub = case _ of
    ChangeParam ch -> ChangeParam (applySubChange sub ch)
    PlusParam ty -> PlusParam (applySubType sub ty)
    MinusParam ty -> MinusParam (applySubType sub ty)

emptySub :: Sub
emptySub = { subTypeVars: Map.empty, subTHoles: Map.empty }

runUnify :: forall a. Unify a -> Either String (a /\ Sub)
-- runUnify m = either (const Nothing) pure $ Except.runExcept (State.runStateT m emptySub)
runUnify m = case State.runState (Except.runExceptT m) emptySub of
  Left msg /\ _ -> Left msg
  Right a /\ sub -> Right (a /\ sub)

normThenUnify :: TypeAliasContext -> Type -> Type -> Unify Type
normThenUnify actx ty1 ty2 = unify (normalizeType actx ty1) (normalizeType actx ty2)

-- NOTE: output substitution substitutes holes in ty2 for things in ty1
-- either (const Nothing) pure $ Except.runExcept (State.runStateT m emptySub)
unify :: Type -> Type -> Unify Type
unify ty1 ty2 = case ty1 /\ ty2 of
  THole _ hid1 /\ THole _ hid2 | hid1 == hid2 -> pure ty1 -- need this case, otherwise unifying a hole with itself would fail occurs check!
  THole _ hid /\ _ -> do
    checkOccurs hid ty2
    State.modify_ (\sub -> sub { subTHoles = Map.insert hid ty2 sub.subTHoles })
    pure ty2
  _ /\ THole _ hid -> do
    checkOccurs hid ty1
    State.modify_ (\sub -> sub { subTHoles = Map.insert hid ty2 sub.subTHoles })
    pure ty2
  Arrow md tyA1 tyB1 /\ Arrow _ tyA2 tyB2 -> Arrow md <$> unify tyA1 tyA2 <*> unify tyB1 tyB2
  -- TODO: handle type arguments
  _
    | ty1 == ty2 -> pure ty1
    | otherwise -> Except.throwError $ "types do not unify: (" <> show ty1 <> ") ~ (" <> show ty2 <> ")"

-- throws error if the type hole id appears in the type
checkOccurs :: TypeHoleID -> Type -> Unify Unit
checkOccurs hid ty = go ty
  where
  go = case _ of
    Arrow _ ty1 ty2 -> do
      checkOccurs hid ty1
      checkOccurs hid ty2
    THole _ hid' -> when (hid == hid') <<< Except.throwError $ "occurence check fail; the type hole id '" <> show hid <> "' appears in the type '" <> show ty <> "'"
    TNeu _ _ args -> traverse_ (go <<< \(TypeArg _ ty) -> ty) args

-- create neutral form from variable of first type that can fill the hole of the
-- second type
fillNeutral :: TypeAliasContext -> PolyType -> TermVarID -> Type -> Unify Term
fillNeutral actx pty id ty = fillNeutralImpl actx pty id ty emptySub List.Nil

fillNeutralImpl :: TypeAliasContext -> PolyType -> TermVarID -> Type -> Sub -> List.List TypeArg -> Unify Term
fillNeutralImpl actx pty id ty sub tyArgs = case pty of
  Forall x pty' ->
    let h = (freshTHole unit) in
    fillNeutralImpl actx pty' id ty sub{subTypeVars= Map.insert x h sub.subTypeVars} ((TypeArg defaultTypeArgMD h) List.: tyArgs)
  PType ty' -> fillNeutral' actx (applySubType sub ty') id ty tyArgs

{-
NOTE: when creating a variable to place into a new neutral form, if the type is a hole, you can prioritize as many or as few
arguments. fillNeutral'' prioritizes many arguments, and fillNeutral' prioritizes few.
-}
--fillNeutral'' :: TypeAliasContext -> Type -> TermVarID -> Type -> List.List TypeArg -> Unify Term
--fillNeutral'' actx ty id ty' tyArgs = case ty of
--  Arrow _ ty1 ty2 ->
--    (\tm -> App defaultAppMD tm (freshHole unit) ty1 ty2)
--      <$> fillNeutral'' actx ty2 id ty' tyArgs
--  _ -> do
--    void $ normThenUnify actx ty' ty
--    pure $ Var defaultVarMD id tyArgs

-- first type is that of variable, second type is that of location that variable will fill
fillNeutral' :: TypeAliasContext -> Type -> TermVarID -> Type -> List.List TypeArg -> Unify Term
fillNeutral' actx ty id ty' tyArgs =
--    \trace ("getting called with: " <> show ty') \_ ->
    case runUnify (normThenUnify actx ty' ty) of
    Left msg ->
        case ty of
        Arrow _ ty1 ty2 -> do
            tm <- fillNeutral' actx ty2 id ty' tyArgs
            pure $ App defaultAppMD tm (freshHole unit) ty1 ty2
        _ -> Except.throwError msg
    Right (_ /\ sub) -> do
        State.modify_ (\_ -> sub)
        pure $ Var defaultVarMD id tyArgs -- TODO: this is where we need to not just have Nil but actually use the type parameters. Probably have the Var get passed as argument from fillNeutral.
--runUnify :: forall a. Unify a -> Either String (a /\ Sub)

subTerm :: Sub -> Term -> Term
subTerm sub term =
    let rec = subTerm sub in
    let st = applySubType sub in
    case term of
    App md t1 t2 argTy outTy -> App md (rec t1) (rec t2) (st argTy) (st outTy)
    Lambda md tBind argTy body bodyTy -> Lambda md tBind (st argTy) (rec body) (st bodyTy)
    Var md x tyArgs -> Var md x (map (\(TypeArg md ty) -> TypeArg md (st ty)) tyArgs)
    Let md tBind tyBinds def defTy body bodyTy -> Let md tBind tyBinds (rec def) (st defTy) (rec body) (st bodyTy)
    Data md tyBind tyBinds ctrs body bodyTy -> Data md tyBind tyBinds (map (subConstructor sub) ctrs) (rec body) (st bodyTy)
    TLet md tyBind tyBinds def body bodyTy -> TLet md tyBind tyBinds (st def) (rec body) (st bodyTy)
    TypeBoundary md ch body -> TypeBoundary md (applySubChange sub ch) (rec body)
    ContextBoundary md x ch body -> ContextBoundary md x (subVarChange sub ch) (rec body)
    Hole md -> Hole md
    Buffer md def defTy body bodyTy -> Buffer md (rec def) (st defTy) (rec body) (st bodyTy)

subTermPath :: Sub -> UpPath -> UpPath
subTermPath sub List.Nil = List.Nil
subTermPath sub (tooth List.: rest) = (subTermTooth sub tooth) List.: (subTermPath sub rest)

subTermTooth :: Sub -> Tooth -> Tooth
subTermTooth sub tooth =
    let rec = subTerm sub in
    let st = applySubType sub in
    case tooth of
        App1 md {-Term-} t2 argTy bodyTy -> App1 md (rec t2) (st argTy) (st bodyTy)
        App2 md t1 {-Term-} argTy bodyTy -> App2 md (rec t1) (st argTy) (st bodyTy)
        Lambda3 md tBind argTy {-Term-} bodyTy -> Lambda3 md tBind (st argTy) (st bodyTy)
        Let3 md tBind tyBinds {-Term-} defTy body bodyTy -> Let3 md tBind tyBinds (st defTy) (rec body) (st bodyTy)
        Let5 md tBind tyBinds def defTy {-Term-} bodyTy -> Let5 md tBind tyBinds (rec def) (st defTy) (st bodyTy)
        Buffer1 md {-Term-} defTy body bodyTy -> Buffer1 md (st defTy) (rec body) (st bodyTy)
        Buffer3 md def defTy {-Term-} bodyTy -> Buffer3 md (rec def) (st defTy) (st bodyTy)
        TypeBoundary1 md ch {-Term-} -> TypeBoundary1 md (applySubChange sub ch)
        ContextBoundary1 md x vch {-Term-} -> ContextBoundary1 md x (subVarChange sub vch)
        TLet4 md tyBind tyBinds def {-Term-} bodyTy -> TLet4 md tyBind tyBinds (st def) (st bodyTy)
        Data4 md tyBind tyBinds ctrs {-Term-} bodyTy -> Data4 md tyBind tyBinds (map (subConstructor sub) ctrs) (st bodyTy)
        _ -> unsafeThrow "Either wasn't a term tooth, or I forgot a case in subTermTooth"

--Need subTypeTooth as well...
--
--
--Lambda2 LambdaMD TermBind {-Type-} Term Type
--Let4 LetMD TermBind (List TypeBind) Term {-Type-} Term Type
--Buffer2 BufferMD Term {-Type-} Term Type
--TLet3 TLetMD TypeBind (List TypeBind) {-Type-} Term Type
--Arrow1 ArrowMD {-Type-} Type
--Arrow2 ArrowMD Type {-Type-}
--TypeArg1 TypeArgMD {-Type-}
--
--
--TNeu1 TNeuMD TypeVarID {-List TypeArg-}
--TypeArgListCons2 (TypeArg) {-List TypeArg-}
--
--TypeArgListCons1 {-TypeArg-} (List TypeArg)

subTypePath :: Sub -> UpPath -> UpPath
subTypePath sub List.Nil = List.Nil
subTypePath sub (tooth : teeth) =
    let sterm = subTerm sub in
    let stype = applySubType sub in
    case tooth of
        Lambda2 md tBind {--} body bodyTy -> (Lambda2 md tBind {--} (sterm body) (stype bodyTy)) : subTermPath sub teeth
        Let4 md tBind tyBinds def {-defTy-} body bodyTy -> Let4 md tBind tyBinds (sterm def) {--} (sterm body) (stype bodyTy) : subTermPath sub teeth
        Buffer2 md def {-defTy-} body bodyTy -> Buffer2 md (sterm def) {--} (sterm body) (stype bodyTy) : subTermPath sub teeth
        TLet3 md tyBind tyBinds {-def-} body bodyTy -> TLet3 md tyBind tyBinds {--} (sterm body) (stype bodyTy) : subTermPath sub teeth
        Arrow1 md {--} ty2 -> Arrow1 md {--} (stype ty2) : subTypePath sub teeth
        Arrow2 md ty1 {--} -> Arrow2 md (stype ty1) {--} : subTypePath sub teeth
        TypeArg1 md {--} -> TypeArg1 md {--} : subTypeArgPath sub teeth
        _ -> unsafeThrow "Either wasn't a type path, or I forgot a case in subTypePath"

subTypeArgPath :: Sub -> UpPath -> UpPath
subTypeArgPath sub List.Nil = List.Nil
subTypeArgPath sub (tooth : teeth) =
    case tooth of
        TypeArgListCons1 {--} tyArgs -> TypeArgListCons1 {--} (map (subTypeArg sub) tyArgs) : subTypeArgListPath sub teeth
        _ -> unsafeThrow "Either wasn't a TypeArg path, or I forgot a case in subTypeArgPath"

subTypeArgListPath :: Sub -> UpPath -> UpPath
subTypeArgListPath sub List.Nil = List.Nil
subTypeArgListPath sub (tooth : teeth) =
    case tooth of
        TypeArgListCons2 tyArg -> TypeArgListCons2 (subTypeArg sub tyArg) : subTypeArgListPath sub teeth
        TNeu1 md x {--} -> TNeu1 md x : subTypeArgListPath sub teeth
        _ -> unsafeThrow "Either wasn't a TypeArgList path, or I forgot a case in subTypeArgListPath"


subPolyChange :: Sub -> PolyChange -> PolyChange
subPolyChange sub polyChange =
    let rec = subPolyChange sub in
    case polyChange of
        CForall x pc -> CForall x (rec pc)
        PPlus x pc -> PPlus x (rec pc)
        PMinus x pc -> PMinus x (rec pc)
        PChange ch -> PChange (applySubChange sub ch)

subPolyType :: Sub -> PolyType -> PolyType
subPolyType sub = case _ of
  Forall x pt -> Forall x (subPolyType sub pt)
  PType ty -> PType (applySubType sub ty)


subVarChange :: Sub -> VarChange -> VarChange
subVarChange sub varChange =
    case varChange of
        VarTypeChange pc -> VarTypeChange (subPolyChange sub pc)
        VarDelete pt -> VarDelete (subPolyType sub pt)
        VarInsert pt -> VarInsert (subPolyType sub pt)

subConstructor :: Sub -> Constructor -> Constructor
subConstructor sub (Constructor md x ctrParams) = Constructor md x (map (subCtrParam sub) ctrParams)

subCtrParam :: Sub -> CtrParam -> CtrParam
subCtrParam sub (CtrParam md ty) = CtrParam md (applySubType sub ty)

normalizeType :: TypeAliasContext -> Type -> Type
normalizeType actx ty =
    case ty of
    Arrow md ty1 ty2 -> Arrow md (normalizeType actx ty1) (normalizeType actx ty2)
    THole md x -> THole md x
    TNeu md x args -> case Map.lookup x actx of
        Nothing -> TNeu md x (map (\(TypeArg md ty) -> TypeArg md (normalizeType actx ty)) args)
        Just (tyBinds /\ def) ->
            let types = map (\(TypeArg _ ty) -> ty) args in
            let ids = map (\(TypeBind _ id) -> id) tyBinds in
            let sub = Map.fromFoldable (List.zip ids types) in
            normalizeType actx (applySubType {subTypeVars: sub, subTHoles: Map.empty} def)

subCtx :: Sub -> TermContext -> TermContext
subCtx sub ctx = map (subPolyType sub) ctx

subTACtx :: Sub -> TypeAliasContext -> TypeAliasContext
subTACtx sub actx = map (\(tyBinds /\ ty) -> tyBinds /\ applySubType sub ty) actx

subAllCtx :: Sub -> AllContext -> AllContext
subAllCtx sub ctxs = ctxs{ctx = subCtx sub ctxs.ctx, actx = subTACtx sub ctxs.actx}