module TypeCraft.Purescript.ChangeTerm where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.TypeChangeAlgebra
import TypeCraft.Purescript.TypeChangeAlgebra2

import Data.List (List(..), (:), foldr, null)
import Data.List as List
import Data.Map.Internal (empty, lookup, insert)
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple (snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Util (lookup')
import TypeCraft.Purescript.Freshen
import TypeCraft.Purescript.Unification
import TypeCraft.Purescript.Kinds (bindsToKind)
import TypeCraft.Purescript.Util (delete')
import TypeCraft.Purescript.Alpha (applySubChange, applySubChangeGen)
import Debug (trace)
import TypeCraft.Purescript.Util (insert')

-- calls chTerm, but if it returns a non-id change, it wraps in a boundary
-- TODO: Im not sure how I should understand this. I think that this is used for places where we assume that the output change is id, but I'm not sure what the criteria for that is.
chTermBoundary :: KindChangeCtx -> ChangeCtx -> Change -> Term -> Term
chTermBoundary kctx ctx c t =
    let c /\ t' = chTerm kctx ctx c t in
    if chIsId c
        then t'
        else
            TypeBoundary defaultTypeBoundaryMD (invert c) t'

getRightCtxInj :: ChangeCtx -> ChangeCtx
getRightCtxInj ctx =
    let ctx1_ /\ ctx2 = getCtxEndpoints ctx in
    ctxInject ctx2

{-
chTerm inputs D, C1, t1 and outputs t2, and C2 such that
D |- t1 --[C1 o C2] --> t2
-}
chTerm :: KindChangeCtx -> ChangeCtx -> Change -> Term -> Change  /\ Term
chTerm kctx ctx c t =
    let cRes /\ tRes = (
        case c /\ t of
            cin /\ (App md t1 t2 argTy outTy) ->
                let c1 /\ t1' = chTerm kctx ctx (CArrow (tyInject argTy) cin) t1 in
                case c1 of
                (Minus _ c1') ->
                    let ct2 /\ t2' = chTerm kctx ctx (tyInject argTy) t2 in
                    c1' /\ Buffer defaultBufferMD t2 (snd (getEndpoints ct2)) t1' (snd (getEndpoints c1))
                (CArrow c1a c1b) ->
                    trace ("c1b is " <> show c1b) \_ ->
                    let c2 /\ t2' = chTerm kctx ctx c1a t2 in
                    let t2'' = if chIsId c2
                        then t2'
                        else TypeBoundary defaultTypeBoundaryMD (invert c2) t2'
                    in c1b /\ App md t1' t2'' (snd (getEndpoints c1a)) (snd (getEndpoints c1b))
                otherChange ->
                    let ct2 /\ t2' = chTerm kctx ctx (tyInject argTy) t2 in
                    tyInject (outTy)
                    /\ TypeBoundary defaultTypeBoundaryMD (Replace (snd (getEndpoints otherChange)) (snd (getEndpoints cin)))
                       (Buffer defaultBufferMD t2' (snd (getEndpoints ct2)) t1' (snd (getEndpoints otherChange)))
--                _ -> composeChange (Minus argTy (tyInject (snd (getEndpoints cin)))) c1 /\ -- is this right?
--                     Buffer defaultBufferMD t1' (snd (getEndpoints c1)) t1'
            cin /\ (Var md x tArgs) -> -- TODO: actually do var case for real
                -- try the polymorphism case
--                case getSubstitution cin (lookup x ctx)
                let xVarCh = lookup' x ctx in
                trace ("In var case here: cin is" <> show cin <> " and xVarCh is: " <> show xVarCh) \_ ->
                case xVarCh of
                    -- TODO: CtxBoundary, and still need to change args!
                    VarDelete _ -> tyInject (snd (getEndpoints cin)) /\ Hole defaultHoleMD -- later use context boundary
--                    VarTypeChange xChange ->
--                        let tryPolymorhpismCase =
----                                do _ <- (if pChIsId xChange then Just xChange else Nothing) -- (for now at least), polymorphism thing only works if variable type is unchanged in context
----                                   let ty = (snd (getEndpoints xChange))
----                                   sub <- getSubstitution cin ty
----                                   let c' = composeChange (invert c) (subChange sub (tyInject ty))
----                                   pure $ c' /\ (Var md x (unsafeThrow "need to deal with tArgs!"))
--                                Nothing
--                        in case tryPolymorhpismCase  of
--                           Just res -> res
--                           Nothing -> hole -- xChange /\ Var md x (unsafeThrow "need to deal with tArgs!") -- if the polymorhpism case didn't apply, simply return the change and leave the variable as is
--                    VarTypeChange (PChange cVar) ->
--                        if not (chIsId cin) then tyInject (snd (getEndpoints cin)) /\ Hole defaultHoleMD
--                        else cVar /\ Var md x tArgs
                    VarInsert _ -> unsafeThrow "shouldn't get here"
                    VarTypeChange pch ->
                        if chIsId cin then
                            let ch /\ tyArgs' = chTypeArgs2 kctx tArgs pch in
                            ch /\ Var md x tyArgs'
                        else if pChIsId pch then
                            tyInject (snd (getEndpoints cin)) /\ Buffer defaultBufferMD (Var md x tArgs) (fst (getEndpoints cin)) (Hole defaultHoleMD) (snd (getEndpoints cin)) -- TODO: shouldn't we call chTypeArgs2???
                        else if null tArgs && pch == PChange cin then
                            (tyInject (snd (getEndpoints cin))) /\ Var md x Nil
                        else unsafeThrow ("I didn't think it was possible to have a non-id, non-equal typechange both from ctx and term in var case! (or equal but with tyArgs)" -- TODO: it is possible, for example id<A -> A> id<A>, and then apply a typechange to the type of id. In this situation, it should just use a TypeBoudnary!
                                <> "\n pch is: " <> show pch <> " and cin is: " <> show cin
                                )
            (CArrow c1 c2) /\ (Lambda md tBind@(TermBind _ x) ty t bodyTy) ->
                if not (ty == fst (getEndpoints c1)) then unsafeThrow "shouldn't happen 1" else
                if not (bodyTy == fst (getEndpoints c2)) then unsafeThrow "shouldn't happen 2" else
                let c2' /\ t' = chTerm kctx (insert x (VarTypeChange (PChange c1)) ctx) c2 t in
                let ty' = snd (getEndpoints c1) in
                (CArrow (tyInject ty') c2') /\ Lambda md tBind ty' t' (snd (getEndpoints c2'))
            (Minus ty1 c) /\ (Lambda md tBind@(TermBind _ x) ty2 t bodyTy) ->
                if not (ty1 == ty2) then unsafeThrow "shouldn't happen 3" else
                if not (bodyTy == fst (getEndpoints c)) then unsafeThrow "shouldn't happen 4" else
                let c2' /\ t' = chTerm kctx (insert x (VarDelete (PType ty2)) ctx) c t in
                c2' /\ t'
            (Minus ty c) /\ t ->
                let c' /\ t' = chTerm kctx ctx c t in
                (CArrow (tyInject ty) c') /\ App defaultAppMD t' (Hole defaultHoleMD) ty (snd (getEndpoints c))
            (Plus ty c) /\ t ->
                let tBind@(TermBind _ x) = (freshTermBind Nothing) in
                let ctx' = insert x (VarInsert (PType ty)) ctx in
                let c' /\ t' = chTerm kctx ctx' c t in
                (CArrow (tyInject ty) c') /\ Lambda defaultLambdaMD tBind ty t' (snd (getEndpoints c'))
            c /\ Let md tBind@(TermBind _ x) binds t1 ty t2 tyBody ->
                -- TODO: need to include the binds into the kctx for some things I think?
                if not (fst (getEndpoints c) == tyBody) then unsafeThrow "shouldn't happen 5" else
                let kctx' = addLetToKCCtx kctx binds in
                let ty' /\ tyCh = chType kctx' ty in
--                let ctx' = addLetToCCtx ctx tBind binds ty' in
                let ctx' = insert' x (VarTypeChange (tyBindsWrapChange binds tyCh)) ctx in
                let c2 /\ t2' = chTerm kctx ctx' c t2 in
                trace ("In Let, tyCH is: " <> show tyCh) \_ ->
                let t1'= chTermBoundary kctx' ctx' tyCh t1 in -- TODO: is this correct!?! should it first apply the kctx to the type?
                -- TODO: apply change to x to the let itself!
                c2 /\ Let md tBind binds t1' ty' t2' (snd (getEndpoints c2)) -- TODO: certianly, this will be a bug if a type is deleted for example. ty needs to get updated somehow!
            c /\ Buffer md t1 ty1 t2 bodyTy ->
                let c1 /\ t1' = chTerm kctx ctx (tyInject ty1) t1 in
                let c2 /\ t2' = chTerm kctx ctx c t2 in
                c2 /\ Buffer md t1' (snd (getEndpoints c1)) t2' (snd (getEndpoints c2))
            c /\ TLet md x params ty t bodyType ->
                if not (fst (getEndpoints c) == bodyType) then unsafeThrow "shouldn't happen 6" else
                let ty' /\ tyChange = chType kctx ty in
--                let c' /\ t' = chTerm (ctxKindCons kctx x (TVarTypeChange tyChange)) ctx c t in
                let typeAliasChange = hole' "chTerm" in
                let c' /\ t' = chTerm (ctxKindCons kctx x (TVarKindChange (kindInject (tyBindsWrapKind params Type)) (Just typeAliasChange))) ctx c t in
                c' /\ TLet md x params ty' t' (snd (getEndpoints c')) -- TODO: what if c references x? Then it is out of scope above.
            c /\ Hole md -> (tyInject (snd (getEndpoints c))) /\ Hole md
            c /\ Data md tyBind tyBinds ctrs body bodyTy ->
                let ctrsCh /\ ctrs' = chCtrList kctx ctrs in
                let kctx' /\ ctx' = addDataToCtx (kctx /\ ctx) tyBind tyBinds ctrsCh in
                let c' /\ body' = chTerm kctx' ctx' c body in
                c' /\ Data md tyBind tyBinds ctrs' body' (snd (getEndpoints c'))
            c /\ TypeBoundary md ch body ->
                let ch' = composeChange ch c in
                let tyChInside = tyInject (fst (getEndpoints ch)) in
                let chBackUp /\ body' = chTerm kctx ctx tyChInside body in
                tyChInside /\ TypeBoundary md (composeChange (invert chBackUp) ch') body'
            c /\ ContextBoundary md x vCh body ->
                -- case lookup x ?kctx of
                --     Just xChInCtx -> hole' "chTerm"
                --     Nothing -> hole' "chTerm"
                hole' "chTerm" -- TODO: jacob
            cin /\ t -> tyInject (snd (getEndpoints cin)) /\ TypeBoundary defaultTypeBoundaryMD cin t
        )
    in
        let ch' /\ t' = doInsertArgs cRes tRes in
        ch' /\ t'
{-
Inputs (implicit D) C1 t, and outputs t2 and C2 such that
D |- t1 ---[C1 o (C2 ^-1)]---> t2
-}
doInsertArgs :: Change -> Term -> Change /\ Term
doInsertArgs (Plus ty c) t = doInsertArgs c (App defaultAppMD t (Hole defaultHoleMD) ty (snd (getEndpoints c)))
doInsertArgs c t = c /\ t

-- here, the output Change is the Change inside the input PolyChange.
chTypeArgs2 :: KindChangeCtx -> List TypeArg -> PolyChange -> Change /\ (List TypeArg)
chTypeArgs2 kctx Nil (PChange ch) = ch /\ Nil
chTypeArgs2 kctx (tyArg@(TypeArg _ ty) : tyArgs) (CForall x pc) =
    let ch /\ tyArgsOut = chTypeArgs2 kctx tyArgs pc in
    let ch' = applySubChange { subTypeVars : (insert x ty empty) , subTHoles : empty} ch in -- What is this line doing????
    ch' /\ tyArg : tyArgsOut
chTypeArgs2 kctx tyArgs (PPlus x pc) =
    -- TODO: Here is where we need to deal with ADDING subs to holes!
    let ch /\ tyArgsOut = chTypeArgs2 kctx tyArgs pc in
    let ty = (freshTHole unit) in
    -- This is not right! applySubChange will put SubTypeChange for that var into each hole sub. But we need SubInsert
    let ch' = applySubChangeGen { subTypeVars : (insert x (SubInsert ty) empty) , subTHoles : empty} ch in -- What is this line doing????
    trace ("the change afeter applying the sub is: " <> show ch') \_ ->
    ch' /\ (TypeArg defaultTypeArgMD ty) : tyArgsOut
chTypeArgs2 kctx ((TypeArg _ ty) : tyArgs) (PMinus x pc) =
    -- TODO: Here is where we need to deal with removing subs from holes
    -- Similarly, here we need to place SubDelete for each hole sub
    let ch /\ tyArgsOut = chTypeArgs2 kctx tyArgs pc in
    let ch' = applySubChangeGen { subTypeVars : (insert x (SubDelete ty) empty) , subTHoles : empty} ch in -- What is this line doing????
    ch' /\ tyArgsOut
chTypeArgs2 _ _ _ = unsafeThrow "invalid input to chTypeArgs2, or I forgot a case"

-- could avoid returning Type (because you can get it from the change with getEndpoints), if I put metadata into Change
chType :: KindChangeCtx -> Type -> Type /\ Change
chType kctx (Arrow md t1 t2) =
    let t1' /\ c1 = chType kctx t1 in
    let t2' /\ c2 = chType kctx t2 in
    Arrow md t1' t2' /\ CArrow c1 c2
chType kctx (THole md x w s) = THole md x w s /\ CHole x w (subInject s) -- TODO: is this right?
chType kctx (TNeu md tv args) =
    case tv of
        TypeVar x ->
            case lookup x kctx of
            Nothing -> unsafeThrow "shouldn't get here! all variables should be bound in the context!"
            Just (TVarKindChange kindChange taCh) ->
                case taCh of
                Nothing ->
                    let args' /\ cargs = chTypeArgs kctx kindChange args in
                    TNeu md (TypeVar x) args' /\ CNeu (CTypeVar x) cargs
                Just taCh -> hole' "chType" -- if the type variable was that of a type alias, we must deal with the possiblity that the type alias was changed
            Just (TVarDelete name kind maybeValue) ->
                let args' /\ cargs = chTypeArgs kctx (kindInject kind) args in
                TNeu md (CtxBoundaryTypeVar kind maybeValue name x) args' /\ CNeu (PlusCtxBoundaryTypeVar kind maybeValue name x) cargs
            Just (TVarInsert _ kind maybeValue) -> unsafeThrow "Shouldn't happen chType 1"
        cbtv@(CtxBoundaryTypeVar k mtv name x) -> -- because this represents an Insert boundary, x can't be in kctx. Therefore, we output the identity
            let nothingCase =
                    let args' /\ cargs = chTypeArgs kctx (kindInject k) args in
                    TNeu md cbtv args' /\ CNeu (CCtxBoundaryTypeVar k mtv name x) cargs
            in
            case lookup x kctx of
            Nothing -> nothingCase
            Just (TVarInsert name k2 maybeValue) ->
                -- If the kind changed, then just to simplify things, don't consider this the same variable anymore.
                if not (k == k2) then nothingCase else
                let args' /\ cargs = chTypeArgs kctx (kindInject k) args in
                TNeu md (TypeVar x) args' /\ CNeu (MinusCtxBoundaryTypeVar k maybeValue name x) cargs -- Technically the name could have changed, but I think its fine.
            Just _ -> unsafeThrow "Shouldn't happen chType 2"


chTypeArgs :: KindChangeCtx -> KindChange -> List TypeArg -> List TypeArg /\ List ChangeParam
chTypeArgs kctx KCType Nil = Nil /\ Nil
chTypeArgs kctx (KPlus kc) params =
    let tparams /\ cparams = chTypeArgs kctx kc params in
    let newType = freshTHole unit in
    (TypeArg defaultTypeArgMD newType : tparams) /\ (PlusParam newType : cparams)
chTypeArgs kctx (KCArrow kc) (TypeArg md t : params) =
    let t' /\ c = chType kctx t in
    let tparams /\ cparams = chTypeArgs kctx kc params in
    ((TypeArg md t') : tparams) /\ (ChangeParam c) : cparams
chTypeArgs kctx (KMinus kc) (TypeArg md t : params) =
    let tparams /\ cparams = chTypeArgs kctx kc params in
    tparams /\ (MinusParam t) : cparams
chTypeArgs kctx _ _ = unsafeThrow "shouldn't get here: types didn't line up with kindchanges (or I missed a case)"

-- The output Change is the change to the constructor itself
chCtrList :: KindChangeCtx -> List Constructor ->  ListCtrChange /\ List Constructor
chCtrList kctx ctrs = case ctrs of
    Nil -> ListCtrChangeNil /\ Nil
    Cons (Constructor md tBind@(TermBind _ x) ctrParams) ctrs ->
        let ctrCh /\ ctrParams' = chParamList kctx ctrParams in
        let ctrChs' /\ ctrs' = chCtrList kctx ctrs in
        ListCtrChangeCons x ctrCh ctrChs' /\ (Constructor md tBind ctrParams') : ctrs'

-- The output Change is the change to the constructor itself
--chCtr :: KindChangeCtx -> Constructor -> ListCtrParamChange /\ Constructor
--chCtr = hole' "chCtr"

chCtrParam :: KindChangeCtx -> CtrParam -> Change /\ CtrParam
chCtrParam kctx (CtrParam md t) =
    let t' /\ c = chType kctx t in c /\ CtrParam md t'

chParamList :: KindChangeCtx -> List CtrParam -> ListCtrParamChange /\ List CtrParam
chParamList _ Nil = ListCtrParamChangeNil /\ Nil
chParamList kctx (param : params) =
    let ch /\ param' = chCtrParam kctx param in
    let chs /\ params' = chParamList kctx params in
    (ListCtrParamChangeCons ch chs) /\ param' : params'

chTypeBindList :: List TypeBind -> ListTypeBindChange
chTypeBindList Nil = ListTypeBindChangeNil
chTypeBindList (tyBind : tyBinds) = ListTypeBindChangeCons tyBind (chTypeBindList tyBinds)

chTypeParamList :: KindChangeCtx -> List TypeArg -> ListTypeArgChange /\ List TypeArg
--chTypeParamList kctx tyArgs = (tyArgs <#> \(TypeArg _ ty) -> tyInject ty) /\ tyArgs -- TODO: impl
chTypeParamList kctx Nil = ListTypeArgChangeNil /\ Nil
chTypeParamList kctx ((TypeArg md ty) : tyArgs) =
    let ty' /\ ch = chType kctx ty in
    let chs /\ tyArgs' = chTypeParamList kctx tyArgs in
    ListTypeArgChangeCons ch chs /\ (TypeArg md ty') : tyArgs'

---- inputs PolyChange by which var type changed, outputs new args and TypeChange by which the whole neutral form changes
chTypeArgsNeu :: PolyChange -> List TypeArg -> Change /\ List TypeArg
chTypeArgsNeu (PChange ch) Nil = ch /\ Nil
chTypeArgsNeu (CForall x ch) (arg : args) = hole' "chTypeArgsNeu"
chTypeArgsNeu (PMinus x ch) (arg : args) = hole' "chTypeArgsNeu"
chTypeArgsNeu (PPlus x ch) args = hole' "chTypeArgsNeu"
chTypeArgsNeu _ _ = unsafeThrow "shouldn't happen 7"
-- TODO: there is something nontrivial to think about here. It should track a context so it knows which arguments got deleted etc.
-- also if a type argument gets affected by the KindChangeCtx, then that needs to be reflected as well...



--------------------------------------------------------------------------------
--------------- Helper functions for adjusting the contexts --------------------
--------------------------------------------------------------------------------

-- Constructors, datatype itself, and recursor
addDataToCtx :: CAllContext -> TypeBind -> List TypeBind -> ListCtrChange -> CAllContext
addDataToCtx (kctx /\ ctx) tyBind@(TypeBind xmd dataType) tyBinds ctrsCh =
    insert dataType (TVarKindChange (kindInject (bindsToKind tyBinds)) Nothing) kctx
    /\ adjustCtxByCtrChanges dataType (map (\(TypeBind _ x) -> x) tyBinds) ctrsCh ctx


adjustCtxByCtrChanges :: {-the datatype id-}TypeVarID -> {-the datatype's parameters-}List TypeVarID -> ListCtrChange -> ChangeCtx -> ChangeCtx
adjustCtxByCtrChanges dataType tyVarIds ctrsCh ctx = case ctrsCh of
    ListCtrChangeNil -> ctx
    ListCtrChangeCons ctrId ctrParamsCh ctrsCh' ->
        let ch = ctrParamsChangeToChange dataType tyVarIds ctrParamsCh in
        insert ctrId (VarTypeChange ch) ctx
    ListCtrChangePlus (Constructor _ (TermBind _ ctrId) ctrParams) ctrsCh' ->
        let ty = ctrParamsToType dataType tyVarIds ctrParams in
        insert ctrId (VarInsert ty) ctx
    ListCtrChangeMinus (Constructor _ (TermBind _ ctrId) ctrParams) ctrsCh' ->
        let ty = ctrParamsToType dataType tyVarIds ctrParams in
        insert ctrId (VarDelete ty) ctx

ctrParamsChangeToChange :: {-datatype-}TypeVarID -> {-datatype params-}List TypeVarID -> ListCtrParamChange -> PolyChange
ctrParamsChangeToChange dataType tyVarIds ctrParamsCh =
    let sub = genFreshener tyVarIds in -- TODO: figure out how to abstract this out and not have repetition with the other instance of these lines below
    let freshTyVarIds = map (\id -> lookup' id sub) tyVarIds in
    let ctrOutType = TNeu defaultTNeuMD (TypeVar dataType) (map (\x -> TypeArg defaultTypeArgMD (TNeu defaultTNeuMD (TypeVar x) Nil)) freshTyVarIds) in
    tyVarIdsWrapChange freshTyVarIds (ctrParamsChangeToChangeImpl ctrParamsCh sub (tyInject ctrOutType))

ctrParamsChangeToChangeImpl :: ListCtrParamChange -> {-freshen datatype parameters in each type-}TyVarSub -> Change -> Change
ctrParamsChangeToChangeImpl ctrParamsCh sub outCh = case ctrParamsCh of
    ListCtrParamChangeNil -> outCh
    ListCtrParamChangeCons ch ctrParamsCh' ->
        let tyVarSub = map (\x -> TNeu defaultTNeuMD (TypeVar x) Nil) sub in
        let ch' = applySubChange {subTypeVars: tyVarSub, subTHoles: empty} ch in
        CArrow ch' (ctrParamsChangeToChangeImpl ctrParamsCh' sub outCh)
    ListCtrParamChangePlus (CtrParam _ ty) ctrParamsCh' -> Plus (subType sub ty) (ctrParamsChangeToChangeImpl ctrParamsCh' sub outCh)
    ListCtrParamChangeMinus (CtrParam _ ty) ctrParamsCh' -> Minus (subType sub ty) (ctrParamsChangeToChangeImpl ctrParamsCh' sub outCh)

