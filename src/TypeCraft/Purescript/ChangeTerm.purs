module TypeCraft.Purescript.ChangeTerm where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.TypeChangeAlgebra

import Data.List (List(..), (:), foldr, null)
import Data.Map.Internal (empty, lookup, insert)
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple (snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Freshen (freshenChange)
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Util (lookup')
import Debug (trace)
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Freshen
import TypeCraft.Purescript.Unification
import TypeCraft.Purescript.Kinds (bindsToKind)
import TypeCraft.Purescript.Util (delete')
import TypeCraft.Purescript.Alpha (applySubChange)


-- calls chTerm, but if it returns a non-id change, it wraps in a boundary
-- TODO: Im not sure how I should understand this. I think that this is used for places where we assume that the output change is id, but I'm not sure what the criteria for that is.
chTermBoundary :: KindChangeCtx -> ChangeCtx -> Change -> Term -> ChangeCtx /\ Term
chTermBoundary kctx ctx c t =
    let ctx' /\ c /\ t' = chTerm kctx ctx c t in
    if chIsId c
        then ctx' /\ t'
        else ctx' /\ TypeBoundary defaultTypeBoundaryMD (invert c) t'

-- ASSUMPTION: if you only propagate a ctx down, nothing should come back up!
chTermCtxOnly :: KindChangeCtx -> ChangeCtx -> Type -> Term -> Term
chTermCtxOnly kctx ctx ty t =
    let ctx' /\ c /\ t' = chTerm kctx ctx (tyInject ty) t in
    if not (ctxIsId ctx') then unsafeThrow ("Assumption violated! ctx' is: " <> show ctx') else
    if not (chIsId c) then unsafeThrow ("Assumption violated! c is: " <> show c) else
    t'

getRightCtxInj :: ChangeCtx -> ChangeCtx
getRightCtxInj ctx =
    let ctx1_ /\ ctx2 = getCtxEndpoints ctx in
    ctxInject ctx2

{-
chTerm inputs D1, C1, t1 and outputs D2, t2, and C2 such that
D1 o D2 |- t1 --[C1 o c2] --> t2
-}
chTerm :: KindChangeCtx -> ChangeCtx -> Change -> Term -> ChangeCtx /\ Change  /\ Term
chTerm kctx ctx c t =
    let ctx' /\ cRes /\ tRes = (
        case c /\ t of
            cin /\ (App md t1 t2 argTy outTy) ->
                let ctx' /\ c1 /\ t1' = chTerm kctx ctx (CArrow (tyInject argTy) cin) t1 in
                case c1 of
                (Minus _ c1') ->
                    let ctx'' /\ ct2 /\ t2' = chTerm kctx ctx' (tyInject argTy) t2 in
                    (composeCtxs ctx' ctx'') /\ c1' /\ Buffer defaultBufferMD t2 (snd (getEndpoints ct2)) t1' (snd (getEndpoints c1))
                (CArrow c1a c1b) ->
                    trace ("c1b is " <> show c1b) \_ ->
                    let ctx'' /\ c2 /\ t2' = chTerm kctx ctx' c1a t2 in
                    let t2'' = if chIsId c2
                        then t2'
                        else TypeBoundary defaultTypeBoundaryMD (invert c2) t2'
                    in (composeCtxs ctx' ctx'') /\ c1b /\ App md t1' t2'' (snd (getEndpoints c1a)) (snd (getEndpoints c1b))
                otherChange ->
                    let ctx'' /\ ct2 /\ t2' = chTerm kctx ctx' (tyInject argTy) t2 in
                    (composeCtxs ctx' ctx'') /\ tyInject (outTy)
                    /\ TypeBoundary defaultTypeBoundaryMD (Replace (snd (getEndpoints otherChange)) (snd (getEndpoints cin)))
                       (Buffer defaultBufferMD t2' (snd (getEndpoints ct2)) t1' (snd (getEndpoints otherChange)))
--                _ -> composeChange (Minus argTy (tyInject (snd (getEndpoints cin)))) c1 /\ -- is this right?
--                     Buffer defaultBufferMD t1' (snd (getEndpoints c1)) t1'
            cin /\ (Var md x tArgs) -> -- TODO: actually do var case for real
                -- try the polymorphism case
--                case getSubstitution cin (lookup x ctx)
                let xVarCh = lookup' x ctx in
                case xVarCh of
                    VarDelete _ -> getRightCtxInj ctx /\ tyInject (snd (getEndpoints cin)) /\ Hole defaultHoleMD -- later use context boundary
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
                        if not (chIsId cin) then
                              if null tArgs then
                                  insert x (VarTypeChange (PChange cin)) ctx /\ tyInject (snd (getEndpoints cin)) /\ Var md x tArgs else
                                  getRightCtxInj ctx /\ tyInject (snd (getEndpoints cin)) /\ Hole defaultHoleMD else
                        let ch /\ tyArgs' = chTypeArgs2 kctx tArgs pch in
                        getRightCtxInj ctx /\ ch /\ Var md x tyArgs'
            (CArrow c1 c2) /\ (Lambda md tBind@(TermBind _ x) ty t bodyTy) ->
                if not (ty == fst (getEndpoints c1)) then unsafeThrow "shouldn't happen 1" else
                if not (bodyTy == fst (getEndpoints c2)) then unsafeThrow "shouldn't happen 2" else
                let ctx' /\ c2' /\ t' = chTerm kctx (insert x (VarTypeChange (PChange c1)) ctx) c2 t in
                let ctx'' = delete' x ctx' in
                let xCh = lookup' x ctx' in
                case xCh of
                    VarTypeChange (PChange ch) ->
                        let fullCh = composeChange c1 ch in
                        ctx'' /\ (CArrow ch c2') /\ Lambda md tBind (snd (getEndpoints fullCh)) t' (snd (getEndpoints c2))
                    _ -> unsafeThrow "shouldn't happen chTerm 1"
            (Minus ty1 c) /\ (Lambda md tBind@(TermBind _ x) ty2 t bodyTy) ->
                if not (ty1 == ty2) then unsafeThrow "shouldn't happen 3" else
                if not (bodyTy == fst (getEndpoints c)) then unsafeThrow "shouldn't happen 4" else
                let ctx' /\ c2' /\ t' = chTerm kctx (insert x (VarDelete (PType ty2)) ctx) c t in
                let ctx'' = delete' x ctx' in
                ctx'' /\ c2' /\ t'
            (Minus ty c) /\ t ->
                let ctx' /\ c' /\ t' = chTerm kctx ctx c t in
                ctx' /\ (CArrow (tyInject ty) c') /\ App defaultAppMD t' (Hole defaultHoleMD) ty (snd (getEndpoints c))
            (Plus ty c) /\ t ->
                let tBind@(TermBind _ x) = (freshTermBind Nothing) in
                let ctx' = insert x (VarInsert (PType ty)) ctx in
                let ctx' /\ c' /\ t' = chTerm kctx ctx' c t in
                ctx' /\ (CArrow (tyInject ty) c') /\ Lambda defaultLambdaMD tBind ty t' (snd (getEndpoints c'))
            c /\ Let md tBind@(TermBind _ x) binds t1 ty t2 tyBody ->
                -- TODO: need to include the binds into the kctx for some things I think?
                if not (fst (getEndpoints c) == tyBody) then unsafeThrow "shouldn't happen 5" else
                let ctx' = addLetToCCtx ctx tBind binds ty in
                let kctx' = addLetToKCCtx kctx binds in
                let ctx'' /\ c2 /\ t2' = chTerm kctx' ctx' c t2 in
                let t1'= chTermCtxOnly kctx' (composeCtxs ctx' ctx'') ty t1 in
                let ctx''' = delete' x ctx'' in
                -- TODO: apply change to x to the let itself!
                ctx''' /\ c2 /\ Let md tBind binds t1' ty t2' (snd (getEndpoints c2))
            c /\ Buffer md t1 ty1 t2 bodyTy ->
                let ctx' /\ c1 /\ t1' = chTerm kctx ctx (tyInject ty1) t1 in
                let ctx'' /\ c2 /\ t2' = chTerm kctx ctx' c t2 in
                ctx'' /\ c2 /\ Buffer md t1' (snd (getEndpoints c1)) t2' (snd (getEndpoints c2))
            c /\ TLet md x params ty t bodyType ->
                if not (fst (getEndpoints c) == bodyType) then unsafeThrow "shouldn't happen 6" else
                let ty' /\ tyChange = chType kctx ty in
--                let c' /\ t' = chTerm (ctxKindCons kctx x (TVarTypeChange tyChange)) ctx c t in
                let typeAliasChange = hole' "chTerm" in
                let ctx' /\ c' /\ t' = chTerm (ctxKindCons kctx x (TVarKindChange (kindInject (tyBindsWrapKind params Type)) (Just typeAliasChange))) ctx c t in
                ctx' /\ c' /\ TLet md x params ty' t' (snd (getEndpoints c')) -- TODO: what if c references x? Then it is out of scope above.
            c /\ Hole md -> getRightCtxInj ctx /\ (tyInject (snd (getEndpoints c))) /\ Hole md
            c /\ Data md tyBind tyBinds ctrs body bodyTy ->
                let ctrsCh /\ ctrs' = chCtrList kctx ctrs in
                let kctx' /\ ctx' = addDataToCtx (kctx /\ ctx) tyBind tyBinds ctrsCh in
                let ctx'' /\ c' /\ body' = chTerm kctx' ctx' c body in
                ctx'' /\ c' /\ Data md tyBind tyBinds ctrs' body' (snd (getEndpoints c'))
            c /\ TypeBoundary md ch body ->
                let ch' = composeChange ch c in
                let tyChInside = tyInject (fst (getEndpoints ch)) in
                let ctx' /\ chBackUp /\ body' = chTerm kctx ctx tyChInside body in
                ctx' /\ tyChInside /\ TypeBoundary md (composeChange (invert chBackUp) ch') body'
            c /\ ContextBoundary md x vCh body ->
                case lookup x kctx of
                    Just xChInCtx -> hole' "chTerm"
                    Nothing -> hole' "chTerm"
            cin /\ t -> hole' "chTerm" -- tyInject (snd (getEndpoints cin)) /\ TypeBoundary defaultTypeBoundaryMD cin t
        )
    in
        let ch' /\ t' = doInsertArgs cRes tRes in
        ctx' /\ ch' /\ t'
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
    let ch' = applySubChange { subTypeVars : (insert x ty empty) , subTHoles : empty} ch in
    ch' /\ tyArg : tyArgsOut
chTypeArgs2 kctx tyArgs (PPlus x pc) =
    let ch /\ tyArgsOut = chTypeArgs2 kctx tyArgs pc in
    ch /\ (TypeArg defaultTypeArgMD (freshTHole unit)) : tyArgsOut
chTypeArgs2 kctx (tyArg : tyArgs) (PMinus x pc) =
    let ch /\ tyArgsOut = chTypeArgs2 kctx tyArgs pc in
    ch /\ tyArgs
chTypeArgs2 _ _ _ = unsafeThrow "invalid input to chTypeArgs2, or I forgot a case"

-- could avoid returning Type (because you can get it from the change with getEndpoints), if I put metadata into Change
chType :: KindChangeCtx -> Type -> Type /\ Change
chType kctx (Arrow md t1 t2) =
    let t1' /\ c1 = chType kctx t1 in
    let t2' /\ c2 = chType kctx t2 in
    Arrow md t1' t2' /\ CArrow c1 c2
chType kctx (THole md x) = THole md x /\ CHole x
chType kctx startType@(TNeu md tv args) =
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
            Just (TVarDelete kind maybeValue) ->
                let x = freshTypeHoleID unit in
                let newType = THole defaultHoleMD x in
                newType /\ Replace startType newType
            Just (TVarInsert kind maybeValue) -> unsafeThrow "I don't think this should happen but I'm not 100% sure"
        --    (Just (TVarTypeChange _)) -> unsafeThrow "I need to figure out what is the deal with TVarTypeChange!!!"
        CtxBoundaryTypeVar k mtv name x -> -- because this represents an Insert boundary, x can't be in kctx. Therefore, we output the identity
            hole' "chType" -- We still need to change the args though.


chTypeArgs :: KindChangeCtx -> KindChange -> List TypeArg -> List TypeArg /\ List ChangeParam
chTypeArgs kctx KCType Nil = Nil /\ Nil
chTypeArgs kctx (KPlus kc) params =
    let tparams /\ cparams = chTypeArgs kctx kc params in
    let x = freshTypeHoleID unit in
    let newType = THole defaultHoleMD x in
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
chTypeBindList (tyBind : tyBinds) = ListTypeBindChangePlus tyBind (chTypeBindList tyBinds)

chTypeParamList :: KindChangeCtx -> List TypeArg -> List Change /\ List TypeArg
chTypeParamList = hole' "chTypeParamList"

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