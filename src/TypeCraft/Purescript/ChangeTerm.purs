module TypeCraft.Purescript.ChangeTerm where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (empty, lookup, insert)
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Freshen (freshenChange)
--import TypeCraft.Purescript.Substitution (Sub, combineSub, subChange, subChangeCtx, unify)
import Data.Tuple (snd)
import TypeCraft.Purescript.MD
import Data.List (List(..), (:))
import TypeCraft.Purescript.TypeChangeAlgebra
import Data.Tuple (fst)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Util (lookup')

-- calls chTerm, but if it returns a non-id change, it wraps in a boundary
chTermBoundary :: KindChangeCtx -> ChangeCtx -> Change -> Term -> Term
chTermBoundary kctx ctx c t =
    let c /\ t' = chTerm kctx ctx c t in
    if chIsId c
        then t'
        else TypeBoundary defaultTypeBoundaryMD (invert c) t'

{-
chTerm inputs D, C1, t1 and outputs t2 and C2 such that
D |- t1 --[C1 o c2] --> t2
-}
chTerm :: KindChangeCtx -> ChangeCtx -> Change -> Term -> Change  /\ Term
chTerm kctx ctx c t =
    let cRes /\ tRes = (
        case c /\ t of
            cin /\ (App md t1 t2 argTy outTy) ->
                let c1 /\ t1' = chTerm kctx ctx (CArrow (tyInject argTy) cin) t1 in
                case c1 of
                (Minus _ c1') -> c1' /\ Buffer defaultBufferMD t2 argTy t1' (snd (getEndpoints c1))
                (CArrow c1a c1b) ->
                    let c2 /\ t2' = chTerm kctx ctx c1a t2 in
                    let t2'' = if chIsId c2
                        then t2'
                        else TypeBoundary defaultTypeBoundaryMD (invert c2) t2'
                    in c1b /\ App md t1' t2'' (snd (getEndpoints c1a)) (snd (getEndpoints c1b))
                otherChange -> tyInject (outTy)
                    /\ TypeBoundary defaultTypeBoundaryMD (Replace (Arrow defaultArrowMD argTy outTy) (snd (getEndpoints otherChange)))
                       (Buffer defaultBufferMD t2 argTy t1' (snd (getEndpoints otherChange)))
--                _ -> composeChange (Minus argTy (tyInject (snd (getEndpoints cin)))) c1 /\ -- is this right?
--                     Buffer defaultBufferMD t1' (snd (getEndpoints c1)) t1'
            cin /\ (Var md x params) -> -- TODO: actually do var case for real
                -- try the polymorphism case
--                case getSubstitution cin (lookup x ctx)
                let xVarCh = lookup' x ctx in
                case xVarCh of
                    VarDelete -> tyInject (snd (getEndpoints cin)) /\ Hole defaultHoleMD -- later use context boundary
--                    VarTypeChange xChange ->
--                        let tryPolymorhpismCase =
----                                do _ <- (if pChIsId xChange then Just xChange else Nothing) -- (for now at least), polymorphism thing only works if variable type is unchanged in context
----                                   let ty = (snd (getEndpoints xChange))
----                                   sub <- getSubstitution cin ty
----                                   let c' = composeChange (invert c) (subChange sub (tyInject ty))
----                                   pure $ c' /\ (Var md x (unsafeThrow "need to deal with params!"))
--                                Nothing
--                        in case tryPolymorhpismCase  of
--                           Just res -> res
--                           Nothing -> hole -- xChange /\ Var md x (unsafeThrow "need to deal with params!") -- if the polymorhpism case didn't apply, simply return the change and leave the variable as is
                    VarTypeChange (PChange cVar) ->
                        if not (chIsId cin) then tyInject (snd (getEndpoints cin)) /\ Hole defaultHoleMD
                        else cVar /\ Var md x params
                    VarTypeChange _ -> unsafeThrow "not implemented yet"
            (CArrow c1 c2) /\ (Lambda md tBind@(TermBind _ x) ty t bodyTy) ->
                if not (ty == fst (getEndpoints c1)) then unsafeThrow "shouldn't happen" else
                if not (bodyTy == fst (getEndpoints c2)) then unsafeThrow "shouldn't happen" else
                let c2' /\ t' = chTerm kctx (insert x (VarTypeChange (PChange c1)) ctx) c2 t in
                (CArrow (tyInject (snd (getEndpoints c1))) c2') /\ Lambda md tBind (snd (getEndpoints c1)) t' (snd (getEndpoints c2))
            (Minus ty1 c) /\ (Lambda md tBind@(TermBind _ x) ty2 t bodyTy) ->
                if not (ty1 == ty2) then unsafeThrow "shouldn't happen" else
                if not (bodyTy == fst (getEndpoints c)) then unsafeThrow "shouldn't happen" else
                let c2' /\ t' = chTerm kctx (insert x VarDelete ctx) c t in
                (Minus ty1 c2') /\ t'
            (Plus ty c) /\ t ->
                c /\ App defaultAppMD t (Hole defaultHoleMD) ty (snd (getEndpoints c))
            c /\ Let md tBind@(TermBind _ x) binds t1 ty t2 tybody ->
                -- TODO: need to include the binds into the kctx for some things I think?
                if not (fst (getEndpoints c) == ty) then unsafeThrow "shouldn't happen" else
                let ctx' = addLetToCCtx ctx tBind binds ty in
                let c1 /\ t1'= chTerm kctx ctx' (tyInject ty) t1 in
                let c2 /\ t2' = chTerm kctx ctx' c t2 in
                let t1'' = if chIsId c1 then t1' else TypeBoundary defaultTypeBoundaryMD c1 t1' in
                c2 /\ Let md tBind binds t1'' ty t2' (snd (getEndpoints c2))
            c /\ Buffer md t1 ty1 t2 bodyTy ->
                let c1 /\ t1' = chTerm kctx ctx (tyInject ty1) t1 in
                let c2 /\ t2' = chTerm kctx ctx c t2 in
                c2 /\ Buffer md t1' (snd (getEndpoints c1)) t2' (snd (getEndpoints c2))
            c /\ TLet md x params ty t bodyType ->
                if not (fst (getEndpoints c) == bodyType) then unsafeThrow "shouldn't happen" else
                let ty' /\ tyChange = chType kctx ty in
                let c' /\ t' = chTerm (ctxKindCons kctx x (TVarTypeChange tyChange)) ctx c t in
                c' /\ TLet md x params ty' t' (snd (getEndpoints c')) -- TODO: what if c references x? Then it is out of scope above.
            cin /\ t -> tyInject (snd (getEndpoints cin)) /\ TypeBoundary defaultTypeBoundaryMD cin t
        )
    in
        doInsertArgs cRes tRes
{-
Inputs (implicit D) C1 t, and outputs t2 and C2 such that
D |- t1 ---[C1 o (C2 ^-1)]---> t2
-}
doInsertArgs :: Change -> Term -> Change /\ Term
doInsertArgs (Plus ty c) t = doInsertArgs c (App defaultAppMD t (Hole defaultHoleMD) ty (snd (getEndpoints c)))
doInsertArgs c t = c /\ t

-- could avoid returning Type (because you can get it from the change with getEndpoints), if I put metadata into Change
chType :: KindChangeCtx -> Type -> Type /\ Change
chType kctx (Arrow md t1 t2) =
    let t1' /\ c1 = chType kctx t1 in
    let t2' /\ c2 = chType kctx t2 in
    Arrow md t1' t2' /\ CArrow c1 c2
chType kctx (THole md x) = THole md x /\ CHole x
chType kctx startType@(TNeu md x args) =
    case lookup x kctx of
    Nothing -> unsafeThrow "shouldn't get here! all variables should be bound in the context!"
    Just (TVarKindChange kindChange) ->
        let args' /\ cargs = chTypeArgs kctx kindChange args in
        TNeu md x args' /\ CNeu x cargs
    Just TVarDelete ->
        let x = freshTypeHoleID unit in
        let newType = THole defaultHoleMD x in
        newType /\ Replace startType newType
    (Just (TVarTypeChange _)) -> unsafeThrow "I need to figure out what is the deal with TVarTypeChange!!!"


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

--chTerm :: KindChangeCtx -> ChangeCtx -> Change -> Term -> Change  /\ Term

-- The output Change is the change to the constructor itself
chCtrList :: KindChangeCtx -> List Constructor ->  List (List ChangeParam) /\ List Constructor
chCtrList = hole

-- The output Change is the change to the constructor itself
chCtr :: KindChangeCtx -> Constructor -> (List Change) /\ Constructor
chCtr = hole

chCtrParam :: KindChangeCtx -> CtrParam -> Change /\ CtrParam
chCtrParam kctx (CtrParam md t) =
    let t' /\ c = chType kctx t in c /\ CtrParam md t'

chParamList :: KindChangeCtx -> List CtrParam -> (List Change) /\ List CtrParam
chParamList _ Nil = Nil /\ Nil
chParamList kctx (param : params) =
    let ch /\ param' = chCtrParam kctx param in
    let chs /\ params' = chParamList kctx params in
    (ch : chs) /\ param' : params'

chTypeParamList :: KindChangeCtx -> List TypeArg -> List Change /\ List TypeArg
chTypeParamList = hole

---- inputs PolyChange by which var type changed, outputs new args and TypeChange by which the whole neutral form changes
chTypeArgsNeu :: PolyChange -> List TypeArg -> Change /\ List TypeArg
chTypeArgsNeu (PChange ch) Nil = ch /\ Nil
chTypeArgsNeu (CForall x ch) (arg : args) = hole
chTypeArgsNeu (PMinus x ch) (arg : args) = hole
chTypeArgsNeu (PPlus x ch) args = hole
chTypeArgsNeu _ _ = unsafeThrow "shouldn't happen"
-- TODO: there is something nontrivial to think about here. It should track a context so it knows which arguments got deleted etc.
-- also if a type argument gets affected by the KindChangeCtx, then that needs to be reflected as well...