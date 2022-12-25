module TypeCraft.Purescript.ChangeTerm where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))

import TypeCraft.Purescript.Grammar
import Data.Map.Internal (empty, lookup)
import Data.Maybe (Maybe(..))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Freshen (freshenChange)
import TypeCraft.Purescript.Substitution (Sub, combineSub, subChange, subChangeCtx, unify)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints, composeChange)
import Data.Tuple (snd)
import TypeCraft.Purescript.MD
import Data.List (List(..), (:))
import TypeCraft.Purescript.ChangeType (chType)
import TypeCraft.Purescript.TypeChangeAlgebra (isIdentity, invert)
import Data.Tuple (fst)
import TypeCraft.Purescript.TypeChangeAlgebra (getSubstitution)
import TypeCraft.Purescript.ChangeType (chTypeArgs)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)

-- calls chTerm, but if it returns a non-id change, it wraps in a boundary
chTermBoundary :: KindChangeCtx -> ChangeCtx -> Change -> Term -> Term
chTermBoundary kctx ctx c t =
    let c /\ t' = chTerm kctx ctx c t in
    if isIdentity c
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
                    let t2'' = if isIdentity c2
                        then t2'
                        else TypeBoundary defaultTypeBoundaryMD (invert c2) t2'
                    in c1b /\ App md t1' t2'' (snd (getEndpoints c1a)) (snd (getEndpoints c1b))
                otherChange -> tyInject (outTy)
                    /\ TypeBoundary defaultTypeBoundaryMD (Replace (Arrow defaultArrowMD argTy outTy) (snd (getEndpoints otherChange)))
                       (Buffer defaultBufferMD t2 argTy t1' (snd (getEndpoints otherChange)))
--                _ -> composeChange (Minus argTy (tyInject (snd (getEndpoints cin)))) c1 /\ -- is this right?
--                     Buffer defaultBufferMD t1' (snd (getEndpoints c1)) t1'
            cin /\ (Var md x params) ->
                -- try the polymorphism case
--                case getSubstitution cin (lookup x ctx)
                let xVarCh = ctxLookup x ctx in
                case xVarCh of
                    VarDelete -> tyInject (snd (getEndpoints cin)) /\ Hole defaultHoleMD -- later use context boundary
                    VarTypeChange xChange ->
                        let tryPolymorhpismCase =
                                do _ <- (if isIdentity xChange then Just xChange else Nothing) -- (for now at least), polymorphism thing only works if variable type is unchanged in context
                                   let ty = (snd (getEndpoints xChange))
                                   sub <- getSubstitution cin ty
                                   let c' = composeChange (invert c) (subChange sub (tyInject ty))
                                   pure $ c' /\ (Var md x (unsafeThrow "need to deal with params!"))
                        in case tryPolymorhpismCase  of
                           Just res -> res
                           Nothing -> xChange /\ Var md x (unsafeThrow "need to deal with params!") -- if the polymorhpism case didn't apply, simply return the change and leave the variable as is
            (CArrow c1 c2) /\ (Lambda md x ty t bodyTy) ->
                if not (ty == fst (getEndpoints c1)) then unsafeThrow "shouldn't happen" else
                if not (bodyTy == fst (getEndpoints c2)) then unsafeThrow "shouldn't happen" else
                let c2' /\ t' = chTerm kctx (ctxLambdaCons ctx x (VarTypeChange c1)) c2 t in
                (CArrow (tyInject (snd (getEndpoints c1))) c2') /\ Lambda md x (snd (getEndpoints c1)) t' (snd (getEndpoints c2))
            (Minus ty1 c) /\ (Lambda md x ty2 t bodyTy) ->
                if not (ty1 == ty2) then unsafeThrow "shouldn't happen" else
                if not (bodyTy == fst (getEndpoints c)) then unsafeThrow "shouldn't happen" else
                let c2' /\ t' = chTerm kctx (ctxLambdaCons ctx x VarDelete) c t in
                (Minus ty1 c2') /\ t'
            (Plus ty c) /\ t ->
                c /\ App defaultAppMD t (Hole defaultHoleMD) ty (snd (getEndpoints c))
            c /\ Let md x binds t1 ty t2 tybody ->
                -- TODO: need to include the binds into the kctx for some things I think?
                if not (fst (getEndpoints c) == ty) then unsafeThrow "shouldn't happen" else
                let c1 /\ t1' = chTerm kctx (ctxLetCons ctx x (VarTypeChange (tyInject ty))) (tyInject ty) t1 in
                let c2 /\ t2' = chTerm kctx (ctxLetCons ctx x (VarTypeChange (tyInject ty))) c t2 in
                let t1'' = if isIdentity c1 then t1' else TypeBoundary defaultTypeBoundaryMD c1 t1' in
                c2 /\ Let md x binds t1'' ty t2' (snd (getEndpoints c2))
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

--chTerm :: KindChangeCtx -> ChangeCtx -> Change -> Term -> Change  /\ Term

-- The output Change is the change to the constructor itself
chCtrList :: KindChangeCtx -> List Constructor ->  List (List ChangeParam) /\ List Constructor
chCtrList = hole

-- The output Change is the change to the constructor itself
chCtr :: KindChangeCtx -> Constructor -> (List Change) /\ Constructor
chCtr = hole

chParam :: KindChangeCtx -> CtrParam -> Change /\ CtrParam
chParam kctx (CtrParam md t) =
    let t' /\ c = chType kctx t in c /\ CtrParam md t'

chParamList :: KindChangeCtx -> List CtrParam -> (List Change) /\ List CtrParam
chParamList _ Nil = Nil /\ Nil
chParamList kctx (param : params) =
    let ch /\ param' = chParam kctx param in
    let chs /\ params' = chParamList kctx params in
    (ch : chs) /\ param' : params'

chTypeParamList :: KindChangeCtx -> List TypeArg -> List Change /\ List TypeArg
chTypeParamList = hole