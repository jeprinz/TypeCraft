module TypeCraft.Purescript.ChangePath where

import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested (type (/\), (/\))
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.ChangeTerm
import Effect.Exception.Unsafe (unsafeThrow)
import Data.Tuple (fst)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints)
import Data.Tuple (snd)
import Data.List (List(..), (:))
import Data.Map.Internal (empty, lookup, insert, delete)
import TypeCraft.Purescript.TypeChangeAlgebra
import TypeCraft.Purescript.MD

-- For now, I won't do anything with upwards ChangeCtx. But I can implement that in the future.

chTermPath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
chTermPath kctx ctx (CArrow c1 c2) (App1 md {-here-} t argTy outTy : up) =
    if not (argTy == fst (getEndpoints c1) && outTy == fst (getEndpoints c1)) then unsafeThrow "shouldn't happen" else
    let t' = chTermBoundary kctx ctx c1 t in
    let up' = chTermPath kctx ctx c2 up in
    App1 md t' (snd (getEndpoints c1)) (snd (getEndpoints c2)) : up'
-- TODO: App2 case, other App1 cases with other TypeChanges
chTermPath kctx ctx c  (Let2 md x tbinds {-Term = here-} ty body tybody : up) =
    hole
chTermPath kctx ctx c (Let4 md tBind@(TermBind _ x) tbinds def ty {-body = here-} tybody : up) =
    if not (fst (getEndpoints c) == tybody) then unsafeThrow "shouldn't happen" else
    let ctx' = delete x ctx in
    let def' = chTermBoundary kctx ctx (tyInject ty) def in
    let up' = chTermPath kctx ctx' c up in
    Let4 md tBind tbinds def' ty (snd (getEndpoints c)) : up'
chTermPath kctx ctx c (Data4 md x tbinds ctrs {-body = here-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    -- TODO: update ctrs using kctx and chCtrList
    let up' = chTermPath kctx ctx c up in
    Data4 md x tbinds ctrs (snd (getEndpoints c)) : up'
--Data4 TermPath GADTMD TypeBind (List TypeBind) (List Constructor) {-Term-}
--App2 TermPath AppMD Term {-Term-} Type
--Lambda2 TermPath LambdaMD TermBind Type {-Term-}
--Buffer1 TermPath BufferMD {-Term-} Type Term | Buffer3 TermPath BufferMD Term Type {-Term-}
--TypeBoundary1 TermPath TypeBoundaryMD Change {-Term-}
--ContextBoundary1 TermPath ContextBoundaryMD Change {-Term-}
--TLet3 TermPath TLetMD TypeBind Type Kind {-Term-}
chTermPath _ _ _ _ = unsafeThrow "finish implementing all cases"

chTypePath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
chTypePath kctx ctx ch (Let3 md tBind@(TermBind _ x) tyBinds def {-Type-} body bodyTy : termPath) =
    let ctx' = insert x (VarTypeChange (tyBindsWrapChange tyBinds ch)) ctx in
    let c1 /\ def' = chTerm kctx ctx' ch def in
    let c2 /\ body' = chTerm kctx ctx' (tyInject bodyTy) body in
    let def'' = if chIsId c1 then def' else TypeBoundary defaultTypeBoundaryMD c1 def' in
    let termPath' = chTermPath kctx ctx c2 termPath in
    Let3 md tBind tyBinds def'' body' (snd (getEndpoints c2)) : termPath'
chTypePath _ _ _ _ = hole

-- these are the cases:
--      lambda2 :: TermPathRecValue -> LambdaMD -> TermBindRecValue -> TermRecValue -> Type -> a
--      , let3 :: TermPathRecValue -> LetMD -> TermBindRecValue -> ListTypeBindRecValue -> TermRecValue -> TermRecValue -> Type -> a
--      , buffer2 :: TermPathRecValue -> BufferMD -> TermRecValue -> TermRecValue -> Type -> a
--      , tLet3 :: TermPathRecValue -> TLetMD -> TypeBindRecValue -> ListTypeBindRecValue -> TermRecValue -> Type -> a
--      , ctrParam1 :: CtrParamPathRecValue -> CtrParamMD -> a
--      , typeArg1 :: TypeArgPathRecValue -> TypeArgMD -> a
--      , arrow1 :: TypePathRecValue -> ArrowMD -> TypeRecValue -> a
--      , arrow2 :: TypePathRecValue -> ArrowMD -> TypeRecValue -> a
