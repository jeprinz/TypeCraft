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

-- For now, I won't do anything with upwards ChangeCtx. But I can implement that in the future.

chPath :: KindChangeCtx -> ChangeCtx -> Change -> TermPath -> TermPath
chPath kctx ctx (CArrow c1 c2) (App1 up md {-here-} t argTy outTy) =
    if not (argTy == fst (getEndpoints c1) && outTy == fst (getEndpoints c1)) then unsafeThrow "shouldn't happen" else
    let t' = chTermBoundary kctx ctx c1 t in
    let up' = chPath kctx ctx c2 up in
    App1 up' md t' (snd (getEndpoints c1)) (snd (getEndpoints c2))
-- TODO: App2 case, other App1 cases
chPath kctx ctx c  (Let1 up md x tbinds {-Term = here-} ty body tybody) =
    hole
chPath kctx ctx c (Let3 up md x tbinds def ty {-body = here-} tybody) =
    if not (fst (getEndpoints c) == tybody) then unsafeThrow "shouldn't happen" else
    let def' = chTermBoundary kctx (ctxLetCons ctx x (VarTypeChange (tyInject ty))) (tyInject ty) def in
    let up' = chPath kctx ctx c up in
    Let3 up' md x tbinds def' ty (snd (getEndpoints c))
chPath kctx ctx c (Data3 up md x tbinds ctrs {-body = here-} bodyTy) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    -- TODO: update ctrs using kctx and chCtrList
    let up' = chPath kctx ctx c up in
    Data3 up' md x tbinds ctrs (snd (getEndpoints c))
--Data3 TermPath GADTMD TypeBind (List TypeBind) (List Constructor) {-Term-}
--App2 TermPath AppMD Term {-Term-} Type
--Lambda2 TermPath LambdaMD TermBind Type {-Term-}
--Buffer1 TermPath BufferMD {-Term-} Type Term | Buffer3 TermPath BufferMD Term Type {-Term-}
--TypeBoundary1 TermPath TypeBoundaryMD Change {-Term-}
--ContextBoundary1 TermPath ContextBoundaryMD Change {-Term-}
--TLet3 TermPath TLetMD TypeBind Type Kind {-Term-}

chPath _ _ _ _ = unsafeThrow "finish implementing all cases"
