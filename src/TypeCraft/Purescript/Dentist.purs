module TypeCraft.Purescript.Dentist where

import Prelude
import Data.Tuple.Nested (type (/\), (/\))
import Prim hiding (Type)
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Util (hole)
import Effect.Exception.Unsafe (unsafeThrow)
import Data.Map.Internal (empty, lookup, insert, union)
import TypeCraft.Purescript.TypeChangeAlgebra (alterCtxVarChange)
import TypeCraft.Purescript.TypeChangeAlgebra (alterCCtxVarChange)

{-
The middle path in a selection is composed of a subset of Teeth: those for which the top and bottom have the
same sort.
We have selections in:
Term, Type, List Constructor, List CtrParam, (List TypeArg???), List TypeBind

For each of these, we need to look at a selection and get the TypeChange and ContextChange associated with it.

*TooothChange inputs an UpTooth, so the context and type input starts from the bottom!
-}


termToothChange :: Type -> TypeContext -> TermContext -> Tooth -> Change /\ KindChangeCtx /\ ChangeCtx
termToothChange ty kctx ctx tooth =
    case ty /\ tooth of
        Arrow _ ty1 ty2 /\ App1 md {-Term-} t2 argTy outTy -> Minus ty1 (tyInject ty2) /\ kCtxInject kctx /\ ctxInject ctx
        ty /\ App2 md t1 {-Term-} argTy outTy -> Replace ty outTy /\ kCtxInject kctx /\ ctxInject ctx
        ty /\ Lambda3 md tBind@(TermBind _ x) argTy {-Term-} bodyTy -> Plus argTy (tyInject ty) /\ kCtxInject kctx /\ insert x (VarDelete (PType argTy)) (ctxInject ctx)
        ty /\ Let2 md tBind@(TermBind _ x) tyBinds {-Term-} defTy body bodyTy
            -> Replace defTy bodyTy /\ kCtxInject kctx /\ insert x (VarDelete (tyBindsWrapType tyBinds defTy)) (ctxInject ctx)
        ty /\ Let4 md tBind@(TermBind _ x) tyBinds def defTy {-Term-} bodyTy
            -> tyInject bodyTy /\ kCtxInject kctx /\ insert x (VarDelete (tyBindsWrapType tyBinds defTy)) (ctxInject ctx)
        ty /\ Buffer1 md {-Term-} defTy body bodyTy -> Replace defTy bodyTy /\ kCtxInject kctx /\ ctxInject ctx
        ty /\ Buffer3 md def defTy {-Term-} bodyTy -> tyInject bodyTy /\ kCtxInject kctx /\ ctxInject ctx
        ty /\ TypeBoundary1 md ch {-Term-} -> ch /\ kCtxInject kctx /\ ctxInject ctx
        ty /\ ContextBoundary1 md x vch {-Term-} -> tyInject ty /\ kCtxInject kctx /\ alterCCtxVarChange (ctxInject ctx) x vch
        ty /\ TLet4 md tyBind tyBinds def {-Term-} bodyTy -> hole
        ty /\ Data4 md tyBind tyBinds ctrs {-Term-} bodyTy -> hole
        _ -> unsafeThrow "Not a term-term tooth"

-- TODO: insetad of having ctxInject everywhere, maybe it should input a change ctx?