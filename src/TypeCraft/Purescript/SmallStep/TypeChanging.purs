module TypeCraft.Purescript.SmallStep.TypeChanging where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.SmallStep.UTerm
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.TypeChangeAlgebra
import TypeCraft.Purescript.Context
import Data.Tuple.Nested
import Data.List (List(..), (:))
--import Data.List as List
import TypeCraft.Purescript.Util
import TypeCraft.Purescript.Context
import Data.Tuple (fst, snd)
import Effect.Exception.Unsafe (unsafeThrow)

{-
QUESTIONS:
How can this deal with typechange bouncing back up for dealing with polymorhpism?
Or even more simply, how can it deal with adding an argument to a variable? A typechange has to be propagated up from the variable.
Answer: downChange needs to also return a typechange going up!
-}

downChange :: Label -> CAllContext -> Change -> Label /\ Change /\Array (Change /\ CAllContext)
downChange (LApp md {-Term-} {-Term-} argTy outTy) ctxs ch = hole' "downChange"
downChange (LLambda md tBind ty1 {-Term-} ty2) ctxs ch = hole' "downChange"
downChange (LVar md x tyArgs) ctxs ch = hole' "downChange"
downChange (LLet md tBind tyBinds {-Term-} defTy {-Term-} bodyTy) (kctx /\ ctx) ch =
    let ctx' = addLetToCCtx ctx tBind tyBinds defTy in
    let kctx' = addLetToKCCtx kctx tyBinds in
    LLet md tBind tyBinds {--} defTy {--} (snd (getEndpoints ch))
    /\ (tyInject bodyTy)
    /\ [((tyInject defTy) /\ (kctx' /\ ctx')) , (ch /\ (kctx' /\ ctx'))]
downChange (LData md tyBind tyBinds ctrs {-Term-} bodyTy) ctxs ch = hole' "downChange"
downChange (LTLet md tyBind tyBinds def {-Term-} bodyTy) ctxs ch = hole' "downChange"
downChange (LTypeBoundary md ch1 {-Term-}) ctxs ch = hole' "downChange"
downChange (LContextBoundary md x vc {-Term-}) ctxs ch = hole' "downChange"
downChange (LHole md {-NEEDS WEAKENINGS! (A set of variables by which the context was weakened)-}) ctxs ch = hole' "downChange"
downChange (LBuffer md {-Term-} bufTy {-Term-} bodyTy) ctxs ch = hole' "downChange"

upChange :: Label -> Int -> CAllContext -> Change -> Label /\ Array (Change /\ CAllContext) /\ Array (Change /\ CAllContext)
upChange (LApp md {-Term-} {-Term-} argTy outTy) 0 ctxs ch = hole' "upChange"
upChange (LApp md {-Term-} {-Term-} argTy outTy) 1 ctxs ch = hole' "upChange"
upChange (LLambda md tBind ty1 {-Term-} ty2) 0 ctxs ch = hole' "upChange"
upChange (LLet md tBind tyBinds {-Term-} defTy {-Term-} bodyTy) 0 (kctx /\ ctx) ch = hole' "upChange"
upChange (LLet md tBind tyBinds {-Term-} defTy {-Term-} bodyTy) 1 (kctx /\ ctx) ch = hole' "upChange"
upChange (LData md tyBind tyBinds ctrs {-Term-} bodyTy) 0 ctxs ch = hole' "upChange"
upChange (LTLet md tyBind tyBinds def {-Term-} bodyTy) 0 ctxs ch = hole' "upChange"
upChange (LTypeBoundary md ch1 {-Term-}) 0 ctxs ch = hole' "upChange"
upChange (LContextBoundary md x vc {-Term-}) 0 ctxs ch = hole' "upChange"
upChange (LBuffer md {-Term-} bufTy {-Term-} bodyTy) 0 ctxs ch = hole' "upChange"
upChange (LBuffer md {-Term-} bufTy {-Term-} bodyTy) 1 ctxs ch = hole' "upChange"
upChange label child _ _ = unsafeThrow ("invalid input to upChange: got label " <> show label <> " child number " <> show child)
