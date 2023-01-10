module TypeCraft.Purescript.ChangePath where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.ChangeTerm
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.TypeChangeAlgebra

import Data.List (List(..), (:))
import Data.Map.Internal (empty, lookup, insert, delete)
import Data.Tuple (fst)
import Data.Tuple (snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints)
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Util (hole)

-- For now, I won't do anything with upwards ChangeCtx. But I can implement that in the future.

{-
TODO: seemingly, chTermPath should never recieve an input change of the form (Plus ...)
Dually, chTerm should never output an input change of the form (Plus ...)
....
-}

chTermPath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
chTermPath kctx ctx (CArrow c1 c2) (App1 md {-here-} t argTy outTy : up) =
    if not (argTy == fst (getEndpoints c1) && outTy == fst (getEndpoints c2)) then unsafeThrow "shouldn't happen" else
    let t' = chTermBoundary kctx ctx c1 t in
    let up' = chTermPath kctx ctx c2 up in
    App1 md t' (snd (getEndpoints c1)) (snd (getEndpoints c2)) : up'
chTermPath kctx ctx (Minus t1 (Plus t2 c)) (App1 md1 {-here-} arg1 argTy1 outTy1 -- Swap case!
        : App1 md2 {-Term-} arg2 argTy2 outTy2 : up)
        | t1 == t2 =
    if not (outTy1 == Arrow defaultArrowMD argTy2 outTy2) then unsafeThrow "shouldn't happen" else
    let up' = chTermPath kctx ctx c up in
    App1 md1 {-Term-} arg2 argTy2 (Arrow defaultArrowMD argTy2 (Arrow defaultArrowMD argTy1 outTy2)) : App1 md2 {-Term-} arg2 argTy2 outTy2 : up'
chTermPath kctx ctx (Minus t c) (App1 md {-here-} arg argTy outTy : up) =
    if not (t == argTy && fst (getEndpoints c) == outTy) then unsafeThrow "shouldn't happen" else
    let up' = chTermPath kctx ctx c up in
    Buffer3 defaultBufferMD arg argTy {-Term-} outTy : up'
-- TODO: App2 case, other App1 cases with other TypeChanges
--    App2 AppMD Term {-Term-} Type Type -- TODO: this case goes along with the polymorphism change stuff
chTermPath kctx ctx c  (Let3 md x tbinds {-Term = here-} ty body tybody : up) =
    hole' "chTermPath"
chTermPath kctx ctx c (Let5 md tBind@(TermBind _ x) tbinds def ty {-body = here-} tybody : up) =
    if not (fst (getEndpoints c) == tybody) then unsafeThrow "shouldn't happen" else
    let ctx' = delete x ctx in
    let def' = chTermBoundary kctx ctx (tyInject ty) def in -- TODO: why would the def of the let ever change anyway?
    let up' = chTermPath kctx ctx' c up in
    Let5 md tBind tbinds def' ty (snd (getEndpoints c)) : up'
chTermPath kctx ctx c (Data4 md x tbinds ctrs {-body = here-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    -- TODO: update ctrs using kctx and chCtrList
    let up' = chTermPath kctx ctx c up in
    Data4 md x tbinds ctrs (snd (getEndpoints c)) : up'
chTermPath kctx ctx c (Lambda3 md tBind@(TermBind _ x) ty {-Term-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    let ctx' = delete x ctx in
    let up' = chTermPath kctx ctx' (CArrow (tyInject ty) c) up in
    Lambda3 md tBind ty {-Term-} (snd (getEndpoints c)) : up'
chTermPath kctx ctx c (Buffer1 md {-Term-} defTy body bodyTy : up) =
    if not (fst (getEndpoints c) == defTy) then unsafeThrow "shouldn't happen" else
    Buffer1 md {-Term-} (snd (getEndpoints c)) body bodyTy : up
chTermPath kctx ctx c (TypeBoundary1 md ch {-Term-} : up) = -- TODO: this is one point where we can make different design descisions
    TypeBoundary1 md (composeChange (invert c) ch) : up
chTermPath kctx ctx c (Buffer3 md def defTy {-Term-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    let up' = chTermPath kctx ctx c up in
    let defCh /\ def' = chTerm kctx ctx (tyInject defTy) def in -- TODO: why would the def of the buffer ever change anyway?
    Buffer3 md def' (snd (getEndpoints defCh)) (snd (getEndpoints c)) : up'
chTermPath kctx ctx c (ContextBoundary1 md x varCh {-Term-} : up) =
    let ctx' = alterCCtxVarChange ctx x (invertVarChange varCh) in
    let up' = chTermPath kctx ctx' c up in
    ContextBoundary1 md x varCh {-Term-} : up'
chTermPath kctx ctx c (TLet4 md tyBind@(TypeBind _ x) tyBinds def {-Term-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    let kctx' = delete x kctx in
    let up' = chTermPath kctx' ctx c up in
    TLet4 md tyBind tyBinds def {-Term-} bodyTy : up'
chTermPath _ _ _ _ = unsafeThrow "finish implementing all cases"

chTypePath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
chTypePath kctx ctx ch (Let4 md tBind@(TermBind _ x) tyBinds def {-Type-} body bodyTy : termPath) =
    let ctx' = insert x (VarTypeChange (tyBindsWrapChange tyBinds ch)) ctx in
    let c1 /\ def' = chTerm kctx ctx' ch def in
    let c2 /\ body' = chTerm kctx ctx' (tyInject bodyTy) body in
    let def'' = if chIsId c1 then def' else TypeBoundary defaultTypeBoundaryMD c1 def' in
    let termPath' = chTermPath kctx ctx c2 termPath in
    Let4 md tBind tyBinds def'' body' (snd (getEndpoints c2)) : termPath'
--    Lambda2 LambdaMD TermBind {-Type-} Term Type
chTypePath kctx ctx ch (Lambda2 md tBind@(TermBind _ x) {-Type-} body bodyTy : termPath) =
    let ctx' = insert x (VarTypeChange (PChange ch)) ctx in
    let c /\ body' = chTerm kctx ctx' (tyInject bodyTy) body in
    let termPath' = chTermPath kctx ctx c termPath in
    Lambda2 md tBind {-Type-} body' (snd (getEndpoints c)) : termPath'
--    Let4 LetMD TermBind (List TypeBind) Term {-Type-} Term Type
--    Buffer2 BufferMD Term {-Type-} Term Type
chTypePath kctx ctx ch (Arrow1 md {-Type-} ty2 : typePath) =
    let typePath' = chTypePath kctx ctx (CArrow ch (tyInject ty2)) typePath in
    Arrow1 md {-Type-} ty2 : typePath'
chTypePath kctx ctx ch (Arrow2 md ty1 {-Type-} : typePath) =
    let typePath' = chTypePath kctx ctx (CArrow (tyInject ty1) ch) typePath in
    Arrow2 md ty1 {-Type-} : typePath'
--    CtrParam1 CtrParamMD {-Type-}
--    TypeArg1 TypeArgMD {-Type-}
--    TLet3 TLetMD TypeBind (List TypeBind) {-Type-} Term Type
chTypePath _ _ _ _ = hole' "chTypePath"

-- TODO: I believe that Constructors should change by a Change
chCtrPath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
--    CtrListCons1 {-Constructor-} (List Constructor)
chCtrPath _ _ _ _ = hole' "chCtrPath"

-- TODO: I believe that CtrParams should change by a Change
chCtrParamPath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
--    CtrParamListCons1 {-CtrParam-} (List CtrParam)
chCtrParamPath _ _ _ _ = hole' "chCtrParaPath"


-- I don't believe that there is any need for changing a TypeArgPath
--    TypeArgListCons1 {-TypeArg-} (List TypeArg)

-- I don't believe that there is any need for changing a TypeBindPath
--    TLet1 TLetMD {-TypeBind-} (List TypeBind) Type Term Type
--    TypeBindListCons1 {-TypeBind-} (List TypeBind)
--    Data1 GADTMD {-TypeBind-} (List TypeBind) (List Constructor) Term Type

-- I don't believe that there is any need for changing a TermBindPath
--    Lambda1 LambdaMD {-TermBind-} Type Term Type
--    Let1 LetMD {-TermBind-} (List TypeBind) Term Type Term Type
--    Constructor1 CtrMD {-TermBind-} (List CtrParam)

-- This datatype describes how a list of constructors has changed
-- TODO: PROBLEM: this is unable to describe re-orderings.
-- You can have - c [+ c [...]], but when this is applied to a match expression it will not
-- swap the cases, but rather delete one and create a new empty one!
data ListCtrChange = ListCtrChangeNil | ListCtrChangeCons Change ListCtrChange
    | ListCtrChangePlus Constructor ListCtrChange
    | ListCtrChangeMinus Constructor ListCtrChange
-- The Change by which a CtrListPath changes is the change by which the recursor
chListCtrPath :: KindChangeCtx -> ChangeCtx -> ListCtrChange -> UpPath -> UpPath
--    Data3 GADTMD TypeBind (List TypeBind) {-List Constructor-} Term Type
--    Data2 GADTMD TypeBind {-List TypeBind-} (List Constructor) Term Type
--    CtrListCons2 Constructor {-List Constructor-}
chListCtrPath _ _ _ _ = hole' "chListCtrPath"

-- TODO: again, there will be a problem with swapping!
-- TODO: Should I just use Change instead of ListCtrParamChange? They are more or less the same!
data ListCtrParamChange = ListCtrParamChangeNil | ListCtrParamChangeCons Change ListCtrParamChange
    | ListCtrParamChangePlus CtrParam ListCtrParamChange
    | ListCtrParamChangeMinus CtrParam ListCtrParamChange
chListCtrParamPath :: KindChangeCtx -> ChangeCtx -> ListCtrChange -> UpPath -> UpPath
--    Constructor2 CtrMD TermBind {-List CtrParam-}
--    CtrParamListCons2 CtrParam {-List CtrParam-}
chListCtrParamPath _ _ _ _ = hole' "chListCtrParamPath"

--    TypeArgListCons2 (TypeArg) {-List TypeArg-}
--    TNeu1 TNeuMD TypeVarID {-List TypeArg-}

--    TLet2 TLetMD TypeBind {-List TypeBind-} Type Term Type
--    TypeBindListCons2 (TypeBind) {-List TypeBind-}
