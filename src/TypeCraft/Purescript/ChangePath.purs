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
--    App2 AppMD Term {-Term-} Type Type
--    Lambda3 LambdaMD TermBind Type {-Term-} Type
--    Buffer1 BufferMD {-Term-} Type Term Type
--    TypeBoundary1 TypeBoundaryMD Change {-Term-}
--    Buffer3 BufferMD Term Type {-Term-} Type
--    ContextBoundary1 ContextBoundaryMD TermVarID PolyChange {-Term-}
--    TLet4 TLetMD TypeBind (List TypeBind) Type {-Term-} Type
chTermPath _ _ _ _ = unsafeThrow "finish implementing all cases"

chTypePath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
chTypePath kctx ctx ch (Let3 md tBind@(TermBind _ x) tyBinds def {-Type-} body bodyTy : termPath) =
    let ctx' = insert x (VarTypeChange (tyBindsWrapChange tyBinds ch)) ctx in
    let c1 /\ def' = chTerm kctx ctx' ch def in
    let c2 /\ body' = chTerm kctx ctx' (tyInject bodyTy) body in
    let def'' = if chIsId c1 then def' else TypeBoundary defaultTypeBoundaryMD c1 def' in
    let termPath' = chTermPath kctx ctx c2 termPath in
    Let3 md tBind tyBinds def'' body' (snd (getEndpoints c2)) : termPath'
--    Lambda2 LambdaMD TermBind {-Type-} Term Type
--    Let3 LetMD TermBind (List TypeBind) Term {-Type-} Term Type
--    Buffer2 BufferMD Term {-Type-} Term Type
--    Arrow1 ArrowMD {-Type-} Type
--    Arrow2 ArrowMD Type {-Type-}
--    CtrParam1 CtrParamMD {-Type-}
--    TypeArg1 TypeArgMD {-Type-}
--    TLet3 TLetMD TypeBind (List TypeBind) {-Type-} Term Type
chTypePath _ _ _ _ = hole

-- TODO: I believe that Constructors should change by a Change
chCtrPath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
--    CtrListCons1 {-Constructor-} (List Constructor)
chCtrPath _ _ _ _ = hole

-- TODO: I believe that CtrParams should change by a Change
chCtrParamPath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
--    CtrParamListCons1 {-CtrParam-} (List CtrParam)
chCtrParamPath _ _ _ _ = hole


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
chListCtrPath _ _ _ _ = hole

-- TODO: again, there will be a problem with swapping!
-- TODO: Should I just use Change instead of ListCtrParamChange? They are more or less the same!
data ListCtrParamChange = ListCtrParamChangeNil | ListCtrParamChangeCons Change ListCtrParamChange
    | ListCtrParamChangePlus CtrParam ListCtrParamChange
    | ListCtrParamChangeMinus CtrParam ListCtrParamChange
chListCtrParamPath :: KindChangeCtx -> ChangeCtx -> ListCtrChange -> UpPath -> UpPath
--    Constructor2 CtrMD TermBind {-List CtrParam-}
--    CtrParamListCons2 CtrParam {-List CtrParam-}
chListCtrParamPath _ _ _ _ = hole

--    TypeArgListCons2 (TypeArg) {-List TypeArg-}
--    TNeu1 TNeuMD TypeVarID {-List TypeArg-}

--    TLet2 TLetMD TypeBind {-List TypeBind-} Type Term Type
--    TypeBindListCons2 (TypeBind) {-List TypeBind-}
