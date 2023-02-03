module TypeCraft.Purescript.ChangePath where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.ChangeTerm
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.TypeChangeAlgebra

import Data.List (List(..), (:))
import Data.Maybe (Maybe (..))
import Data.Map.Internal (empty, lookup, insert, delete)
import Data.Tuple (fst)
import Data.Tuple (snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints)
import TypeCraft.Purescript.Util (hole')
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Util (lookup')
import Debug (trace)

-- For now, I won't do anything with upwards ChangeCtx. But I can implement that in the future.

{-
TODO: seemingly, chTermPath should never recieve an input change of the form (Plus ...)
Dually, chTerm should never output an input change of the form (Plus ...)
....
-}

getRightCtxInj :: KindChangeCtx -> ChangeCtx -> CAllContext
getRightCtxInj kctx ctx =
    let ctx1 /\ ctx2 = getCtxEndpoints ctx in
    let kctx1 /\ kctx2 = getKCtxTyEndpoints kctx in
    let actx1 /\ actx2 = getKCtxAliasEndpoints kctx in
    (kCtxInject kctx2 actx2 /\ ctxInject ctx2)

{-
chTermPath inputs D1, C, path1 and outputs path2 and D2 such that
D1 o D2 |- path1 --[C] --> path2
-}
chTermPath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> CAllContext /\ UpPath
chTermPath kctx ctx _ Nil = getRightCtxInj kctx ctx /\ Nil
chTermPath kctx ctx (CArrow c1 c2) (App1 md {-here-} t argTy outTy : up) =
    if not (argTy == fst (getEndpoints c1) && outTy == fst (getEndpoints c2)) then unsafeThrow "shouldn't happen" else
    let (kctx' /\ ctx') /\ up' = chTermPath kctx ctx c2 up in
    let t' = chTermBoundary kctx' ctx' c1 t in
    (kctx' /\ ctx') /\ App1 md t' (snd (getEndpoints c1)) (snd (getEndpoints c2)) : up'
--chTermPath kctx ctx (Minus t1 (Plus t2 c)) (App1 md1 {-here-} arg1 argTy1 outTy1 -- Swap case!
--        : App1 md2 {-Term-} arg2 argTy2 outTy2 : up)
--        | t1 == t2 =
--    if not (outTy1 == Arrow defaultArrowMD argTy2 outTy2) then unsafeThrow "shouldn't happen" else
--    let up' = chTermPath kctx ctx c up in
--    App1 md1 {-Term-} arg2 argTy2 (Arrow defaultArrowMD argTy2 (Arrow defaultArrowMD argTy1 outTy2)) : App1 md2 {-Term-} arg2 argTy2 outTy2 : up'
chTermPath kctx ctx (Minus t c) (App1 md {-here-} arg argTy outTy : up) =
    if not (t == argTy && fst (getEndpoints c) == outTy) then unsafeThrow "shouldn't happen" else
    let (kctx' /\ ctx') /\ up' = chTermPath kctx ctx c up in
    let argTy' /\ chArgTy = chType kctx' argTy in -- This should never really do anything, but it is in theory correct
    let argCh /\ arg' = chTerm kctx' ctx' chArgTy arg in
    (kctx' /\ ctx') /\ Buffer3 defaultBufferMD arg' (snd (getEndpoints argCh)) {-Term-} outTy : up'
-- TODO: App2 case, other App1 cases with other TypeChanges
--    App2 AppMD Term {-Term-} Type Type -- TODO: this case goes along with the polymorphism change stuff
chTermPath kctx ctx ch (Let3 md tBind@(TermBind _ x) tyBinds {-Term = here-} ty body bodyTy : termPath) =
    if not (ty == fst (getEndpoints ch)) then unsafeThrow "shouldn't happen" else
--    let ctx' = insert x (VarTypeChange (tyBindsWrapChange tyBinds ch)) ctx in
    let ctx' = delete x ctx in
    let (kctx' /\ ctx'') /\ termPath' = chTermPath kctx ctx' (tyInject bodyTy) termPath in
    if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
    let ctx''' = insert x (VarTypeChange (tyBindsWrapChange tyBinds ch)) ctx'' in
--    let bodyTy' /\ bodyCh = chType kctx' bodyTy in
    let body' = chTermBoundary kctx' ctx''' (tyInject bodyTy) body in -- TODO TODO TODO TODO:::: There are various other design descisions that could be made here. The issue is that we may want to call chTerm on the body first to get a TypeChange, but then we would need to call it again with the context change gotten from the path above.
    (kctx' /\ ctx''') /\ Let3 md tBind tyBinds {-def-} (snd (getEndpoints ch)) body' bodyTy : termPath'
chTermPath kctx ctx c (Let5 md tBind@(TermBind _ x) tyBinds def defTy {-body = here-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    let ctx' = delete x ctx in
    let (kctx' /\ ctx'') /\ up' = chTermPath kctx ctx' c up in
--    let defTy' /\ defTyCh = chType kctx' defTy in
    -- TODO: in principle, I need to account for possibility that kctx' is not identitiy. But, I've ignored that because I don't think it can happen here.
    if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
    let ctx''' = insert x (VarTypeChange (tyBindsWrapChange tyBinds (tyInject defTy))) ctx'' in
    let def' = chTermBoundary kctx' ctx''' (tyInject defTy) def in -- TODO: why would the def of the let ever change anyway?
    (kctx' /\ ctx''') /\ Let5 md tBind tyBinds def' defTy (snd (getEndpoints c)) : up'
chTermPath kctx ctx c (Data4 md x tbinds ctrs {-body = here-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    -- TODO: update ctrs using kctx and chCtrList
    -- TODO: THIS is wrong, should remove and then add constructors to and from context here!
    let (kctx' /\ ctx') /\ up' = chTermPath kctx ctx c up in
    (kctx' /\ ctx') /\ Data4 md x tbinds ctrs (snd (getEndpoints c)) : up'
chTermPath kctx ctx c (Lambda3 md tBind@(TermBind _ x) ty {-Term-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    let ctx' = delete x ctx in
    let (kctx' /\ ctx'') /\ up' = chTermPath kctx ctx' (CArrow (tyInject ty) c) up in
    let ctx''' = insert x (VarTypeChange (PChange (tyInject ty))) ctx'' in
    -- TODO: again, we make the assumption that kctx' will actually be ID and therefore don't bother with changing defTy.
    if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
    (kctx' /\ ctx''') /\ Lambda3 md tBind ty {-Term-} (snd (getEndpoints c)) : up'
chTermPath kctx ctx c (Buffer1 md {-Term-} defTy body bodyTy : up) =
    -- TODO: should propagate context changes upwards?!
    if not (fst (getEndpoints c) == defTy) then unsafeThrow "shouldn't happen" else
    (kctx /\ ctx) /\ Buffer1 md {-Term-} (snd (getEndpoints c)) body bodyTy : up
chTermPath kctx ctx c (TypeBoundary1 md ch {-Term-} : up) = -- TODO: this is one point where we can make different design decisions
    let (kctx' /\ ctx') /\ up' = chTermPath kctx ctx (tyInject (snd (getEndpoints c))) up in
    (kctx' /\ ctx') /\ TypeBoundary1 md (composeChange (invert c) ch) : up'
chTermPath kctx ctx c (Buffer3 md def defTy {-Term-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    let (kctx' /\ ctx') /\ up' = chTermPath kctx ctx c up in
    if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
--    let defCh /\ def' = chTerm kctx ctx (tyInject defTy) def in -- TODO: why would the def of the buffer ever change anyway?
    (kctx' /\ ctx') /\ Buffer3 md def defTy {-def' (snd (getEndpoints defCh))-} (snd (getEndpoints c)) : up'
chTermPath kctx ctx c (ContextBoundary1 md x varCh {-Term-} : up) =
    let ctx' = alterCCtxVarChange ctx x (invertVarChange varCh) in
    let (kctx' /\ ctx'') /\ up' = chTermPath kctx ctx' c up in
    if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
    let ctx''' = alterCCtxVarChange ctx x varCh in
    (kctx' /\ ctx''') /\ ContextBoundary1 md x varCh {-Term-} : up'
chTermPath kctx ctx c (TLet4 md tyBind@(TypeBind _ x) tyBinds def {-Term-} bodyTy : up) =
    if not (fst (getEndpoints c) == bodyTy) then unsafeThrow "shouldn't happen" else
    let pop = lookup' x kctx in
    let kctx' = delete x kctx in
    let (kctx'' /\ ctx') /\ up' = chTermPath kctx' ctx c up in
    if not (kCtxIsId kctx'') then unsafeThrow "ktx assumptinon violated" else
    let kctx''' = insert x pop kctx'' in
    (kctx''' /\ ctx') /\ TLet4 md tyBind tyBinds def {-Term-} bodyTy : up'
chTermPath _ _ ch path = unsafeThrow ("finish implementing all cases. Path is:" <> show path <> "and ch is: " <> show ch)

chTypePath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> CAllContext /\ UpPath
chTypePath kctx ctx ch (Let4 md tBind@(TermBind _ x) tyBinds def {-Type-} body bodyTy : termPath) =
--    let (kctx' /\ ctx') /\ termPath' = chTermPath kctx ctx (tyInject bodyTy) termPath in
    if not (kCtxIsId kctx) then unsafeThrow "ktx assumptinon violated" else
    let ctx' = insert x (VarTypeChange (tyBindsWrapChange tyBinds ch)) ctx in
    let body' = chTermBoundary kctx ctx' (tyInject bodyTy) body in -- TODO TODO TODO TODO:::: There are various other design descisions that could be made here. The issue is that we may want to call chTerm on the body first to get a TypeChange, but then we would need to call it again with the context change gotten from the path above.
    let def' = chTermBoundary kctx ctx' ch def in
    (kctx /\ ctx') /\ Let4 md tBind tyBinds def' body' bodyTy : termPath
chTypePath kctx ctx ch (Lambda2 md tBind@(TermBind _ x) {-Type-} body bodyTy : termPath) =
    let ctx' = insert x (VarTypeChange (PChange ch)) ctx in
    let c /\ body' = chTerm kctx ctx' (tyInject bodyTy) body in
    let (kctx' /\ ctx2) /\ termPath' = chTermPath kctx ctx (CArrow c (tyInject bodyTy)) termPath in
    if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
    (kctx' /\ ctx2) /\ Lambda2 md tBind {-Type-} body' (snd (getEndpoints c)) : termPath'
chTypePath kctx ctx ch (Arrow1 md {-Type-} ty2 : typePath) =
    let (kctx' /\ ctx') /\ typePath' = chTypePath kctx ctx (CArrow ch (tyInject ty2)) typePath in
    (kctx' /\ ctx') /\ Arrow1 md {-Type-} ty2 : typePath'
chTypePath kctx ctx ch (Arrow2 md ty1 {-Type-} : typePath) =
    let (kctx' /\ ctx') /\ typePath' = chTypePath kctx ctx (CArrow (tyInject ty1) ch) typePath in
    (kctx' /\ ctx') /\ Arrow2 md ty1 {-Type-} : typePath'
--    Buffer2 BufferMD Term {-Type-} Term Type
--    CtrParam1 CtrParamMD {-Type-}
--    TypeArg1 TypeArgMD {-Type-}
--    TLet3 TLetMD TypeBind (List TypeBind) {-Type-} Term Type
chTypePath _ _ ch path = hole' ("chTypePath. Path is:" <> show path <> "and ch is: " <> show ch)

chCtrPath :: KindChangeCtx -> ChangeCtx -> TermVarID -> ListCtrParamChange -> UpPath -> UpPath
chCtrPath kctx ctx x ch (CtrListCons1 {-ctr-} ctrs : ctrListPath) =
    let ctrsCh /\ ctrs' = chCtrList kctx ctrs in
    let ctrListPath' = chListCtrPath kctx ctx (ListCtrChangeCons x ch ctrsCh) ctrListPath in
    CtrListCons1 {--} ctrs' : ctrListPath'
chCtrPath _ _ _ _ _ = hole' "chCtrPath"

-- TODO: I believe that CtrParams should change by a Change
chCtrParamPath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
--    CtrParamListCons1 {-CtrParam-} (List CtrParam)
chCtrParamPath kctx ctx ch (CtrParamListCons1 {-ctrParam-} ctrParams : listCtrParamPath) =
    let ctrParamsCh /\ ctrParams' = chParamList kctx ctrParams in
    let listCtrParamListPath' = chListCtrParamPath kctx ctx ctrParamsCh listCtrParamPath in
    CtrParamListCons1 {--} ctrParams' : listCtrParamListPath'
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

-- The Change by which a CtrListPath changes is the change by which the recursor
chListCtrPath :: KindChangeCtx -> ChangeCtx -> ListCtrChange -> UpPath -> UpPath
chListCtrPath kctx ctx ch (Data3 md tyBind@(TypeBind _ x) tyBinds {-ctrs-} body bodyTy : termPath) =
    let ctx' = adjustCtxByCtrChanges x (map (\(TypeBind _ x) -> x) tyBinds) ch ctx in
    -- TODO: here I make an assumption that the context hasn't changed above!
    let _ /\ termPath' = chTermPath kctx ctx' (tyInject bodyTy) termPath in
    let body' = chTermBoundary kctx ctx' (tyInject bodyTy) body in
    Data3 md tyBind tyBinds {--} body' bodyTy : termPath'
chListCtrPath kctx ctx ch (CtrListCons2 ctr@(Constructor _ (TermBind _ x) ctrParams) {-ctrs-} : listCtrPath) =
    let listCtrParamCh /\ ctrParams' = chParamList kctx ctrParams in
    let listCtrPath' = chListCtrPath kctx ctx (ListCtrChangeCons x listCtrParamCh ch) listCtrPath in
    (CtrListCons2 ctr {--}) : listCtrPath'
chListCtrPath _ _ _ _ = hole' "chListCtrPath"

chListCtrParamPath :: KindChangeCtx -> ChangeCtx -> ListCtrParamChange -> UpPath -> UpPath
chListCtrParamPath kctx ctx ch (Constructor2 md tBind@(TermBind _ x) {-ctrParams-} : listCtrPath) =
    let listCtrPath' = chCtrPath kctx ctx x ch listCtrPath in
    Constructor2 md tBind {--} : listCtrPath'
chListCtrParamPath kctx ctx ch (CtrParamListCons2 ctrParam@(CtrParam _ ty) {-ctrParams-}: listCtrParamPath) =
    let listCtrParamPath' = chListCtrParamPath kctx ctx (ListCtrParamChangeCons (tyInject ty) ch) listCtrParamPath in
    (CtrParamListCons2 ctrParam {--}) : listCtrParamPath'
chListCtrParamPath _ _ _ _ = hole' "chListCtrParamPath"

data ListTypeArgChange = ListTypeArgChangeNil | ListTypeArgChangeCons Change ListTypeArgChange

chListTypeArgPath :: KindChangeCtx -> ChangeCtx -> ListTypeArgChange -> UpPath -> UpPath
--    TypeArgListCons2 (TypeArg) {-List TypeArg-}
--    TNeu1 TNeuMD TypeVarID {-List TypeArg-}
chListTypeArgPath = hole' "chListTypeArgPath"


-- This function should enable adding type parameters to lets
chListTypeBindPath :: KindChangeCtx -> ChangeCtx -> ListTypeBindChange -> UpPath -> UpPath
--    TLet2 TLetMD TypeBind {-List TypeBind-} Type Term Type
--    Data2 GADTMD TypeBind {-List TypeBind-} (List Constructor) Term Type
--    Let2 LetMD TermBind {-List TypeBind-} Term Type Term Type
chListTypeBindPath kctx ctx ch (Let2 md tBind@(TermBind _ x) {-tyBinds-} def defTy body bodyTy : termPath) =
    -- TODO: here I make an assumption that the context hasn't changed above!
    let _ /\ termPath' = chTermPath kctx ctx (tyInject bodyTy) termPath in
    let polyTyCh = listTypeBindChWrapPolyChange ch (tyInject defTy) in
    let ctx' = insert x (VarTypeChange polyTyCh) ctx in
    let def' = chTermBoundary kctx ctx' (tyInject defTy) def in
    let body' = chTermBoundary kctx ctx' (tyInject bodyTy) body in
    Let2 md tBind {--} def' defTy body' bodyTy : termPath'
chListTypeBindPath kctx ctx ch (TypeBindListCons2 tyBind {-tyBinds-} : listTypeBindPath) =
    let listTypeBindPath' = chListTypeBindPath kctx ctx (ListTypeBindChangeCons tyBind ch) listTypeBindPath in
    TypeBindListCons2 tyBind {--} : listTypeBindPath'
chListTypeBindPath _ _ _ _ = hole' "chTypeBindPath"