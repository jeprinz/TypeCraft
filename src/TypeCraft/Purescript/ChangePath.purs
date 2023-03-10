module TypeCraft.Purescript.ChangePath where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.ChangeTerm
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.TypeChangeAlgebra

import Data.List (List(..), (:))
import Data.List as List
import Data.Map as Map
import Data.Maybe (Maybe (..))
import Data.Map.Internal (empty, lookup, insert, delete)
import Data.Tuple (fst)
import Data.Tuple (snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.TypeChangeAlgebra (getEndpoints)
import TypeCraft.Purescript.Util (hole')
--import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Util (lookup')
import Debug (trace)
import TypeCraft.Purescript.Util (delete')
import TypeCraft.Purescript.PathRec

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
-- TODO: why does chTermPath even output a KindChangeContext at all!?!??
chTermPath :: Change -> TermPathRecValue -> CAllContext /\ UpPath
chTermPath _ {ctxs, termPath: Nil} = (kCtxInject ctxs.kctx ctxs.actx /\ ctxInject ctxs.ctx) /\ Nil
chTermPath ch termPath =
    let kctx = termPath.ctxs.kctx in
    let actx = termPath.ctxs.actx in
    let ctx = termPath.ctxs.ctx in
    let idChkctx = kCtxInject kctx actx in
    let idChCtx = ctxInject ctx in
    recTermPath {
        let3: \up md tBind@{tBind: TermBind _ x} tyBinds defTy body bodyTy ->
            if not (defTy.ty == fst (getEndpoints ch)) then unsafeThrow ("shouldn't happen chPath 3: defTy.ty is: " <> show defTy.ty <> "and thing is: " <> show (fst (getEndpoints ch))) else
            let (kctx'' /\ ctx'') /\ termPath' = chTermPath (tyInject bodyTy) up in
            if not (kCtxIsId kctx'') then unsafeThrow "ktx assumptinon violated" else
            let ctx''' = insert x (VarTypeChange (tyBindsWrapChange tyBinds.tyBinds ch)) ctx'' in
            let body' = chTermBoundary kctx'' ctx''' (tyInject bodyTy) body.term in -- TODO TODO TODO TODO:::: There are various other design descisions that could be made here. The issue is that we may want to call chTerm on the body first to get a TypeChange, but then we would need to call it again with the context change gotten from the path above.
            let kctx''' = addLetToKCCtx kctx'' tyBinds.tyBinds in
            (kctx''' /\ ctx''') /\ Let3 md tBind.tBind tyBinds.tyBinds {-def-} (snd (getEndpoints ch)) body' bodyTy : termPath'
        , let5: \up md tBind@{tBind: TermBind _ x} {tyBinds} def defTy bodyTy ->
            if not (fst (getEndpoints ch) == bodyTy) then unsafeThrow "shouldn't happen chPath 4" else
            let (kctx'' /\ ctx'') /\ up' = chTermPath ch up in
            -- We assume that kctx'' coming back down is identity
            if not (kCtxIsId kctx'') then unsafeThrow "ktx assumptinon violated" else
            let ctx''' = insert x (VarTypeChange (tyBindsWrapChange tyBinds (tyInject defTy.ty))) ctx'' in
            let kctx''' = addLetToKCCtx kctx'' tyBinds in
            let def' = chTermBoundary kctx'' ctx''' (tyInject defTy.ty) def.term in -- TODO: why would the def of the let ever change anyway?
            (kctx''' /\ ctx''') /\ Let5 md tBind.tBind tyBinds def' defTy.ty (snd (getEndpoints ch)) : up'
        , data4: \up md tyBind tyBinds ctrs bodyTy ->
            if not (fst (getEndpoints ch) == bodyTy) then unsafeThrow "shouldn't happen chPath 5" else
            let (kctx' /\ ctx') /\ up' = chTermPath ch up in
            let kctx'' = addDataToKCCtx kctx' tyBind.tyBind tyBinds.tyBinds in
            let ctx'' = addDataToCCtx ctx' tyBind.tyBind tyBinds.tyBinds ctrs.ctrs in
            (kctx'' /\ ctx'') /\ Data4 md tyBind.tyBind tyBinds.tyBinds ctrs.ctrs (snd (getEndpoints ch)) : up'
        , app1 : \up md {-Term-} t2 argTy outTy ->
            case ch of
                (CArrow c1 c2) ->
                    if not (argTy == fst (getEndpoints c1) && outTy == fst (getEndpoints c2)) then unsafeThrow "shouldn't happen chPath 1" else
                    let (kctx' /\ ctx') /\ up' = chTermPath c2 up in
                    let t' = chTermBoundary kctx' ctx' c1 t2.term in
                    (kctx' /\ ctx') /\ App1 md t' (snd (getEndpoints c1)) (snd (getEndpoints c2)) : up'
                (Minus t c) ->
                    if not (t == argTy && fst (getEndpoints c) == outTy) then unsafeThrow "shouldn't happen chPath 2" else
                    let argTy'_ /\ chArgTy = chType idChkctx argTy in -- This should never really do anything, but it is in theory correct
                    let (kctx' /\ ctx') /\ up' = chTermPath c up in
                    let argCh /\ t2' = chTerm idChkctx idChCtx chArgTy t2.term in
                    (kctx' /\ ctx') /\ Buffer3 defaultBufferMD t2' (snd (getEndpoints argCh)) {-Term-} outTy : up'
                _ -> unsafeThrow "shouldn't get herer app1 case of chTermPath'"
        , app2 : \up md t {-Term-} argTy outTy ->
            if not (fst (getEndpoints ch) == argTy) then unsafeThrow "shouldn't happen chTermPath App2 case" else
            let chtUp /\ t' = chTerm idChkctx idChCtx (CArrow ch (tyInject outTy)) t.term in
            case chtUp of
                CArrow chArg chOut ->
                    let (kctx' /\ ctx') /\ up' = chTermPath chOut up in
                    let t'' = chTermBoundary kctx' ctx' (tyInject (snd (getEndpoints chtUp))) t' in
                    (kctx' /\ ctx') /\ App2 md t'' {--} (snd (getEndpoints chArg)) (snd (getEndpoints chOut)) : up'
                _ -> hole' "chTermPath App2 case, not sure what to do here..."
        , lambda3 : \up md tBind@{tBind: TermBind _ x} argTy {-body-} bodyTy ->
            if not (fst (getEndpoints ch) == bodyTy) then unsafeThrow ("shouldn't happen chPath 6. bodyTy is: " <> show bodyTy <> "and ch is: " <> show ch) else
            let (kctx' /\ ctx'') /\ up' = chTermPath (CArrow (tyInject argTy.ty) ch) up in
            let ctx''' = insert x (VarTypeChange (PChange (tyInject argTy.ty))) ctx'' in
            -- TODO: again, we make the assumption that kctx' will actually be ID and therefore don't bother with changing defTy.
            if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
            (kctx' /\ ctx''') /\ Lambda3 md tBind.tBind argTy.ty {-Term-} (snd (getEndpoints ch)) : up'
        , buffer1 : \up md {-Term-} bufTy body bodyTy ->
            -- TODO: should propagate context changes upwards?!
            if not (fst (getEndpoints ch) == bufTy.ty) then unsafeThrow "shouldn't happen chPath 7" else
            (idChkctx /\ idChCtx) /\ Buffer1 md {-Term-} (snd (getEndpoints ch)) body.term bodyTy : up.termPath
        , buffer3 : \up md buf bufTy {-Term-} bodyTy ->
            if not (fst (getEndpoints ch) == bodyTy) then unsafeThrow "shouldn't happen chPath 8" else
            let (kctx' /\ ctx') /\ up' = chTermPath ch up in
            if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
        --    let defCh /\ def' = chTerm kctx ctx (tyInject defTy) def in -- TODO: why would the def of the buffer ever change anyway?
            (kctx' /\ ctx') /\ Buffer3 md buf.term bufTy.ty {-def' (snd (getEndpoints defCh))-} (snd (getEndpoints ch)) : up'
        , typeBoundary1 : \up md change {-Term-} ->
            let (kctx' /\ ctx') /\ up' = chTermPath (tyInject (snd (getEndpoints ch))) up in
            (kctx' /\ ctx') /\ TypeBoundary1 md (composeChange (invert ch) change) : up'
        , contextBoundary1 : \up md x varCh {-Term-} ->
            let (kctx' /\ ctx'') /\ up' = chTermPath ch up in
            if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
            let ctx''' = alterCCtxVarChange ctx'' x varCh in
            (kctx' /\ ctx''') /\ ContextBoundary1 md x varCh {-Term-} : up'
        , tLet4 : \up md tyBind@(TypeBind _ x) tyBinds def {-Term-} bodyTy ->
            if not (fst (getEndpoints ch) == bodyTy) then unsafeThrow "shouldn't happen chPath 9" else
            let popKind = lookup' x kctx in
            let popTyDefInfo = lookup' x actx in
            let (kctx'' /\ ctx') /\ up' = chTermPath ch up in
            if not (kCtxIsId kctx'') then unsafeThrow "ktx assumptinon violated" else
            let kctx''' = insert x (TVarKindChange (kindInject popKind) (Just $ tacInject popTyDefInfo)) kctx'' in
            (kctx''' /\ ctx') /\ TLet4 md tyBind tyBinds.tyBinds def.ty {-Term-} bodyTy : up'
    } termPath

chTypePath :: Change -> TypePathRecValue -> CAllContext /\ UpPath
chTypePath ch typePath =
    let kctx = typePath.ctxs.kctx in
    let actx = typePath.ctxs.actx in
    let ctx = typePath.ctxs.ctx in
    let idChkctx = kCtxInject kctx actx in
    let idChCtx = ctxInject ctx in
    recTypePath {
      lambda2:
        \termPath md tBind@{tBind: TermBind _ x} {-Type-} body bodyTy ->
            let c /\ body' = chTerm (kCtxInject body.ctxs.kctx body.ctxs.actx) (ctxInject body.ctxs.ctx) (tyInject bodyTy) body.term in
            let (kctx' /\ ctx2) /\ termPath' = chTermPath (CArrow c (tyInject bodyTy)) termPath in
            if not (kCtxIsId kctx') then unsafeThrow "ktx assumptinon violated" else
            (kctx' /\ ctx2) /\ Lambda2 md tBind.tBind {-Type-} body' (snd (getEndpoints c)) : termPath'
        , let4: \termPath md tBind@{tBind: TermBind _ x} tyBinds def {-Type-} body bodyTy ->
        --    let (kctx' /\ ctx') /\ termPath' = chTermPath kctx ctx (tyInject bodyTy) termPath in
            let innerCtx = insert x (VarTypeChange (tyBindsWrapChange tyBinds.tyBinds ch)) (ctxInject ctx) in
            let body' = chTermBoundary (kCtxInject body.ctxs.kctx body.ctxs.actx) innerCtx (tyInject bodyTy) body.term in
            let def' = chTermBoundary (kCtxInject def.ctxs.kctx def.ctxs.actx) innerCtx ch def.term in
            (idChkctx /\ idChCtx) /\ Let4 md tBind.tBind tyBinds.tyBinds def' body' bodyTy : termPath.termPath
        , buffer2: \termPath md def {-Type-} body bodyTy -> hole' "chTypePath"
        , tLet3: \termPath md tyBind tyBinds {-Type-} body bodyTy -> hole' "chTypePath"
        , ctrParam1: \ctrParamPath md {-Type-} -> hole' "chTypePath"
        , typeArg1: \tyArgPath md {-Type-} ->  hole' "chTypePath"
        , arrow1: \typePath md {-Type-} ty2 ->
            let (kctx' /\ ctx') /\ typePath' = chTypePath (CArrow ch (tyInject ty2.ty)) typePath in
            (kctx' /\ ctx') /\ Arrow1 md {-Type-} ty2.ty : typePath'
        , arrow2: \typePath md ty1 {-Type-} ->
            let (kctx' /\ ctx') /\ typePath' = chTypePath (CArrow (tyInject ty1.ty) ch) typePath in
            (kctx' /\ ctx') /\ Arrow2 md ty1.ty {-Type-} : typePath'
} typePath

chCtrPath :: TermVarID -> ListCtrParamChange -> CtrPathRecValue -> UpPath
chCtrPath x ch ctrPath =
    let kctx = ctrPath.ctxs.kctx in
    let actx = ctrPath.ctxs.actx in
    let ctx = ctrPath.ctxs.ctx in
    let idChkctx = kCtxInject kctx actx in
    let idChCtx = ctxInject ctx in
    recCtrPath {
        ctrListCons1: \listCtrPath ctrs ->
            let ctrsCh /\ ctrs' = chCtrList idChkctx ctrs.ctrs in
            let ctrListPath' = chListCtrPath (ListCtrChangeCons x ch ctrsCh) listCtrPath in
            CtrListCons1 {--} ctrs' : ctrListPath'
    } ctrPath


--
---- TODO: I believe that CtrParams should change by a Change
--chCtrParamPath :: KindChangeCtx -> ChangeCtx -> Change -> UpPath -> UpPath
----    CtrParamListCons1 {-CtrParam-} (List CtrParam)
--chCtrParamPath kctx ctx ch (CtrParamListCons1 {-ctrParam-} ctrParams : listCtrParamPath) =
--    let ctrParamsCh /\ ctrParams' = chParamList kctx ctrParams in
--    let listCtrParamListPath' = chListCtrParamPath kctx ctx ctrParamsCh listCtrParamPath in
--    CtrParamListCons1 {--} ctrParams' : listCtrParamListPath'
--chCtrParamPath _ _ _ _ = hole' "chCtrParaPath"
--
--
---- I don't believe that there is any need for changing a TypeArgPath
----    TypeArgListCons1 {-TypeArg-} (List TypeArg)
--
---- I don't believe that there is any need for changing a TypeBindPath
----    TLet1 TLetMD {-TypeBind-} (List TypeBind) Type Term Type
----    TypeBindListCons1 {-TypeBind-} (List TypeBind)
----    Data1 GADTMD {-TypeBind-} (List TypeBind) (List Constructor) Term Type
--
---- I don't believe that there is any need for changing a TermBindPath
----    Lambda1 LambdaMD {-TermBind-} Type Term Type
----    Let1 LetMD {-TermBind-} (List TypeBind) Term Type Term Type
----    Constructor1 CtrMD {-TermBind-} (List CtrParam)
--


---- The Change by which a CtrListPath changes is the change by which the recursor
chListCtrPath :: ListCtrChange -> ListCtrPathRecValue -> UpPath
chListCtrPath ch ctrPath =
    let idkchctx = (kCtxInject ctrPath.ctxs.kctx ctrPath.ctxs.actx) in
    recListCtrPath {
        data3: \termPath md tyBind tyBinds body bodyTy ->
            let (kctx /\ ctx) /\ termPath' = chTermPath (tyInject bodyTy) termPath in
            let body' = chTermBoundary kctx ctx (tyInject bodyTy) body.term in
            Data3 md tyBind.tyBind tyBinds.tyBinds {--} body' bodyTy : termPath'
        , ctrListCons2: \listCtrPath ctr@{ctr: (Constructor _ (TermBind _ x) ctrParams)} ->
            let listCtrParamCh /\ ctrParams' = chParamList idkchctx ctrParams in
            let listCtrPath' = chListCtrPath (ListCtrChangeCons x listCtrParamCh ch) listCtrPath in
            (CtrListCons2 ctr.ctr {--}) : listCtrPath'
    } ctrPath

chListCtrParamPath :: ListCtrParamChange -> ListCtrParamPathRecValue -> UpPath
chListCtrParamPath ch ctrParamPath =
    recListCtrParamPath {
        constructor2: \listCtrPath md tBind@{tBind: TermBind _ x} ->
            let listCtrPath' = chCtrPath x ch listCtrPath in
            Constructor2 md tBind.tBind {--} : listCtrPath'
        , ctrParamListCons2: \listCtrParamPath ctrParam@{ctrParam: CtrParam _ ty} ->
            let listCtrParamPath' = chListCtrParamPath (ListCtrParamChangeCons (tyInject ty) ch) listCtrParamPath in
            (CtrParamListCons2 ctrParam.ctrParam {--}) : listCtrParamPath'
    } ctrParamPath


data ListTypeArgChange = ListTypeArgChangeNil | ListTypeArgChangeCons Change ListTypeArgChange

chListTypeArgPath :: ListTypeArgChange -> ListTypeArgPathRecValue -> UpPath
chListTypeArgPath ch listTyArgPath =
    recListTypeArgPath {
        tNeu1: \typePath md x -> hole' "chListTypeArgPath"
        , typeArgListCons2: \listTypeArgPath tyArg -> hole' "chListTypeArgPath"
        , var1 : \termPath md x -> hole' "chListTypeArgPath"
    } listTyArgPath

chListTypeBindPath :: ListTypeBindChange -> ListTypeBindPathRecValue -> UpPath
chListTypeBindPath ch listTypeBindPath =
    recListTypeBindPath {
        data2 : \termPath md tyBind ctrs body bodyTy -> hole'  "chListTypeBindPath"
        , tLet2 : \termPath md tyBind def body bodyTy -> hole'  "chListTypeBindPath"
        , typeBindListCons2 : \listTypeBindPath tyBind ->
            let listTypeBindPath' = chListTypeBindPath (ListTypeBindChangeCons tyBind.tyBind ch) listTypeBindPath in
            TypeBindListCons2 tyBind.tyBind {--} : listTypeBindPath'
        , let2 : \termPath md tBind@{tBind: TermBind _ x} def defTy body bodyTy ->
            -- TODO: here I make an assumption that the context hasn't changed above!
            let (kctx /\ ctx) /\ termPath' = chTermPath (tyInject bodyTy) termPath in
            let kctx' = addTyBindChsToKCCtx ch kctx in
            let defTy' /\ defCh = chType kctx' defTy.ty in
            let polyTyCh = listTypeBindChWrapPolyChange ch defCh in
            let ctx' = insert x (VarTypeChange polyTyCh) ctx in
            let def' = chTermBoundary kctx' ctx' defCh def.term in
            let body' = chTermBoundary kctx' ctx' (tyInject bodyTy) body.term in
            Let2 md tBind.tBind {--} def' defTy' body' bodyTy : termPath'
    } listTypeBindPath