module TypeCraft.Purescript.PathToNode where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.PathRec
import TypeCraft.Purescript.TermToNode
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.Context (AllContext)
import TypeCraft.Purescript.Grammar (Constructor, CtrParam, DownPath, Term, Tooth(..), Type, TypeArg, TypeBind, UpPath)
import TypeCraft.Purescript.Node (Node, NodeTag, makeNode)
import TypeCraft.Purescript.State (CursorLocation(..), Mode(..), Select(..), makeCursorMode, topSelectOrientation)
import TypeCraft.Purescript.Util (hole', justWhen)
import TypeCraft.Purescript.Util (hole)

data BelowInfo term ty -- NOTE: a possible refactor is to combine term and ty into syn like in TermToNode. On the other hand, I'll probably never bother.
  = BITerm
  | BISelect UpPath term AllContext ty -- middle path, then bottom term. ctx and ty are the type and context of term.

{-
stepBI :: forall gsort1 gsort2. Tooth -> BelowInfo gsort1 -> BelowInfo gsort2
stepBI tooth (BITerm syn) = BITerm (step syn)
stepBI tooth (BISelect path syn) = BISelect (tooth : path) syn
stepBI = hole
-}
-- TODO: this function is the sketchies thing about my whole setup!!!!!
-- TODO: TODO: think about this!
-- TODO: @jacob think about this
stepBI :: forall syn synty. Tooth -> BelowInfo syn synty -> BelowInfo syn synty
stepBI _tooth BITerm = BITerm
stepBI tooth (BISelect middle bottom ctxs ty) = BISelect (middle <> (tooth : Nil)) bottom ctxs ty

arrangeKid :: forall a recVal. UpPath -> UpPath -> (AboveInfo a -> recVal -> Node) -> recVal -> PreNode
arrangeKid path abovePath k rv th = k (AICursor (th : path <> abovePath)) rv

--arrangeKid :: forall term ty rc. BelowInfo term ty -> (BelowInfo term ty -> rc -> Node) -> rc -> PreNode
--arrangeKid bi k rc ind th = setNodeIndentation ind $ k (stepBI th bi) rc
type PartialNode
  = { kids :: Array Node
    , tag :: NodeTag
    }


-- The MDType is for the top of the path (which is the end of the list)
termPathToNode :: Boolean -> UpPath -> BelowInfo Term Type -> TermPathRecValue -> (Node -> Node)
termPathToNode _isActive _abovePath _ { termPath: Nil } node = node
termPathToNode isActive abovePath belowInfo termPath innerNode =
  let
    term = termPath.term
  in
    recTermPath
      { let3:
          \upRecVal md tBind tyBinds {-def-} ty body bodyTy ->
            let
              newBI = (stepBI (Let3 md tBind.tBind tyBinds.tyBinds ty.ty body.term bodyTy) belowInfo)
            in
              termPathToNode isActive abovePath newBI upRecVal
                $ arrangeTerm (makeTermArgs isActive abovePath newBI upRecVal)
                    [ arrangeKid upRecVal.termPath abovePath (termBindToNode isActive) tBind
                    , arrangeKid upRecVal.termPath abovePath (typeBindListToNode isActive) tyBinds
                    , arrangeKid upRecVal.termPath abovePath (typeToNode isActive) ty
                    , arrangeKid upRecVal.termPath abovePath (\_ _ -> innerNode) term
                    , arrangeKid upRecVal.termPath abovePath (termToNode isActive) body
                    ]
      , app1:
          \upRecVal md {-Term-} t2 argTy bodyTy ->
            let
              newBI = (stepBI (App1 md {-t1-} t2.term argTy bodyTy) belowInfo)
            in
              termPathToNode isActive abovePath newBI upRecVal
                $ arrangeTerm (makeTermArgs isActive abovePath newBI upRecVal)
                    [ arrangeKid upRecVal.termPath abovePath (\_ _ -> innerNode) term
                    , arrangeKid upRecVal.termPath abovePath (termToNode isActive) t2
                    ]
      , app2:
          \upRecVal md t1 {-Term-} argTy bodyTy ->
            let
              newBI = (stepBI (App2 md {--} t1.term argTy bodyTy) belowInfo)
            in
              termPathToNode isActive abovePath newBI upRecVal
                $ arrangeTerm (makeTermArgs isActive abovePath newBI upRecVal)
                    [ arrangeKid upRecVal.termPath abovePath (termToNode isActive) t1
                    , arrangeKid upRecVal.termPath abovePath (\_ _ -> innerNode) term
                    ]
      , lambda3:
          \upRecVal md tBind argTy {-body-} bodyTy ->
            let
              newBI = (stepBI (Lambda3 md tBind.tBind argTy.ty bodyTy) belowInfo)
            in
              termPathToNode isActive abovePath newBI upRecVal
                $ arrangeTerm (makeTermArgs isActive abovePath newBI upRecVal)
                    [ arrangeKid upRecVal.termPath abovePath (termBindToNode isActive) tBind
                    , arrangeKid upRecVal.termPath abovePath (typeToNode isActive) argTy
                    , arrangeKid upRecVal.termPath abovePath (\_ _ -> innerNode) term
                    ]
      , buffer1: \upRecVal md {-Term-} bufTy body bodyTy -> hole' "termPathToNode 1"
      , buffer3: \upRecVal md buf bufTy {-Term-} bodyTy -> hole' "termPathToNode 2"
      , typeBoundary1: \upRecVal md change {-Term-} -> hole' "termPathToNode 3"
      , contextBoundary1: \upRecVal md x change {-Term-} -> hole' "termPathToNode 4"
      , tLet4:
          \upRecVal md tyBind tyBinds def {-Term-} bodyTy ->
            let
              newBI = (stepBI (TLet4 md tyBind tyBinds.tyBinds def.ty bodyTy) belowInfo)
            in
              termPathToNode isActive abovePath newBI upRecVal
                $ arrangeTerm (makeTermArgs isActive abovePath newBI upRecVal)
                    [ arrangeKid upRecVal.termPath abovePath (typeBindToNode isActive) { ctxs: upRecVal.ctxs, tyBind }
                    , arrangeKid upRecVal.termPath abovePath (typeBindListToNode isActive) tyBinds
                    , arrangeKid upRecVal.termPath abovePath (typeToNode isActive) def
                    , arrangeKid upRecVal.termPath abovePath (\_ _ -> innerNode) term
                    ]
      , let5:
          \upRecVal md tBind tyBinds def ty {-body-} bodyTy ->
            let
              newBI = (stepBI (Let5 md tBind.tBind tyBinds.tyBinds def.term ty.ty {-body-} bodyTy) belowInfo)
            in
              termPathToNode isActive abovePath newBI upRecVal
                $ arrangeTerm (makeTermArgs isActive abovePath newBI upRecVal)
                    [ arrangeKid upRecVal.termPath abovePath (termBindToNode isActive) tBind
                    , arrangeKid upRecVal.termPath abovePath (typeBindListToNode isActive) tyBinds
                    , arrangeKid upRecVal.termPath abovePath (typeToNode isActive) ty
                    , arrangeKid upRecVal.termPath abovePath (termToNode isActive) def
                    , arrangeKid upRecVal.termPath abovePath (\_ _ -> innerNode) term
                    ]
      , data4:
          \upRecVal md tyBind tyBinds ctrs {-body-} bodyTy ->
            let
              newBI = (stepBI (Data4 md tyBind.tyBind tyBinds.tyBinds ctrs.ctrs {-body-} bodyTy) belowInfo)
            in
              termPathToNode isActive abovePath newBI upRecVal
                $ arrangeTerm (makeTermArgs isActive abovePath newBI upRecVal)
                    [ arrangeKid upRecVal.termPath abovePath (typeBindToNode isActive) tyBind
                    , arrangeKid upRecVal.termPath abovePath (typeBindListToNode isActive) tyBinds
                    , arrangeKid upRecVal.termPath abovePath (ctrListToNode isActive) ctrs
                    , arrangeKid upRecVal.termPath abovePath (\_ _ -> innerNode) term
                    ]
      }
      termPath

makeTermArgs :: Boolean -> UpPath -> BelowInfo Term Type -> TermPathRecValue -> TermNodeCursorInfo
makeTermArgs isActive abovePath belowInfo upRecVal =
  { isActive
  , makeCursor: \_ -> Just $ TermCursor upRecVal.ctxs upRecVal.ty (upRecVal.termPath <> abovePath) upRecVal.term
  , makeSelect:
      \_ -> case belowInfo of
        BITerm -> Nothing
        BISelect middlePath term ctxs ty -> Just $ TermSelect (upRecVal.termPath <> abovePath) upRecVal.ctxs upRecVal.ty upRecVal.term middlePath ctxs ty term topSelectOrientation
  , term: { ctxs: upRecVal.ctxs, term: upRecVal.term, ty: upRecVal.ty }
  }

makeTypeArgs :: Boolean -> UpPath -> BelowInfo Type Unit -> TypePathRecValue -> TypeNodeCursorInfo
makeTypeArgs isActive abovePath belowInfo urv =
  { isActive
  , makeCursor: \_ -> Just $ TypeCursor urv.ctxs (urv.typePath <> abovePath) urv.ty
  , makeSelect:
      \_ -> case belowInfo of
        BITerm -> Nothing
        BISelect middlePath ty ctxs _ -> Just $ TypeSelect (urv.typePath <> abovePath) urv.ctxs urv.ty middlePath ctxs ty topSelectOrientation
  , ty: { ctxs: urv.ctxs, ty: urv.ty }
  }

typePathToNode :: Boolean -> UpPath -> BelowInfo Type Unit -> TypePathRecValue -> Node -> Node
typePathToNode isActive _abovePath _ { typePath: Nil } node = node
typePathToNode isActive abovePath belowInfo typePath innerNode =
  let
    ty = typePath.ty
  in
    recTypePath
      ( { lambda2:
            \termPath md tBind {-Type-} body bodyTy ->
              let
                newBI = BITerm
              in
                termPathToNode isActive abovePath newBI termPath
                  $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                      [ arrangeKid termPath.termPath abovePath (termBindToNode isActive) tBind
                      , arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) ty
                      , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                      ]
        , let4:
            \termPath md tBind tyBinds def {-Type-} body bodyTy ->
              let
                newBI = BITerm
              in
                termPathToNode isActive abovePath newBI termPath
                  $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                      [ arrangeKid termPath.termPath abovePath (termBindToNode isActive) tBind
                      , arrangeKid termPath.termPath abovePath (typeBindListToNode isActive) tyBinds
                      , arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) ty
                      , arrangeKid termPath.termPath abovePath (termToNode isActive) def
                      , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                      ]
        , buffer2: \termPath md def {-Type-} body bodyTy -> (hole' "typePathToNode isActive")
        , tLet3:
            \termPath md tyBind tyBinds {-Type-} body bodyTy ->
              let
                newBI = BITerm
              in
                termPathToNode isActive abovePath newBI termPath
                  $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                      [ arrangeKid termPath.termPath abovePath (typeBindToNode isActive) tyBind
                      , arrangeKid termPath.termPath abovePath (typeBindListToNode isActive) tyBinds
                      , arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) ty
                      , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                      ]
        , ctrParam1: \ctrParamPath md {-Type-} -> (hole' "typePathToNode isActive")
        , typeArg1: \typeArgPath md {-Type-} -> (hole' "typePathToNode isActive")
        , arrow1:
            \typePath md tyOut {-Type-} ->
              let
                newBI = (stepBI (Arrow1 md tyOut.ty) belowInfo)
              in
                typePathToNode isActive abovePath newBI typePath
                  $ arrangeType (makeTypeArgs isActive abovePath newBI typePath)
                      [ arrangeKid typePath.typePath abovePath (\_ _ -> innerNode) ty
                      , arrangeKid typePath.typePath abovePath (typeToNode isActive) tyOut
                      ]
        , arrow2:
            \typePath md tyIn {-Type-} ->
              let
                newBI = (stepBI (Arrow2 md tyIn.ty) belowInfo)
              in
                typePathToNode isActive abovePath newBI typePath
                  $ arrangeType (makeTypeArgs isActive abovePath newBI typePath)
                      [ arrangeKid typePath.typePath abovePath (typeToNode isActive) tyIn
                      , arrangeKid typePath.typePath abovePath (\_ _ -> innerNode) ty
                      ]
        }
      )
      typePath

makeCtrArgs :: Boolean -> CtrPathRecValue -> CtrNodeCursorInfo
makeCtrArgs isActive ctr = {
    isActive
    , makeCursor: \_ -> Nothing
    , makeSelect: \_ -> Nothing
    , ctr: {ctxs: ctr.ctxs, ctr: ctr.ctr}
}

constructorPathToNode :: Boolean -> UpPath -> CtrPathRecValue -> Node -> Node
constructorPathToNode isActive abovePath ctrPath innerNode = (hole' "constructorPathToNode isActive")

makeCtrParamArgs :: Boolean -> CtrParamPathRecValue -> CtrParamNodeCursorInfo
makeCtrParamArgs isActive ctrParam = {
    isActive
    , ctrParam: {ctxs: ctrParam.ctxs, ctrParam: ctrParam.ctrParam}
}

ctrParamPathToNode :: Boolean -> UpPath -> AllContext -> BelowInfo CtrParam Unit -> UpPath -> Node -> Node
ctrParamPathToNode isActive ctxs belowInfo up innerNode = (hole' "ctrParamPathToNode isActive")

makeTypeArgArgs :: Boolean -> TypeArgPathRecValue -> TypeArgNodeCursorInfo
makeTypeArgArgs isActive tyArg = {
    isActive
    , tyArg: {ctxs: tyArg.ctxs, tyArg: tyArg.tyArg}
}

typeArgPathToNode :: Boolean -> UpPath -> AllContext -> BelowInfo TypeArg Unit -> UpPath -> Node -> Node
typeArgPathToNode isActive ctxs belowInfo up innerNode = (hole' "typeArgPathToNode isActive")

typeBindPathToNode :: Boolean -> UpPath -> TypeBindPathRecValue -> Node -> Node
typeBindPathToNode isActive _abovePath { typeBindPath: Nil } innerNode = innerNode
typeBindPathToNode isActive abovePath typeBindPath innerNode =
  let
    tyBind = typeBindPath.tyBind
  in
    recTypeBindPath
      { tLet1:
          \termPath md {-tyBind-} tyBinds def body bodyTy ->
            let
              newBI = BITerm
            in
              termPathToNode isActive abovePath newBI termPath
                $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                    [ arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) tyBind
                    , arrangeKid termPath.termPath abovePath (typeBindListToNode isActive) tyBinds
                    , arrangeKid termPath.termPath abovePath (typeToNode isActive) def
                    , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                    ]
      , data1:
          \termPath md {-tyBind-} tyBinds ctrs body bodyTy ->
            let
              newBI = BITerm
            in
              termPathToNode isActive abovePath BITerm termPath
                $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                    [ arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) tyBind
                    , arrangeKid termPath.termPath abovePath (typeBindListToNode isActive) tyBinds
                    , arrangeKid termPath.termPath abovePath (ctrListToNode isActive) ctrs
                    , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                    ]
      , typeBindListCons1: \listTypeBindPath {-tyBind-} tyBind -> hole' "typeBindPathToNode"
      }
      typeBindPath

{-
typePathToNode isActive :: Boolean -> BelowInfo Type Unit -> TypePathRecValue -> Node -> Node
typePathToNode isActive _ { typePath: Nil } node = node
typePathToNode isActive belowInfo typePath innerNode =
-}
termBindPathToNode :: Boolean -> UpPath -> TermBindPathRecValue -> Node -> Node
termBindPathToNode isActive _abovePath { termBindPath: Nil } innerNode = innerNode
termBindPathToNode isActive abovePath termBindPath innerNode =
  let
    tBind = termBindPath.tBind
  in
    recTermBindPath
      { lambda1:
          \termPath md argTy body bodyTy ->
            let
              newBI = BITerm
            in {- (stepBI (Lambda1 md argTy.ty body.term bodyTy) BITerm) -}
              termPathToNode isActive abovePath newBI termPath
                $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                    [ arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) tBind
                    , arrangeKid termPath.termPath abovePath (typeToNode isActive) argTy
                    , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                    ]
      , let1:
          \termPath md tyBinds def defTy body bodyTy ->
            let
              newBI = BITerm
            in {- (stepBI (Let1 md tyBinds.tyBinds def.term defTy.ty body.term bodyTy) BITerm) -}
              termPathToNode isActive abovePath newBI termPath
                $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                    [ arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) tBind
                    , arrangeKid termPath.termPath abovePath (typeBindListToNode isActive) tyBinds
                    , arrangeKid termPath.termPath abovePath (typeToNode isActive) defTy
                    , arrangeKid termPath.termPath abovePath (termToNode isActive) def
                    , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                    ]
      , constructor1:
          \ctrPath md ctrParams ->
            constructorPathToNode isActive abovePath ctrPath
              $ hole' "termPathBindToNode"
      }
      termBindPath

makeCtrListArgs :: Boolean -> UpPath -> BelowInfo (List Constructor) Unit -> ListCtrPathRecValue -> CtrListNodeCursorInfo
makeCtrListArgs isActive abovePath belowInfo upRecVal =
    { isActive
    , makeCursor: \_ -> Just $ CtrListCursor upRecVal.ctxs (upRecVal.listCtrPath <> abovePath) upRecVal.ctrs
    , makeSelect: \_ ->
        case belowInfo of
            BITerm -> Nothing
            BISelect middlePath ctrs ctxs unit -> Just $ CtrListSelect (upRecVal.listCtrPath <> abovePath) upRecVal.ctxs upRecVal.ctrs middlePath ctxs ctrs topSelectOrientation
    , ctrs: {ctxs: upRecVal.ctxs, ctrs: upRecVal.ctrs}
    }

ctrListPathToNode :: Boolean -> UpPath -> BelowInfo (List Constructor) Unit -> ListCtrPathRecValue -> Node -> Node
ctrListPathToNode isActive abovePath belowInfo {listCtrPath: Nil} innerNode = innerNode
ctrListPathToNode isActive abovePath belowInfo listCtrPath innerNode =
    let ctrs = listCtrPath.ctrs in
    recListCtrPath {
        data3: \termPath md tyBind tyBinds {-ctrs-} body bodyTy ->
            let newBI = BITerm in
            termPathToNode isActive abovePath newBI termPath
                $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                    [ arrangeKid termPath.termPath abovePath (typeBindToNode isActive) tyBind
                    , arrangeKid termPath.termPath abovePath (typeBindListToNode isActive) tyBinds
                    , arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) ctrs
                    , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                    ]
        , ctrListCons2: \listCtrPath ctr {-ctrs-} ->
            let newBI = stepBI (CtrListCons2 ctr.ctr) belowInfo in
            ctrListPathToNode isActive abovePath newBI listCtrPath
                $ arrangeCtrList (makeCtrListArgs isActive abovePath newBI listCtrPath)
                    [ arrangeKid listCtrPath.listCtrPath abovePath (ctrToNode isActive) ctr
                    , arrangeKid listCtrPath.listCtrPath abovePath (ctrListToNode isActive) {ctxs: listCtrPath.ctxs, ctrs}
                    ]
    } listCtrPath

ctrParamListPathToNode :: Boolean -> UpPath -> BelowInfo (List CtrParam) Unit -> ListCtrParamPathRecValue -> Node -> Node
ctrParamListPathToNode isActive abovePath belowInfo {listCtrParamPath: Nil} innerNode = innerNode
ctrParamListPathToNode isActive abovePath belowInfo listCtrParamPath innerNode =
    let ctrParams = listCtrParamPath.ctrParams in
    recListCtrParamPath {
        constructor2: \ctrPath md tBind {-ctrParams-} ->
            let newBI = BITerm in
            constructorPathToNode isActive abovePath ctrPath
                $ arrangeCtr (makeCtrArgs isActive ctrPath)
                    [ arrangeKid ctrPath.ctrPath abovePath (termBindToNode isActive) tBind
                    , arrangeKid ctrPath.ctrPath abovePath (\_ _ -> innerNode) ctrParams
                    ]
        , ctrParamListCons2: \listCtrParamPath ctrParam {-ctrParams-} -> hole
    } listCtrParamPath

typeArgListPathToNode :: Boolean -> UpPath -> BelowInfo (List TypeArg) Unit -> ListTypeArgPathRecValue -> Node -> Node
typeArgListPathToNode isActive abovePath belowInfo listTypeArgPath innerNode = (hole' "typeArgListPathToNode")

typeBindListPathToNode :: Boolean -> UpPath -> BelowInfo (List TypeBind) Unit -> ListTypeBindPathRecValue -> Node -> Node
typeBindListPathToNode isActive abovePath belowInfo typeBindListPath innerNode =
  let
    tyBinds = typeBindListPath.tyBinds
  in
    recListTypeBindPath
      ( { data2: \termPath md tyBind {-tyBinds-} ctrs body bodyTy ->
            let newBI = BITerm in
            termPathToNode isActive abovePath newBI termPath
                $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                    [ arrangeKid termPath.termPath abovePath (typeBindToNode isActive) tyBind
                    , arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) tyBinds
                    , arrangeKid termPath.termPath abovePath (ctrListToNode isActive) ctrs
                    , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                    ]
        , tLet2:
            \termPath md tyBind {-tyBinds-} def body bodyTy ->
              let newBI = BITerm in
                termPathToNode isActive abovePath newBI termPath
                  $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                      [ arrangeKid termPath.termPath abovePath (typeBindToNode isActive) tyBind
                      , arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) tyBinds
                      , arrangeKid termPath.termPath abovePath (typeToNode isActive) def
                      , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                      ]
        , typeBindListCons2: \listTypeBindPath tyBind ->
            let newBI = stepBI (TypeBindListCons2 tyBind.tyBind {--}) belowInfo in
             typeBindListPathToNode isActive abovePath newBI listTypeBindPath
                (hole' "typeBindListPathToNode")
--                $ arrangeTypeBindList
        , let2:
            \termPath md tBind def defTy body bodyTy ->
              let
                newBI = BITerm
              in
                termPathToNode isActive abovePath newBI termPath
                  $ arrangeTerm (makeTermArgs isActive abovePath newBI termPath)
                      [ arrangeKid termPath.termPath abovePath (termBindToNode isActive) tBind
                      , arrangeKid termPath.termPath abovePath (\_ _ -> innerNode) tyBinds
                      , arrangeKid termPath.termPath abovePath (typeToNode isActive) defTy
                      , arrangeKid termPath.termPath abovePath (termToNode isActive) def
                      , arrangeKid termPath.termPath abovePath (termToNode isActive) body
                      ]
        }
      )
      typeBindListPath

{-
Problems currently:
1) *PathToNode are currently not recursive. They should incorporate the teeth rest of the path somehow
2) something something combining teeth with *s causes typing problems?
     remember that when we switch to a different sort we always go to BITerm
3) We need to either 1) draw everything from top down, including paths, or 2) put the MDContext into the State
    TODO TODO TODO ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    The problem with drawing top down is that when detmining the selection, you can't know where is a valid place to
    select to until you traverse UPWARDS from the cursor.
    Another reason to put the metacontext in the state: we actually need it to display queries correctly
-}
