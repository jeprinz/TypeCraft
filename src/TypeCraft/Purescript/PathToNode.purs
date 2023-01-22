module TypeCraft.Purescript.PathToNode where

import Prelude
import Prim hiding (Type)
import Data.List ((:))
import TypeCraft.Purescript.Context (AllContext)
import TypeCraft.Purescript.Grammar (Constructor, CtrParam(..), DownPath, Term(..), Tooth, Type(..), TypeArg(..), UpPath)
import TypeCraft.Purescript.Node (Node)
import TypeCraft.Purescript.PathRec (TermPathRecValue, TypePathRecValue, recTermPath, recTypePath)
import TypeCraft.Purescript.TermToNode (AboveInfo(..), PreNode, arrangeCtrParam, arrangeKid, arrangeTerm, arrangeType, arrangeTypeArg, termBindToNode, termToNode, typeBindListToNode, typeBindToNode, typeToNode)
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.Util (hole, hole')

data BelowInfo term ty -- NOTE: a possible refactor is to combine term and ty into syn like in TermToNode. On the other hand, I'll probably never bother.
  = BITerm
  | BISelect DownPath term AllContext ty -- middle path, then bottom term. ctx and ty are the type and context of term.

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
stepBI tooth BITerm = BITerm

stepBI tooth (BISelect middle bottom ctxs ty) = BISelect (tooth : middle) bottom ctxs ty

termPathToNode :: Boolean -> BelowInfo Term Type -> TermPathRecValue -> PreNode -> Node
termPathToNode isActive belowInfo term prenode =
  recTermPath
    { app1:
        \up md arg ty1 ty2 ->
          arrangeTerm (args up)
            [ prenode
            , arrangeKid (ai up) (termToNode isActive) arg
            ]
    , app2:
        \up md apl ty1 ty2 ->
          arrangeTerm (args up)
            [ arrangeKid (ai up) (termToNode isActive) apl
            , prenode
            ]
    , lambda3:
        \up md tBind sig ty ->
          arrangeTerm (args up)
            [ arrangeKid (ai up) (termBindToNode isActive) tBind
            , arrangeKid (ai up) (typeToNode isActive) sig
            , prenode
            ]
    , let3:
        \up md tBind tyBinds defTy body bodyTy ->
          arrangeTerm (args up)
            [ arrangeKid (ai up) (termBindToNode isActive) tBind
            , arrangeKid (ai up) (typeBindListToNode isActive) tyBinds
            , prenode
            , arrangeKid (ai up) (typeToNode isActive) defTy
            , arrangeKid (ai up) (termToNode isActive) body
            ]
    , let5:
        \up md tBind tyBinds def defTy bodyTy ->
          arrangeTerm (args up)
            [ arrangeKid (ai up) (termBindToNode isActive) tBind
            , arrangeKid (ai up) (typeBindListToNode isActive) tyBinds
            , arrangeKid (ai up) (termToNode isActive) def
            , arrangeKid (ai up) (typeToNode isActive) defTy
            , prenode
            ]
    , buffer1:
        \up md defTy body bodyTy ->
          arrangeTerm (args up)
            [ prenode
            , arrangeKid (ai up) (typeToNode isActive) defTy
            , arrangeKid (ai up) (termToNode isActive) body
            ]
    , buffer3:
        \up md def defTy bodyTy ->
          arrangeTerm (args up)
            [ arrangeKid (ai up) (termToNode isActive) def
            , arrangeKid (ai up) (typeToNode isActive) defTy
            , prenode
            ]
    , tLet4: hole
    , data4: hole
    , typeBoundary1: hole
    , contextBoundary1: hole
    }
    term
  where
  ai :: forall a r. { termPath :: UpPath | r } -> AboveInfo a
  ai up = AICursor up.termPath

  -- TODO: is this correct? or do i have to reconstruct the term and type at every step?
  args up =
    { isActive
    , aboveInfo: AICursor up.termPath
    , term: { ctxs: term.ctxs, term: term.term, ty: term.ty }
    }

typePathToNode :: Boolean -> BelowInfo Type Unit -> TypePathRecValue -> PreNode -> Node
typePathToNode isActive belowInfo ty prenode =
  recTypePath
    { lambda2:
        \up md tBind body bodyTy ->
          arrangeTerm
            { isActive
            , aboveInfo: (ai _.termPath up)
            , term: { ctxs: ty.ctxs, term: Lambda md tBind.tBind ty.ty body.term bodyTy, ty: ty.ty }
            }
            [ arrangeKid (ai _.termPath up) (termBindToNode isActive) tBind
            , prenode
            , arrangeKid (ai _.termPath up) (termToNode isActive) body
            ]
    , let4:
        \up md tBind tyBinds def body bodyTy ->
          arrangeTerm
            { isActive
            , aboveInfo: (ai _.termPath up)
            , term: { ctxs: ty.ctxs, term: Let md tBind.tBind tyBinds.tyBinds def.term ty.ty body.term bodyTy, ty: bodyTy }
            }
            [ arrangeKid (ai _.termPath up) (termBindToNode isActive) tBind
            , arrangeKid (ai _.termPath up) (typeBindListToNode isActive) tyBinds
            , arrangeKid (ai _.termPath up) (termToNode isActive) def
            , prenode
            , arrangeKid (ai _.termPath up) (termToNode isActive) body
            ]
    , buffer2:
        \up md def body bodyTy ->
          arrangeTerm
            { isActive
            , aboveInfo: (ai _.termPath up)
            , term: { ctxs: ty.ctxs, term: Buffer md def.term ty.ty body.term bodyTy, ty: bodyTy }
            }
            [ arrangeKid (ai _.termPath up) (termToNode isActive) def
            , prenode
            , arrangeKid (ai _.termPath up) (termToNode isActive) body
            ]
    , tLet3:
        \up md tyBind tyBinds body bodyTy ->
          arrangeTerm
            { isActive
            , aboveInfo: (ai _.termPath up)
            , term: { ctxs: ty.ctxs, term: TLet md tyBind.tyBind tyBinds.tyBinds ty.ty body.term bodyTy, ty: bodyTy }
            }
            [ arrangeKid (ai _.termPath up) (typeBindToNode isActive) tyBind
            , arrangeKid (ai _.termPath up) (typeBindListToNode isActive) tyBinds
            , prenode
            , arrangeKid (ai _.termPath up) (termToNode isActive) body
            ]
    , ctrParam1:
        \up md ->
          arrangeCtrParam
            { isActive
            , aboveInfo: (ai _.ctrParamPath up)
            , ctrParam: { ctxs: ty.ctxs, ctrParam: CtrParam md ty.ty }
            }
            [ prenode ]
    , typeArg1:
        \up md ->
          arrangeTypeArg
            { isActive
            , aboveInfo: (ai _.typeArgPath up)
            , tyArg: { ctxs: ty.ctxs, tyArg: TypeArg md ty.ty }
            }
            [ prenode ]
    , arrow1:
        \up md ty2 ->
          arrangeType (args up)
            [ prenode
            , arrangeKid (ai _.typePath up) (typeToNode isActive) ty2
            ]
    , arrow2:
        \up md ty1 ->
          arrangeType (args up)
            [ prenode
            , arrangeKid (ai _.typePath up) (typeToNode isActive) ty1
            ]
    }
    ty
  where
  ai :: forall a r. (r -> UpPath) -> r -> AboveInfo a
  ai f up = AICursor (f up)

  args up =
    { isActive
    , aboveInfo: AICursor up.typePath
    , ty: { ctxs: ty.ctxs, ty: ty.ty }
    }

constructorPathToNode :: Boolean -> AllContext -> BelowInfo Constructor Unit -> UpPath -> Node -> Node
constructorPathToNode isActive ctxs belowInfo up innerNode = (hole' "constructorPathToNode isActive")

ctrParamPathToNode :: Boolean -> AllContext -> BelowInfo CtrParam Unit -> UpPath -> Node -> Node
ctrParamPathToNode isActive ctxs belowInfo up innerNode = (hole' "ctrParamPathToNode isActive")

typeArgPathToNode :: Boolean -> AllContext -> BelowInfo TypeArg Unit -> UpPath -> Node -> Node
typeArgPathToNode isActive ctxs belowInfo up innerNode = (hole' "typeArgPathToNode isActive")

-- typeBindPathToNode :: Boolean -> TypeBindPathRecValue -> Node -> Node
-- typeBindPathToNode isActive { typeBindPath: Nil } innerNode = innerNode
-- typeBindPathToNode isActive typeBindPath innerNode =
--   let
--     tyBind = typeBindPath.tyBind
--   in
--     recTypeBindPath {
--         tLet1 : \termPath md {-tyBind-} tyBinds def body bodyTy ->
--             let newBI = BITerm in
--                 termPathToNode isActive newBI termPath
--                   $ makeTermNode isActive newBI termPath
--                       { tag: TLetNodeTag
--                       , kids: [
--                         innerNode
--                         , typeBindListToNode isActive (AICursor (TLet2 md tyBind {-tyBinds-} def.ty body.term bodyTy : termPath.termPath)) tyBinds
--                         , typeToNode isActive (AICursor (TLet3 md tyBind tyBinds.tyBinds {-def-} body.term bodyTy : termPath.termPath)) def
--                         , termToNode isActive (AICursor (TLet4 md tyBind tyBinds.tyBinds def.ty {-body-} bodyTy : termPath.termPath)) body
--                       ]
--                       }
--         , data1 : \termPath md {-tyBind-} tyBinds ctrs body bodyTy -> hole' "typeBindPathToNode"
--         , typeBindListCons1 : \listTypeBindPath {-tyBind-} tyBind -> hole' "typeBindPathToNode"
--     } typeBindPath
-- {-
-- typePathToNode isActive :: Boolean -> BelowInfo Type Unit -> TypePathRecValue -> Node -> Node
-- typePathToNode isActive _ { typePath: Nil } node = node
-- typePathToNode isActive belowInfo typePath innerNode =
-- -}
-- termBindPathToNode :: Boolean -> TermBindPathRecValue -> Node -> Node
-- termBindPathToNode isActive { termBindPath: Nil } innerNode = innerNode
-- termBindPathToNode isActive termBindPath innerNode =
--   let
--     tBind = termBindPath.tBind
--   in
--     recTermBindPath
--       { lambda1:
--           \termPath md argTy body bodyTy ->
--             let
--               newBI = BITerm
--             in {- (stepBI (Lambda1 md argTy.ty body.term bodyTy) BITerm) -}
--               termPathToNode isActive newBI termPath
--                 $ makeTermNode isActive newBI termPath
--                     { kids:
--                         [ innerNode
--                         , typeToNode isActive (AICursor (Lambda2 md tBind body.term bodyTy : termPath.termPath)) argTy
--                         , termToNode isActive (AICursor (Lambda3 md tBind argTy.ty bodyTy : termPath.termPath)) body
--                         ]
--                     , tag: LambdaNodeTag
--                     }
--       , let1:
--           \termPath md tyBinds def defTy body bodyTy ->
--             let
--               newBI = BITerm
--             in {- (stepBI (Let1 md tyBinds.tyBinds def.term defTy.ty body.term bodyTy) BITerm) -}
--               termPathToNode isActive newBI termPath
--                 $ makeTermNode isActive newBI termPath
--                     { kids:
--                         [ innerNode
--                         , typeBindListToNode isActive (AICursor (Let2 md tBind {-List TypeBind-} def.term defTy.ty body.term bodyTy : termPath.termPath)) tyBinds
--                         , typeToNode isActive (AICursor ((Let4 md tBind tyBinds.tyBinds def.term body.term bodyTy) : termPath.termPath)) defTy
--                         , termToNode isActive (AICursor ((Let3 md tBind tyBinds.tyBinds defTy.ty body.term bodyTy) : termPath.termPath)) def
--                         , termToNode isActive (AICursor ((Let5 md tBind tyBinds.tyBinds def.term defTy.ty bodyTy) : termPath.termPath)) body
--                         ]
--                     , tag: LetNodeTag
--                     }
--       , constructor1:
--           \ctrPath md ctrParams ->
--             constructorPathToNode isActive ctrPath.ctxs (stepBI (Constructor1 md ctrParams.ctrParams) BITerm) ctrPath.ctrPath
--               $ hole' "termPathBindToNode"
--       }
--       termBindPath
-- ctrListPathToNode :: Boolean -> BelowInfo (List Constructor) Unit -> ListCtrPathRecValue -> Node -> Node
-- ctrListPathToNode belowInfo listCtrPath innerNode = (hole' "ctrListPathToNode")
-- ctrParamListPathToNode :: Boolean -> BelowInfo (List CtrParam) Unit -> ListCtrParamPathRecValue -> Node -> Node
-- ctrParamListPathToNode belowInfo listCtrParamPath innerNode = (hole' "ctrParamListPathToNode")
-- typeArgListPathToNode :: Boolean -> BelowInfo (List TypeArg) Unit -> ListTypeArgPathRecValue -> Node -> Node
-- typeArgListPathToNode isActive belowInfo listTypeArgPath innerNode = (hole' "typeArgListPathToNode")
-- typeBindListPathToNode :: Boolean -> BelowInfo (List TypeBind) Unit -> ListTypeBindPathRecValue -> Node -> Node
-- typeBindListPathToNode isActive belowInfo typeBindListPath innerNode =
--   let
--     tyBinds = typeBindListPath.tyBinds
--   in
--     recListTypeBindPath
--       ( { data2: \termPath md tyBind ctrs body bodyTy -> hole' "termBindPathToNode isActive"
--         , tLet2: \termPath md tyBind {-tyBinds-} def body bodyTy ->
--             let newBI = BITerm in
--                 termPathToNode isActive newBI termPath
--                   $ makeTermNode isActive newBI termPath
--                       { tag: TLetNodeTag
--                       , kids: [
--                         typeBindToNode isActive (AICursor (TLet1 md {-tyBind-} tyBinds def.ty body.term bodyTy : termPath.termPath)) tyBind
--                         , innerNode
--                         , typeToNode isActive (AICursor (TLet3 md tyBind.tyBind tyBinds {-def-} body.term bodyTy : termPath.termPath)) def
--                         , termToNode isActive (AICursor (TLet4 md tyBind.tyBind tyBinds def.ty {-body-} bodyTy : termPath.termPath)) body
--                       ]
--                       }
--         , typeBindListCons2: \listTypeBindPath tyBind -> hole' "termBindPathToNode isActive"
--         , let2:
--             \termPath md tBind def defTy body bodyTy ->
--               let
--                 newBI = BITerm
--               in
--                 termPathToNode isActive newBI termPath
--                   $ makeTermNode isActive newBI termPath
--                       { kids:
--                           [ termBindToNode isActive (AICursor (Let1 md {-tbind-} tyBinds def.term defTy.ty body.term bodyTy : termPath.termPath)) tBind
--                           , innerNode
--                           , typeToNode isActive (AICursor (Let4 md tBind.tBind tyBinds def.term {-Type-} body.term bodyTy : termPath.termPath)) defTy
--                           , termToNode isActive (AICursor (Let3 md tBind.tBind tyBinds {-Term-} defTy.ty body.term bodyTy : termPath.termPath)) def
--                           , termToNode isActive (AICursor (Let5 md tBind.tBind tyBinds def.term defTy.ty {-Term-} bodyTy : termPath.termPath)) body
--                           ]
--                       , tag: LetNodeTag
--                       }
--         }
--       )
--       typeBindListPath
-- {-
-- Problems currently:
-- 1) *PathToNode are currently not recursive. They should incorporate the teeth rest of the path somehow
-- 2) something something combining teeth with *s causes typing problems?
--      remember that when we switch to a different sort we always go to BITerm
-- 3) We need to either 1) draw everything from top down, including paths, or 2) put the MDContext into the State
--     TODO TODO TODO ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
--     The problem with drawing top down is that when detmining the selection, you can't know where is a valid place to
--     select to until you traverse UPWARDS from the cursor.
--     Another reason to put the metacontext in the state: we actually need it to display queries correctly
-- -}
