module TypeCraft.Purescript.PathToNode where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Node
import TypeCraft.Purescript.State
import TypeCraft.Purescript.TermRec

import Data.List (List(..), (:))
import Data.Map.Internal (Map(..), empty, lookup, insert, union)
import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.Util (hole)
import TypeCraft.Purescript.TermToNode
import TypeCraft.Purescript.PathRec
import TypeCraft.Purescript.Dentist

data BelowInfo term = BITerm term | BISelect DownPath term -- middle path, then bottom term

stepBI :: forall gsort1 gsort2. Tooth -> BelowInfo gsort1 -> BelowInfo gsort2
--stepBI tooth (BITerm syn) = BITerm (step syn)
--stepBI tooth (BISelect path syn) = BISelect (tooth : path) syn
stepBI = hole
-- TODO: this function is the sketchies thing about my whole setup!!!!!
-- TODO: TODO: think about this!

--bIOnlyCursor :: BelowInfo -> BelowInfo

termPathToNode :: MDContext -> BelowInfo Term -> TermPathRecValue -> UpPath -> Node -> Node
termPathToNode _ _ _ Nil node = node
termPathToNode mdctx belowInfo pathRecVal path@(tooth : teeth) innerNode =
    let partialNode' = recTermPath ({
          let1 : \upRecVal md tbind tbinds {-def-} ty body bodyTy -> hole
        , let3 : \upRecVal md tbind tbinds def defTy {-body-} bodyTy -> hole
        , data3 : \upRecVal md tbind tbinds ctrs {-body-} bodyTy -> hole
    })
    in let partialNode = partialNode' pathRecVal tooth
    in makeNode {
            dat: partialNode.dat
            , kids : [partialNode.kids]
            , getCursor :
                let belowTerm = case belowInfo of
                                     BITerm term -> term
                                     BISelect middlePath term -> combineDownPathTerm middlePath term
                in Just \_ -> initState $ initCursorMode $ TermCursor pathRecVal.kctx pathRecVal.ctx pathRecVal.ty path belowTerm
            , getSelect : hole
            , style : hole
    }

typePathToNode :: MDContext -> BelowInfo Term -> TypePathRecValue -> UpPath -> Node -> Node
typePathToNode _ _ _ Nil node = node
typePathToNode mdctx belowInfo pathRecVal path@(tooth : teeth) innerNode =
    let partialNode = case tooth of
            Let2 md tbind tbinds def {-type-} body bodyTy -> {
                dat : hole
                , kids : hole
            }
            _ -> hole
    in makeNode {
            dat: partialNode.dat
            , kids : [partialNode.kids]
            , getCursor :
                let belowTerm = case belowInfo of
                                     BITerm term -> term
                                     BISelect middlePath term -> combineDownPathTerm middlePath term
                in Just \_ -> initState $ initCursorMode $ TermCursor pathRecVal.kctx pathRecVal.ctx pathRecVal.ty path belowTerm
            , getSelect : hole
            , style : hole
    }
typePathToNode _ _ _ _ _ = hole
