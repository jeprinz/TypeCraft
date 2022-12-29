module TypeCraft.Purescript.Node.TermToNode where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.Context
import TypeCraft.Purescript.Grammar
import TypeCraft.Purescript.Node
import TypeCraft.Purescript.State
import TypeCraft.Purescript.Recursor.TermRecursor
import TypeCraft.Purescript.Recursor.TermPathRecursor

import Data.List (List, (:))
import Data.Map.Internal (Map(..), empty, lookup, insert, union)
import Data.Maybe (Maybe(..))
import TypeCraft.Purescript.Util (hole)


data AboveInfo = AICursor DownPath | AISelect DownPath DownPath -- top path, then middle path

stepAI :: Tooth -> AboveInfo -> AboveInfo
stepAI tooth (AICursor path) = AICursor (tooth : path)
stepAI tooth (AISelect topPath middlePath) = AISelect topPath (tooth : middlePath)

aIOnlyCursor :: AboveInfo -> AboveInfo
aIOnlyCursor (AICursor path) = AICursor path
aIOnlyCursor (AISelect topPath middlePath) = AICursor (topPath <> middlePath)

aIGetPath :: AboveInfo -> DownPath
aIGetPath (AICursor path) = path
aIGetPath (AISelect top middle) = top <> middle

--type AboveInfo -- need to track a path for the cursor, and two paths for the selction.
-- also, might consider deriving the cursor path from those two in that case?

toNodeRec :: TermRec (AboveInfo -> Node) (AboveInfo -> Node)
toNodeRec = hole

-- TODO: put TermPath into TermRecValue, and then don't need the TermPath argument here!
-- Problem: what if I really did just have a term, without a TermPath though? I should still be able to recurse over that.
-- So what is the right design here?
termToNode :: TermRecValue -> AboveInfo -> Node
termToNode = recTerm toNodeRec

termPathToNode :: TermPathRecValue -> (AboveInfo -> Node) -> Node
termPathToNode pathRec makeInnerNode = recTermPath toNodeRec pathRec makeInnerNode ?h
