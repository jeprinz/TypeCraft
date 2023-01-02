module TypeCraft.Purescript.StateToNode where

import Prim hiding (Type)
import TypeCraft.Purescript.Node (Node)
import TypeCraft.Purescript.State (State)
import TypeCraft.Purescript.Util (hole)

stateToNode :: State -> Node
stateToNode = hole
