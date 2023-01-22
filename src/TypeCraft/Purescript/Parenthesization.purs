module TypeCraft.Purescript.Parenthesization where

import Data.Tuple.Nested
import Prelude

import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.Grammar (Term(..), Tooth(..))
import TypeCraft.Purescript.Node (Node, NodeTag(..), getNodeTag, setNodeIsParenthesized)
import TypeCraft.Purescript.Util (hole)

-- Example: let case
--letThing :: LetMD -> Node -> Node -> Node -> Node -> Node -> Array Node

parenthesizeChildNode :: NodeTag -> Tooth -> Node -> Node
parenthesizeChildNode tagParent tooth nodeChild =
  flip setNodeIsParenthesized nodeChild case tagParent /\ tooth /\ getNodeTag nodeChild of
    -- Term
    AppNodeTag /\ App1 _ _ _ _ /\ AppNodeTag -> false
    AppNodeTag /\ App1 _ _ _ _ /\ _ -> true
    AppNodeTag /\ App2 _ _ _ _ /\ VarNodeTag -> false
    AppNodeTag /\ App2 _ _ _ _ /\ _ -> true
    LambdaNodeTag /\ _ /\ _ -> false
    LetNodeTag /\ _ /\ _ -> false
    BufferNodeTag /\ _ /\ _ -> false
    TypeBoundaryNodeTag /\ _ /\ _ -> false
    ContextBoundaryNodeTag /\ _ /\ _ -> false
    TLetNodeTag /\ _ /\ _ -> false
    DataNodeTag /\ _ /\ _ -> false
    -- Type
    ArrowNodeTag /\ Arrow1 _ _ /\ ArrowNodeTag -> true
    ArrowNodeTag /\ Arrow1 _ _ /\ _ -> false
    ArrowNodeTag /\ Arrow2 _ _ /\ _ -> false
    TNeuNodeTag /\ _ /\ _ -> false
    -- Constructor
    ConstructorNodeTag /\ _ /\ _ -> false
    -- CtrParam
    CtrParamNodeTag /\ _ /\ _ -> false
    -- TypeArg
    TypeArgNodeTag /\ _ /\ _ -> true
    -- Constructor List
    ConstructorListConsNodeTag /\ _ /\ _ -> false
    -- CtrPaam List
    CtrParamListNilNodeTag /\ _ /\ _ -> false
    -- TypeArg List
    TypeArgListNilNodeTag /\ _ /\ _ -> false
    -- TypeBind List
    TypeBindListNilNodeTag /\ _ /\ _ -> false
    -- malformed
    _ -> unsafeThrow $ "parenthesizeChildNode: malformed childing"
