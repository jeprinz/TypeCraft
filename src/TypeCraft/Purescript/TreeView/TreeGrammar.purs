module TypeCraft.Purescript.TreeView.TreeGrammar where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.Grammar
import Data.List (List(..), (:))
import Data.UUID (UUID, genUUID)
import Data.UUID as UUID
import Effect.Exception.Unsafe (unsafeThrow)
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Ord.Generic (genericCompare)
import Effect.Unsafe (unsafePerformEffect)
import Data.Either (Either(..))

--Term, Type, Constructor, CtrParam, TypeArg, TypeBind, TermBind
--(List Constructor), (List CtrParam), (List TypeArg) , (List TypeBind)
--data GrammaticalSort =
data GrammaticalSort = GSTerm | GSType | GSConstructor | GSCtrParam | GSTypeArg | GSTypeBind | GSTermBind
    | GSCtrList | GSCtrParamList | GSTypeArgList | GSTypeBindList | GSInnerHole

{- But how do I store the type annotations in a generic way? -}

data Label -- =
--  = App {-Term-} {-Term-} Type Type -- The type of the argument, then the type of the output
--  | Lambda TermBind Type Term Type -- first Type is arg, second is type of body
--  | Var VarMD TermVarID (List TypeArg)
--  | Let LetMD TermBind (List TypeBind) Term Type Term Type
--  | Data GADTMD TypeBind (List TypeBind) (List Constructor) Term Type
--  | TLet TLetMD TypeBind (List TypeBind) Type Term Type -- last Type is type of body!
--  | TypeBoundary TypeBoundaryMD Change Term -- the change goes from type inside to type outside. That is, getEndpoints gives inside type on left and outside on right.
--  | ContextBoundary ContextBoundaryMD TermVarID VarChange Term -- the VarChange goes from outside to inside.
--  | Hole HoleMD {-NEEDS WEAKENINGS! (A set of variables by which the context was weakened)-}
--  | Buffer BufferMD Term Type Term Type
----  -- Term
----  LApp | LLambda | LVar | LLet | LData | LTLet | LTypeBoundary | LContextBoundary | LHole | LBuffer
----  -- Type
----  | Arrow ArrowMD Type Type
----  | THole THoleMD TypeHoleID {-Weakenings-} (Set TypeVarID) {-Substitutions-} (Map TypeVarID Type)
----  | TNeu TNeuMD TypeVar (List TypeArg)

data Tree = Tree Label (Array Tree)
--data SubTree = SubTree Tree Boolean -- indentation metadata

--grammar :: GrammaticalSort -> Array SyntaxConstructor
--grammar GSTerm = []
--grammar GSType = []
--grammar GSConstructor = []
--grammar GSCtrParam = []
--grammar GSTypeArg = []
--grammar GSTypeBind = []
--grammar GSTermBind = []
--grammar GSCtrList = []
--grammar GSCtrParamList = []
--grammar GSTypeArgList = []
--grammar GSTypeBindList = []
--grammar GSInnerHole = []

--test :: Tree Int -> Int
--test (Tree n ts) =
--    let a = map ?h ts in
--    ?h