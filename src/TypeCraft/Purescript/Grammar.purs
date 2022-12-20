module TypeCraft.Purescript.Grammar where

import Data.Generic.Rep (class Generic)
import Data.Eq (class Eq)

import TypeCraft.Purescript.MD (LambdaMD)
import Prelude
import Prim hiding (Type)
import Data.Tuple.Nested
import TypeCraft.Purescript.MD
import Data.List (List)
import Data.Unit (Unit)
import Effect.Exception.Unsafe (unsafeThrow)
import Data.Maybe (Maybe(..))
import Effect.Ref (Ref, new, read, write)
import Effect.Unsafe (unsafePerformEffect)

type TypeHoleID = Int -- figure out unique Ids later!
type TermVarID = Int
type TypeVarID = Int
data Type = Arrow ArrowMD Type Type | THole THoleMD TypeHoleID | TNeu TNeuMD TypeVarID (List TypeArg)
data TypeArg = TypeArg TypeArgMD Type
data Term = App AppMD Term Term Type Type -- The type of the argument, then the type of the output
          | Lambda LambdaMD TermBind Type Term -- NOTE: if we do no-lambda-left-of-app, then the Type here is unecessary!
          | Var VarMD TermVarID (List TypeArg) {-NEEDS WEAKENINGS! (A set of variables by which the context was weakened)-}
          | Let LetMD TermBind (List TypeBind) Term Type Term Type
          | Data GADTMD TypeBind (List TypeBind) (List Constructor) Term Type
          | TLet TLetMD TypeBind (List TypeBind) Type Term Type -- last Type is type of body!
          | TypeBoundary TypeBoundaryMD Change Term -- the change goes from type inside to type outside. That is, getEndpoints gives inside type on left and outside on right.
          | ContextBoundary ContextBoundaryMD TermVarID Change Term
          | Hole HoleMD
          | Buffer BufferMD Term Type Term Type

data TypeBind = TypeBind TypeBindMD TypeVarID
data TermBind = TermBind TermBindMD TermVarID
data CtrParam = CtrParam CtrParamMD Type
data Constructor = Constructor CtrMD TermBind (List CtrParam)

--data Kind = KArrow KArrowMD Kind Kind | Type TypeMD
data Kind = KArrow Kind | Type

data Change = CArrow Change Change | CHole TypeHoleID
     | Replace Type Type
     | Plus Type Change | Minus Type Change
     | CNeu TypeVarID (List ChangeParam)
data ChangeParam = ChangeParam Change | PlusParam Type | MinusParam Type

data KindChange = KCArrow KindChange | KCType
     | KPlus KindChange | KMinus KindChange

-- If Term has a constructor named <name>, then here a constructor named <name>n
-- refers to a zipper path piece with a hole as the nth term in that constructor.
-- Also, an upwards path is always the first argument.
data TermPath =
     Top
     | App1 TermPath AppMD {-Term-} Term Type Type
     | App2 TermPath AppMD Term {-Term-} Type Type
     | Lambda2 TermPath LambdaMD TermBind Type {-Term-}
     | Let1 TermPath LetMD TermBind (List TypeBind) {-Term-} Type Term Type
     | Let3 TermPath LetMD TermBind (List TypeBind) Term Type {-Term-} Type
     | Buffer1 TermPath BufferMD {-Term-} Type Term Type
     | Buffer3 TermPath BufferMD Term Type {-Term-} Type
     | TypeBoundary1 TermPath TypeBoundaryMD Change {-Term-}
     | ContextBoundary1 TermPath ContextBoundaryMD TermVarID Change {-Term-}
     | TLet2 TermPath TLetMD TypeBind (List TypeBind) Type {-Term-} Type
     | Data3 TermPath GADTMD TypeBind (List TypeBind) (List Constructor) {-Term-} Type

{-
The following is a list of the grammatical sorts within this editor:
Term, Type, (List Constructor), (List CtrParam), (List TypeArg) , (List TypeBind)
Constructor, CtrParam, TypeArg, TypeBind, TermBind
Each of these has a type of terms and of paths.
The type <thing>Path is the set of possible paths when the cursor is on a <thing>
-}

-- A path, when the cursor is on a list of constructors
data CtrListPath = Data1 TermPath GADTMD TypeBind (List TypeBind) {-List Constructor-} Term Type
    | CtrListCons2 CtrListPath Constructor {-List Constructor-}
-- A path, when the cursor is on a constructor
data ConstructorPath = CtrListCons1 CtrListPath CtrMD {-List CtrParam-} (List CtrParam)
-- A path, when the cursor is on a list of parameters (within a constructor)
data CtrParamListPath = CtrParamListCons2 CtrParamListPath CtrParam {-List CtrParam-}
    | Constructor1 ConstructorPath {-List CtrParam-}
data CtrParamPath = CtrParamListCons1 CtrParamListPath CtrParam (List CtrParam)

data TypePath = Arrow1 TypePath ArrowMD Type | Arrow2 TypePath ArrowMD Type
     | Let2 TermPath LetMD TermBind (List TypeBind) Term {-Type-} Term Type
     | TNeu1 TypePath TNeuMD (List TypeArg)
     | TNeu2 TypePath TNeuMD (List Change) Int -- The Int is position to insert in the list where the hole is -- May want to go for a more functional representation here
     | Buffer2 TermPath BufferMD Term {-Type-} Term Type
     | Lambda1 TermPath LambdaMD TermBind Term
     | TLet1 TermPath TLetMD TypeBind (List TypeBind) Term Type


-- TODO: move the below stuff into a separate file

tyInject :: Type -> Change
tyInject (Arrow _ ty1 ty2) = CArrow (tyInject ty1) (tyInject ty2)
tyInject (TNeu _ x args) = CNeu x (map (case _ of TypeArg _ t -> ChangeParam (tyInject t)) args)
tyInject (THole _ id) = CHole id
--tyInject (TLambda _ x k ty) = CLambda x (tyInject ty)

-- TODO:
-- freshenVars - freshens bound lambda variables in terms, for copy/paste to work correctly.
-- also need that for term paths!

-- TODO: Place this in a separate file
uniqueIdCounter :: Ref Int
uniqueIdCounter = unsafePerformEffect (new 0)

freshInt :: Unit -> Int
freshInt _ =
    let currentValue = unsafePerformEffect (read uniqueIdCounter) in
    let _ = unsafePerformEffect (write (currentValue + 1) uniqueIdCounter) in
    currentValue

freshTypeHoleID :: Unit -> TypeHoleID
freshTypeHoleID = freshInt

--derive newtype instance eqType :: Eq TypeHoleID

instance eqTypeParam :: Eq TypeArg where
    eq (TypeArg _ t1) (TypeArg _ t2) = t1 == t2

instance eqType :: Eq Type where
    eq (Arrow _ t1 t2) (Arrow _ t1' t2') = (t1 == t1') && (t2 == t2')
    eq (THole _ x) (THole _ y) = x == y
    eq (TNeu _ x argsx) (TNeu _ y argsy) = x == y && argsx == argsy
    eq _ _  = false