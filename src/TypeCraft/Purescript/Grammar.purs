module TypeCraft.Purescript.Grammar where

import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)

import Data.Either (Either(..))
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.List (List)
import Data.Map (Map(..))
import Data.Map as Map
import Data.Maybe (Maybe, maybe)
import Data.Ord.Generic (genericCompare)
import Data.Set (Set(..))
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.UUID (UUID, genUUID)
import Effect.Ref (Ref, new, read, write)
import Effect.Unsafe (unsafePerformEffect)
import TypeCraft.Purescript.MD (AppMD, ArrowMD, BufferMD, ContextBoundaryMD, CtrMD, CtrParamMD, GADTMD, HoleMD, LambdaMD, LetMD, THoleMD, TLetMD, TNeuMD, TermBindMD, TypeArgMD, TypeBindMD, TypeBoundaryMD, VarMD, defaultHoleMD, defaultTHoleMD)
import TypeCraft.Purescript.Util (hole')

newtype TypeHoleID = TypeHoleID UUID

derive instance genericTypeHoleID :: Generic TypeHoleID _
instance showTypeHoleID :: Show TypeHoleID  where show x = genericShow x 
instance eqTypeHoleID :: Eq TypeHoleID  where eq x y = genericEq x y
instance ordTypeHoleID :: Ord TypeHoleID  where compare x y = genericCompare x y

newtype TermVarID = TermVarID UUID
instance showTermVarID :: Show TermVarID  where show x = genericShow x 
instance eqTermVarID :: Eq TermVarID  where eq x y = genericEq x y
instance ordTermVarID :: Ord TermVarID  where compare x y = genericCompare x y

derive instance genericTermVarID :: Generic TermVarID _

freshTermVarID :: Unit -> TermVarID
freshTermVarID _ = TermVarID $ unsafePerformEffect genUUID

newtype TypeVarID = TypeVarID UUID


derive instance genericTypeVarID :: Generic TypeVarID _
instance showTypeVarID :: Show TypeVarID  where show x = genericShow x 
instance eqTypeVarID :: Eq TypeVarID  where eq x y = genericEq x y
instance ordTypeVarID :: Ord TypeVarID  where compare x y = genericCompare x y


type TypeDefVal = (List TypeBind /\ Type)
data TypeVar = TypeVar TypeVarID | CtxBoundaryTypeVar Kind (Maybe TypeDefVal) String TypeVarID -- TypeVar represents a variable in scope, and CtxBoundaryTypeVar represents a variable inside a context boundary Insert, with the given type.
data CTypeVar = CTypeVar TypeVarID | CCtxBoundaryTypeVar Kind (Maybe TypeDefVal) String TypeVarID
    | PlusCtxBoundaryTypeVar Kind (Maybe TypeDefVal) String TypeVarID
    | MinusCtxBoundaryTypeVar Kind (Maybe TypeDefVal) String TypeVarID

data Type
  = Arrow ArrowMD Type Type
  | THole THoleMD TypeHoleID {-Weakenings-} (Set TypeVarID) {-Substitutions-} (Map TypeVarID Type)
  | TNeu TNeuMD TypeVar (List TypeArg)

freshTHole :: Unit -> Type
freshTHole _ = THole defaultTHoleMD (freshTypeHoleID unit) Set.empty Map.empty

makeTHole :: TypeHoleID -> Type
makeTHole id = THole defaultTHoleMD id Set.empty Map.empty

data PolyType = Forall TypeVarID PolyType | PType Type -- doesn't appear in source code. Instead, source code has lists of type parameters.

data TypeArg = TypeArg TypeArgMD Type

data Term
  = App AppMD Term Term Type Type -- The type of the argument, then the type of the output
  | Lambda LambdaMD TermBind Type Term Type -- first Type is arg, second is type of body
  | Var VarMD TermVarID (List TypeArg)
  | Let LetMD TermBind (List TypeBind) Term Type Term Type
  | Data GADTMD TypeBind (List TypeBind) (List Constructor) Term Type
  | TLet TLetMD TypeBind (List TypeBind) Type Term Type -- last Type is type of body!
  | TypeBoundary TypeBoundaryMD Change Term -- the change goes from type inside to type outside. That is, getEndpoints gives inside type on left and outside on right.
  | ContextBoundary ContextBoundaryMD TermVarID VarChange Term -- the VarChange goes from outside to inside.
  | Hole HoleMD {-NEEDS WEAKENINGS! (A set of variables by which the context was weakened)-}
  | Buffer BufferMD Term Type Term Type

freshHole :: Unit -> Term
freshHole _ = Hole defaultHoleMD

data TypeBind
  = TypeBind TypeBindMD TypeVarID

freshTypeBind :: Maybe String -> TypeBind
freshTypeBind mb_varName =
  TypeBind
    { varName: maybe "" identity mb_varName }
    (TypeVarID $ unsafePerformEffect genUUID)

data TermBind = TermBind TermBindMD TermVarID

freshTermBind :: Maybe String -> TermBind
freshTermBind mb_varName =
  TermBind
    { varName: maybe "" identity mb_varName }
    (TermVarID $ unsafePerformEffect genUUID)

data CtrParam = CtrParam CtrParamMD Type

data Constructor = Constructor CtrMD TermBind (List CtrParam)

data Kind = KArrow Kind | Type

data PolyChange
  = CForall TypeVarID PolyChange
  | PPlus TypeVarID PolyChange
  | PMinus TypeVarID PolyChange
  | PChange Change

data Change
  = CArrow Change Change
  | CHole TypeHoleID (Set TypeVarID) (Map TypeVarID Type)
  | Replace Type Type
  | Plus Type Change
  | Minus Type Change
  | CNeu CTypeVar (List ChangeParam)

{-
The following is a list of the grammatical sorts within this editor:
Term, Type, Constructor, CtrParam, TypeArg, TypeBind, TermBind
(List Constructor), (List CtrParam), (List TypeArg) , (List TypeBind)
Each of these has a type of terms and of paths.
The type <thing>Path is the set of possible paths when the cursor is on a <thing>
-}

-- If Term has a constructor named <name>, then here a constructor named <name>n
-- refers to a zipper path piece with a hole as the nth term in that constructor.
-- Can tell what path is up by what type the constructor name came from
-- A <blank>-path is a path whose last tooth has a <blank> missing inside it, in the curly braces
data Tooth
  -- Term
  = App1 AppMD {-Term-} Term Type Type
  | App2 AppMD Term {-Term-} Type Type
  | Var1 VarMD TermVarID {-List TypeArg-}
  | Lambda1 LambdaMD {-TermBind-} Type Term Type
  | Lambda2 LambdaMD TermBind {-Type-} Term Type
  | Lambda3 LambdaMD TermBind Type {-Term-} Type
  | Let1 LetMD {-TermBind-} (List TypeBind) Term Type Term Type
  | Let2 LetMD TermBind {-List TypeBind-} Term Type Term Type
  | Let3 LetMD TermBind (List TypeBind) {-Term-} Type Term Type
  | Let4 LetMD TermBind (List TypeBind) Term {-Type-} Term Type
  | Let5 LetMD TermBind (List TypeBind) Term Type {-Term-} Type
  | Buffer1 BufferMD {-Term-} Type Term Type
  | Buffer2 BufferMD Term {-Type-} Term Type
  | Buffer3 BufferMD Term Type {-Term-} Type
  | TypeBoundary1 TypeBoundaryMD Change {-Term-}
  | ContextBoundary1 ContextBoundaryMD TermVarID VarChange {-Term-}
  | TLet1 TLetMD {-TypeBind-} (List TypeBind) Type Term Type
  | TLet2 TLetMD TypeBind {-List TypeBind-} Type Term Type
  | TLet3 TLetMD TypeBind (List TypeBind) {-Type-} Term Type
  | TLet4 TLetMD TypeBind (List TypeBind) Type {-Term-} Type
  | Data1 GADTMD {-TypeBind-} (List TypeBind) (List Constructor) Term Type
  | Data2 GADTMD TypeBind {-List TypeBind-} (List Constructor) Term Type
  | Data3 GADTMD TypeBind (List TypeBind) {-List Constructor-} Term Type
  | Data4 GADTMD TypeBind (List TypeBind) (List Constructor) {-Term-} Type
  -- New, for separate cursor position in hole:
  | Hole1 HoleMD
  -- Type
  | Arrow1 ArrowMD {-Type-} Type
  | Arrow2 ArrowMD Type {-Type-}
  | TNeu1 TNeuMD TypeVar {-List TypeArg-}
  -- Constructor
  | Constructor1 CtrMD {-TermBind-} (List CtrParam)
  | Constructor2 CtrMD TermBind {-List CtrParam-}
  -- CtrParam
  | CtrParam1 CtrParamMD {-Type-}
  -- TypeArg
  | TypeArg1 TypeArgMD {-Type-}
  -- Constructor List
  | CtrListCons1 {-Constructor-} (List Constructor)
  | CtrListCons2 Constructor {-List Constructor-}
  -- CtrParam List
  | CtrParamListCons1 {-CtrParam-} (List CtrParam)
  | CtrParamListCons2 CtrParam {-List CtrParam-}
  -- TypeArg List
  | TypeArgListCons1 {-TypeArg-} (List TypeArg)
  | TypeArgListCons2 (TypeArg) {-List TypeArg-}
  -- TypeBind List
  | TypeBindListCons1 {-TypeBind-} (List TypeBind)
  | TypeBindListCons2 (TypeBind) {-List TypeBind-}

type UpPath = List Tooth
type DownPath = List Tooth

-- Some additional Changes grammars. These don't appear in the program, but are used in the TypeChange logic.
data VarChange
  = VarTypeChange PolyChange
  | VarDelete PolyType
  | VarInsert PolyType

data ChangeParam
  = ChangeParam Change
  | PlusParam Type
  | MinusParam Type

data TypeAliasChange
  = TAForall TypeBind TypeAliasChange
  | TAPlus TypeBind TypeAliasChange
  | TAMinus TypeBind TypeAliasChange
  | TAChange Change

data TVarChange = TVarKindChange KindChange (Maybe TypeAliasChange)
    | TVarDelete Kind (Maybe (List TypeBind /\ Type))
    | TVarInsert Kind (Maybe (List TypeBind /\ Type))
type KindChangeCtx = Map TypeVarID TVarChange

data NameChange = NameChangeInsert String | NameChangeDelete String | NameChangeSame String
type MDTypeChangeCtx = Map TypeVarID NameChange
type MDTermChangeCtx = Map TermVarID NameChange

data KindChange
  = KCArrow KindChange
  | KCType
  | KPlus KindChange
  | KMinus KindChange

data ListCtrChange = ListCtrChangeNil | ListCtrChangeCons TermVarID ListCtrParamChange ListCtrChange
    | ListCtrChangePlus Constructor ListCtrChange
    | ListCtrChangeMinus Constructor ListCtrChange

data ListCtrParamChange = ListCtrParamChangeNil | ListCtrParamChangeCons Change ListCtrParamChange
    | ListCtrParamChangePlus CtrParam ListCtrParamChange
    | ListCtrParamChangeMinus CtrParam ListCtrParamChange

data ListTypeBindChange = ListTypeBindChangeCons TypeBind ListTypeBindChange
    | ListTypeBindChangePlus TypeBind ListTypeBindChange
    | ListTypeBindChangeMinus TypeBind ListTypeBindChange
    | ListTypeBindChangeNil

tyVarInject :: TypeVar -> CTypeVar
tyVarInject (TypeVar x) = CTypeVar x
tyVarInject (CtxBoundaryTypeVar pt mtv name x) = CCtxBoundaryTypeVar pt mtv name x

-- TODO: move the below stuff into a separate file
tyInject :: Type -> Change
tyInject (Arrow _ ty1 ty2) = CArrow (tyInject ty1) (tyInject ty2)
tyInject (TNeu _ x args) = CNeu (tyVarInject x) (map (case _ of TypeArg _ t -> ChangeParam (tyInject t)) args)
tyInject (THole _ id w s) = CHole id w s

pTyInject :: PolyType -> PolyChange
pTyInject (Forall x t) = CForall x (pTyInject t)
pTyInject (PType t) = PChange (tyInject t)

--tyInject (TLambda _ x k ty) = CLambda x (tyInject ty)
kindInject :: Kind -> KindChange
kindInject (KArrow k) = KCArrow (kindInject k)
kindInject Type = KCType

-- TODO:
-- freshenVars - freshens bound lambda variables in terms, for copy/paste to work correctly.
-- also need that for term paths!
-- TODO: Place this in a separate file
uniqueIdCounter :: Ref Int
uniqueIdCounter = unsafePerformEffect (new 0)

freshInt :: Unit -> Int
freshInt _ =
  let currentValue = unsafePerformEffect (read uniqueIdCounter)
  in let _ = unsafePerformEffect (write (currentValue + 1) uniqueIdCounter)
  in currentValue

freshTypeHoleID :: Unit -> TypeHoleID
freshTypeHoleID _ = TypeHoleID $ unsafePerformEffect genUUID

freshTypeVarID :: Unit -> TypeVarID
freshTypeVarID _ = TypeVarID $ unsafePerformEffect genUUID

-- Note: its important that the automatically derived Eq is not used for Type, since we don't want to compare metadata.
-- TODO: fix the Eq for PolyType
instance eqType :: Eq Type where
  eq (Arrow _ t1 t2) (Arrow _ t1' t2') = (t1 == t1') && (t2 == t2')
  eq (THole _ x _ _) (THole _ y _ _) = x == y -- TODO: I don't think its necessary to compare the weakens and subs?
  eq (TNeu _ x argsx) (TNeu _ y argsy) = x == y && argsx == argsy
  eq _ _ = false

-- BEGIN DERIVATIONS 
-- generated by `src/TypeCraft/Purescript/GrammarGeneric.py`

derive instance genericNameChange :: Generic NameChange _

instance showNameChange :: Show NameChange where
    show x = genericShow x

instance eqNameChange :: Eq NameChange where
    eq x = genericEq x

derive instance genericTypeVar :: Generic TypeVar _

instance showTypeVar :: Show TypeVar where
    show x = genericShow x

instance eqTypeVar :: Eq TypeVar where
    eq x = genericEq x

derive instance genericCTypeVar :: Generic CTypeVar _

instance showCTypeVar :: Show CTypeVar where
    show x = genericShow x

instance eqCTypeVar :: Eq CTypeVar where
    eq x = genericEq x

derive instance genericType :: Generic Type _

instance showType :: Show Type where show x = genericShow x

derive instance genericPolyType :: Generic PolyType _

instance eqPolyType :: Eq PolyType where
  eq x = genericEq x

instance showPolyType :: Show PolyType where
  show x = genericShow x

derive instance genericTypeArg :: Generic TypeArg _

instance eqTypeArg :: Eq TypeArg where
  eq x = genericEq x

instance showTypeArg :: Show TypeArg where
  show x = genericShow x

derive instance genericTerm :: Generic Term _

instance eqTerm :: Eq Term where
  eq x = genericEq x

instance showTerm :: Show Term where
  show x = genericShow x

derive instance genericTypeBind :: Generic TypeBind _

instance eqTypeBind :: Eq TypeBind where
  eq x = genericEq x

instance showTypeBind :: Show TypeBind where
  show x = genericShow x

derive instance genericTermBind :: Generic TermBind _

instance eqTermBind :: Eq TermBind where
  eq x = genericEq x

instance showTermBind :: Show TermBind where
  show x = genericShow x

derive instance genericCtrParam :: Generic CtrParam _

instance eqCtrParam :: Eq CtrParam where
  eq x = genericEq x

instance showCtrParam :: Show CtrParam where
  show x = genericShow x

derive instance genericConstructor :: Generic Constructor _

instance eqConstructor :: Eq Constructor where
  eq x = genericEq x

instance showConstructor :: Show Constructor where
  show x = genericShow x

derive instance genericKind :: Generic Kind _

instance eqKind :: Eq Kind where
  eq x = genericEq x

instance showKind :: Show Kind where
  show x = genericShow x

derive instance genericPolyChange :: Generic PolyChange _

instance eqPolyChange :: Eq PolyChange where
  eq x = genericEq x

instance showPolyChange :: Show PolyChange where
  show x = genericShow x

derive instance genericChange :: Generic Change _

instance eqChange :: Eq Change where
  eq x = genericEq x

instance showChange :: Show Change where
  show x = genericShow x

derive instance genericVarChange :: Generic VarChange _

instance eqVarChange :: Eq VarChange where
  eq x = genericEq x

instance showVarChange :: Show VarChange where
  show x = genericShow x

derive instance genericTVarChange :: Generic TVarChange _

instance eqTVarChange :: Eq TVarChange where
  eq x = genericEq x

instance showTVarChange :: Show TVarChange where
  show x = genericShow x

derive instance genericTypeAliasChange :: Generic TypeAliasChange _

instance eqTypeAliasChange :: Eq TypeAliasChange where
  eq x = genericEq x

instance showTypeAliasChange :: Show TypeAliasChange where
  show x = genericShow x

derive instance genericChangeParam :: Generic ChangeParam _

instance eqChangeParam :: Eq ChangeParam where
  eq x = genericEq x

instance showChangeParam :: Show ChangeParam where
  show x = genericShow x

derive instance genericKindChange :: Generic KindChange _

instance eqKindChange :: Eq KindChange where
  eq x = genericEq x

instance showKindChange :: Show KindChange where
  show x = genericShow x

derive instance genericTooth :: Generic Tooth _

instance eqTooth :: Eq Tooth where
  eq x = genericEq x

instance showTooth :: Show Tooth where
  show x = genericShow x

-- END DERIVATIONS

-- BEGIN MORE DERIVATIONS, (hand written):

derive instance genericListCtrParamChange :: Generic ListCtrParamChange _

instance showListCtrParamChange :: Show ListCtrParamChange where
    show x = genericShow x

derive instance genericListCtrChange :: Generic ListCtrChange _

instance showListCtrChange :: Show ListCtrChange where
    show x = genericShow x

derive instance genericListTypeBindChange :: Generic ListTypeBindChange _

instance showListTypeBindChange :: Show ListTypeBindChange where
    show x = genericShow x


