module TypeCraft.Purescript.Grammar where

import Prelude
import Prim hiding (Type)

import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.List (List)
import Data.Maybe (Maybe, maybe)
import Data.Show.Generic (genericShow)
import Data.UUID (UUID, genUUID)
import Effect.Ref (Ref, new, read, write)
import Effect.Unsafe (unsafePerformEffect)
import TypeCraft.Purescript.MD (AppMD, ArrowMD, BufferMD, ContextBoundaryMD, CtrMD, CtrParamMD, GADTMD, HoleMD, LambdaMD, LetMD, THoleMD, TLetMD, TNeuMD, TermBindMD, TypeArgMD, TypeBindMD, TypeBoundaryMD, VarMD, defaultHoleMD, defaultTHoleMD)
import TypeCraft.Purescript.Util (hole')

type TypeHoleID
  = UUID

type TermVarID
  = UUID

freshTermVarID :: Unit -> TermVarID
freshTermVarID _ = unsafePerformEffect genUUID

type TypeVarID
  = UUID

data Type
  = Arrow ArrowMD Type Type
  | THole THoleMD TypeHoleID
  | TNeu TNeuMD TypeVarID (List TypeArg)

freshTHole :: Unit -> Type
freshTHole _ = THole defaultTHoleMD (freshTypeHoleID unit)

data PolyType
  = Forall TypeVarID PolyType
  | PType Type -- doesn't appear in source code. Instead, source code has lists of type parameters.

data TypeArg
  = TypeArg TypeArgMD Type

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
    { varName: maybe "~" identity mb_varName }
    (unsafePerformEffect genUUID)

data TermBind
  = TermBind TermBindMD TermVarID

freshTermBind :: Maybe String -> TermBind
freshTermBind mb_varName =
  TermBind
    { varName: maybe "~" identity mb_varName }
    (unsafePerformEffect genUUID)

data CtrParam
  = CtrParam CtrParamMD Type

data Constructor
  = Constructor CtrMD TermBind (List CtrParam)

--data Kind = KArrow KArrowMD Kind Kind | Type TypeMD
data Kind
  = KArrow Kind
  | Type

data PolyChange
  = CForall TypeVarID PolyChange
  | PPlus TypeVarID PolyChange
  | PMinus TypeVarID PolyChange
  | PChange Change

data Change
  = CArrow Change Change
  | CHole TypeHoleID
  | Replace Type Type
  | Plus Type Change
  | Minus Type Change
  | CNeu TypeVarID (List ChangeParam)

data VarChange
  = VarTypeChange PolyChange
  | VarDelete PolyType
  | VarInsert PolyType

data ChangeParam
  = ChangeParam Change
  | PlusParam Type
  | MinusParam Type

data KindChange
  = KCArrow KindChange
  | KCType
  | KPlus KindChange
  | KMinus KindChange

{-
The following is a list of the grammatical sorts within this editor:
Term, Type, Constructor, CtrParam, TypeArg, TypeBind, TermBind
(List Constructor), (List CtrParam), (List TypeArg) , (List TypeBind)
Each of these has a type of terms and of paths.
The type <thing>Path is the set of possible paths when the cursor is on a <thing>

I'm considering removing the following: Constructor, ConstructorParam, TypeArg
-}
-- Thankfully, I don't think I need Syntax after all
--data Syntax =
--    STerm Term | SType Type | SCtrList (List Constructor) | SCtrParamList (List CtrParam)
--    | TypeArgList (List TypeArg) | TypeBindList (List TypeBind) | SConstructor Constructor
--    | SCtrParam CtrParam | STypeArg TypeArg | STypeBind TypeBind | STermBind TermBind
-- If Term has a constructor named <name>, then here a constructor named <name>n
-- refers to a zipper path piece with a hole as the nth term in that constructor.
-- Can tell what path is up by what type the constructor name came from
-- A <blank>-path is a path whose last tooth has a <blank> missing inside it, in the curly braces
data Tooth
  -- Term
  = App1 AppMD {-Term-} Term Type Type
  | App2 AppMD Term {-Term-} Type Type
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
  -- Type
  | Arrow1 ArrowMD {-Type-} Type
  | Arrow2 ArrowMD Type {-Type-}
  | TNeu1 TNeuMD TypeVarID {-List TypeArg-}
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

type UpPath
  = List Tooth

type DownPath
  = List Tooth

-- TODO: move the below stuff into a separate file
tyInject :: Type -> Change
tyInject (Arrow _ ty1 ty2) = CArrow (tyInject ty1) (tyInject ty2)

tyInject (TNeu _ x args) = CNeu x (map (case _ of TypeArg _ t -> ChangeParam (tyInject t)) args)

tyInject (THole _ id) = CHole id

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
  let
    currentValue = unsafePerformEffect (read uniqueIdCounter)
  in
    let
      _ = unsafePerformEffect (write (currentValue + 1) uniqueIdCounter)
    in
      currentValue

freshTypeHoleID :: Unit -> TypeHoleID
freshTypeHoleID _ = unsafePerformEffect genUUID

freshTypeVarID :: Unit -> TypeVarID
freshTypeVarID _ = unsafePerformEffect genUUID

instance eqType :: Eq Type where
  eq (Arrow _ t1 t2) (Arrow _ t1' t2') = (t1 == t1') && (t2 == t2')
  eq (THole _ x) (THole _ y) = x == y
  eq (TNeu _ x argsx) (TNeu _ y argsy) = x == y && argsx == argsy
  eq _ _ = false

-- BEGIN DERIVATIONS 
-- generated by `src/TypeCraft/Purescript/GrammarGeneric.py`
derive instance genericType :: Generic Type _

instance showType :: Show Type where
  show x = genericShow x

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
