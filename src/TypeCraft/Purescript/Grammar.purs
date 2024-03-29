module TypeCraft.Purescript.Grammar where

import Data.Argonaut.Encode.Generic
import Data.Tuple.Nested
import Prelude
import Prim hiding (Type)

import Data.Argonaut (class DecodeJson, class EncodeJson, Json, JsonDecodeError(..), decodeJson, encodeJson)
import Data.Argonaut.Decode.Generic (genericDecodeJson)
import Data.Argonaut.Encode (toJsonString)
import Data.Either (Either(..))
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.List (List)
import Data.Map (Map(..))
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Ord.Generic (genericCompare)
import Data.Set (Set(..))
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.UUID (UUID, genUUID)
import Data.UUID as UUID
import Effect.Ref (Ref, new, read, write)
import Effect.Unsafe (unsafePerformEffect)
import TypeCraft.Purescript.MD (AppMD, ArrowMD, BufferMD, ContextBoundaryMD, CtrMD, CtrParamMD, GADTMD, HoleMD, LambdaMD, LetMD, THoleMD, TLetMD, TNeuMD, TermBindMD, TypeArgMD, TypeBindMD, TypeBoundaryMD, VarMD, defaultHoleMD, defaultTHoleMD)
import TypeCraft.Purescript.Util (hole')

newtype TypeHoleID = TypeHoleID UUID

maybeEither :: forall e a. e -> Maybe a -> Either e a 
maybeEither e Nothing = Left e 
maybeEither _ (Just a) = Right a


derive instance genericTypeHoleID :: Generic TypeHoleID _
instance encodeJsonTypeHoleID :: EncodeJson TypeHoleID where encodeJson (TypeHoleID uuid) = encodeJson (UUID.toString uuid)
instance dencodeJsonTypeHoleID :: DecodeJson TypeHoleID where decodeJson = map TypeHoleID <<< (maybeEither (TypeMismatch "expected UUID") <<< UUID.parseUUID) <=< decodeJson
instance showTypeHoleID :: Show TypeHoleID  where show (TypeHoleID uuid) = "(TypeHoleID (readUUID \"" <> UUID.toString uuid <> "\"))"
instance eqTypeHoleID :: Eq TypeHoleID  where eq x y = genericEq x y
instance ordTypeHoleID :: Ord TypeHoleID  where compare x y = genericCompare x y

newtype TermVarID = TermVarID UUID
derive instance genericTermVarID :: Generic TermVarID _
instance encodeJsonTermVarID :: EncodeJson TermVarID where encodeJson (TermVarID uuid) = encodeJson (UUID.toString uuid)
instance dencodeJsonTermVarID :: DecodeJson TermVarID where decodeJson = map TermVarID <<< (maybeEither (TypeMismatch "expected UUID") <<< UUID.parseUUID) <=< decodeJson
instance showTermVarID :: Show TermVarID  where show (TermVarID uuid) = "(TermVarID (readUUID \"" <> UUID.toString uuid <> "\"))"
instance eqTermVarID :: Eq TermVarID  where eq x y = genericEq x y
instance ordTermVarID :: Ord TermVarID  where compare x y = genericCompare x y

freshTermVarID :: Unit -> TermVarID
freshTermVarID _ = TermVarID $ unsafePerformEffect genUUID

newtype TypeVarID = TypeVarID UUID
derive instance genericTypeVarID :: Generic TypeVarID _
instance encodeJsonTypeVarID :: EncodeJson TypeVarID where encodeJson (TypeVarID uuid) = encodeJson (UUID.toString uuid)
instance dencodeJsonTypeVarID :: DecodeJson TypeVarID where decodeJson = map TypeVarID <<< (maybeEither (TypeMismatch "expected UUID") <<< UUID.parseUUID) <=< decodeJson
instance showTypeVarID :: Show TypeVarID  where show (TypeVarID uuid) = "(TypeVarID (readUUID \"" <> UUID.toString uuid <> "\"))"
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
  | CHole TypeHoleID (Set TypeVarID) (Map TypeVarID SubChange)
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
  | VarDelete String PolyType
  | VarInsert String PolyType

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
    | TVarDelete String Kind (Maybe (List TypeBind /\ Type))
    | TVarInsert String Kind (Maybe (List TypeBind /\ Type))
type KindChangeCtx = Map TypeVarID TVarChange

data ListTypeArgChange = ListTypeArgChangeNil | ListTypeArgChangeCons Change ListTypeArgChange

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
tyInject (THole _ id w s) = CHole id w (map (\ty -> SubTypeChange (tyInject ty)) s)

data SubChange
  = SubTypeChange Change
  | SubDelete Type
  | SubInsert Type

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

derive instance genericType :: Generic Type _
instance encodeType :: EncodeJson Type where encodeJson x = genericEncodeJson x
instance decodeType :: DecodeJson Type where decodeJson x = genericDecodeJson x
-- instance eqType :: Eq Type where eq x = genericEq x
-- instance showType :: Show Type where show x = genericShow x

derive instance genericPolyType :: Generic PolyType _
instance encodePolyType :: EncodeJson PolyType where encodeJson x = genericEncodeJson x
instance decodePolyType :: DecodeJson PolyType where decodeJson x = genericDecodeJson x
instance eqPolyType :: Eq PolyType where eq x = genericEq x
instance showPolyType :: Show PolyType where show x = genericShow x

derive instance genericTypeArg :: Generic TypeArg _
instance encodeTypeArg :: EncodeJson TypeArg where encodeJson x = genericEncodeJson x
instance decodeTypeArg :: DecodeJson TypeArg where decodeJson x = genericDecodeJson x
instance eqTypeArg :: Eq TypeArg where eq x = genericEq x
instance showTypeArg :: Show TypeArg where show x = genericShow x

derive instance genericTerm :: Generic Term _
instance encodeTerm :: EncodeJson Term where encodeJson x = genericEncodeJson x
instance decodeTerm :: DecodeJson Term where decodeJson x = genericDecodeJson x
instance eqTerm :: Eq Term where eq x = genericEq x
instance showTerm :: Show Term where show x = genericShow x

derive instance genericTypeBind :: Generic TypeBind _
instance encodeTypeBind :: EncodeJson TypeBind where encodeJson x = genericEncodeJson x
instance decodeTypeBind :: DecodeJson TypeBind where decodeJson x = genericDecodeJson x
instance eqTypeBind :: Eq TypeBind where eq x = genericEq x
instance showTypeBind :: Show TypeBind where show x = genericShow x

derive instance genericTermBind :: Generic TermBind _
instance encodeTermBind :: EncodeJson TermBind where encodeJson x = genericEncodeJson x
instance decodeTermBind :: DecodeJson TermBind where decodeJson x = genericDecodeJson x
instance eqTermBind :: Eq TermBind where eq x = genericEq x
instance showTermBind :: Show TermBind where show x = genericShow x

derive instance genericCtrParam :: Generic CtrParam _
instance encodeCtrParam :: EncodeJson CtrParam where encodeJson x = genericEncodeJson x
instance decodeCtrParam :: DecodeJson CtrParam where decodeJson x = genericDecodeJson x
instance eqCtrParam :: Eq CtrParam where eq x = genericEq x
instance showCtrParam :: Show CtrParam where show x = genericShow x

derive instance genericConstructor :: Generic Constructor _
instance encodeConstructor :: EncodeJson Constructor where encodeJson x = genericEncodeJson x
instance decodeConstructor :: DecodeJson Constructor where decodeJson x = genericDecodeJson x
instance eqConstructor :: Eq Constructor where eq x = genericEq x
instance showConstructor :: Show Constructor where show x = genericShow x

derive instance genericKind :: Generic Kind _
instance encodeKind :: EncodeJson Kind where encodeJson x = genericEncodeJson x
instance decodeKind :: DecodeJson Kind where decodeJson x = genericDecodeJson x
instance eqKind :: Eq Kind where eq x = genericEq x
instance showKind :: Show Kind where show x = genericShow x

derive instance genericPolyChange :: Generic PolyChange _
instance encodePolyChange :: EncodeJson PolyChange where encodeJson x = genericEncodeJson x
instance decodePolyChange :: DecodeJson PolyChange where decodeJson x = genericDecodeJson x
instance eqPolyChange :: Eq PolyChange where eq x = genericEq x
instance showPolyChange :: Show PolyChange where show x = genericShow x

derive instance genericChange :: Generic Change _
instance encodeChange :: EncodeJson Change where encodeJson x = genericEncodeJson x
instance decodeChange :: DecodeJson Change where decodeJson x = genericDecodeJson x
-- instance eqChange :: Eq Change where eq x = genericEq x
instance showChange :: Show Change where show x = genericShow x

derive instance genericVarChange :: Generic VarChange _
instance encodeVarChange :: EncodeJson VarChange where encodeJson x = genericEncodeJson x
instance decodeVarChange :: DecodeJson VarChange where decodeJson x = genericDecodeJson x
instance eqVarChange :: Eq VarChange where eq x = genericEq x
instance showVarChange :: Show VarChange where show x = genericShow x

derive instance genericChangeParam :: Generic ChangeParam _
instance encodeChangeParam :: EncodeJson ChangeParam where encodeJson x = genericEncodeJson x
instance decodeChangeParam :: DecodeJson ChangeParam where decodeJson x = genericDecodeJson x
instance eqChangeParam :: Eq ChangeParam where eq x = genericEq x
instance showChangeParam :: Show ChangeParam where show x = genericShow x

derive instance genericKindChange :: Generic KindChange _
instance encodeKindChange :: EncodeJson KindChange where encodeJson x = genericEncodeJson x
instance decodeKindChange :: DecodeJson KindChange where decodeJson x = genericDecodeJson x
instance eqKindChange :: Eq KindChange where eq x = genericEq x
instance showKindChange :: Show KindChange where show x = genericShow x

derive instance genericTooth :: Generic Tooth _
instance encodeTooth :: EncodeJson Tooth where encodeJson x = genericEncodeJson x
instance decodeTooth :: DecodeJson Tooth where decodeJson x = genericDecodeJson x
instance eqTooth :: Eq Tooth where eq x = genericEq x
instance showTooth :: Show Tooth where show x = genericShow x

derive instance genericTypeVar :: Generic TypeVar _
instance encodeTypeVar :: EncodeJson TypeVar where encodeJson x = genericEncodeJson x
instance decodeTypeVar :: DecodeJson TypeVar where decodeJson x = genericDecodeJson x
instance eqTypeVar :: Eq TypeVar where eq x = genericEq x
instance showTypeVar :: Show TypeVar where show x = genericShow x

derive instance genericSubChange :: Generic SubChange _
instance encodeSubChange :: EncodeJson SubChange where encodeJson x = genericEncodeJson x
instance decodeSubChange :: DecodeJson SubChange where decodeJson x = genericDecodeJson x
instance eqSubChange :: Eq SubChange where eq x = genericEq x
instance showSubChange :: Show SubChange where show x = genericShow x

derive instance genericCTypeVar :: Generic CTypeVar _
instance encodeCTypeVar :: EncodeJson CTypeVar where encodeJson x = genericEncodeJson x
instance decodeCTypeVar :: DecodeJson CTypeVar where decodeJson x = genericDecodeJson x
instance eqCTypeVar :: Eq CTypeVar where eq x = genericEq x
instance showCTypeVar :: Show CTypeVar where show x = genericShow x

-- END DERIVATIONS

-- BEGIN MORE INSTANCES, (hand written):

instance showType :: Show Type where
  show = case _ of 
    THole md typeHoleId wkn sub -> "(THole (" <> show md <> ") (" <> show typeHoleId <> ") (Set.fromFoldable " <> show (Set.toUnfoldable wkn :: Array _) <> ") (Map.fromFoldable " <> show (Map.toUnfoldable sub :: Array _) <> "))"
    Arrow md ty1 ty2 -> "(Arrow " <> "(" <> show md <> ") ("<> show ty1 <>") ("<> show ty2 <> "))"
    TNeu md x tys -> "(TNeu (" <> show md <> ") (" <> show x <> ") (" <> show tys <> "))"

instance eqChange :: Eq Change where -- This has to be manually defined for the CHole case to not compare sets and maps? Maybe it would be fine derived generically?
  eq (CArrow t1 t2) (CArrow t1' t2') = (t1 == t1') && (t2 == t2')
  eq (CHole x _ _) (CHole y _ _) = x == y -- TODO: I don't think its necessary to compare the weakens and subs?
  eq (CNeu x argsx) (CNeu y argsy) = x == y && argsx == argsy
  eq (Replace a1 b1) (Replace a2 b2) = a1 == a2 && b1 == b2
  eq (Plus t1 c1) (Plus t2 c2) = t1 == t2 && c1 == c2
  eq (Minus t1 c1) (Minus t2 c2) = t1 == t2 && c1 == c2
  eq _ _ = false

derive instance genericListCtrParamChange :: Generic ListCtrParamChange _

instance showListCtrParamChange :: Show ListCtrParamChange where
    show x = genericShow x

derive instance genericListCtrChange :: Generic ListCtrChange _

instance showListCtrChange :: Show ListCtrChange where
    show x = genericShow x

derive instance genericListTypeBindChange :: Generic ListTypeBindChange _

instance showListTypeBindChange :: Show ListTypeBindChange where
    show x = genericShow x


