module TypeCraft.Purescript.SmallStep.UTerm where

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

{-
The goal is to make an easy to use framework for small step typechange rules.
I will only focus on terms, and assume that stuff for kind changes is already handled (which it is)
-}

newtype LabelHoleID = LabelHoleID UUID

data Label
  = LApp AppMD {-Term-} {-Term-} Type Type -- The type of the argument, then the type of the output
  | LLambda LambdaMD TermBind Type {-Term-} Type -- first Type is arg, second is type of body
  | LVar VarMD TermVarID (List TypeArg)
  | LLet LetMD TermBind (List TypeBind) {-Term-} Type {-Term-} Type
  | LData GADTMD TypeBind (List TypeBind) (List Constructor) {-Term-} Type
  | LTLet TLetMD TypeBind (List TypeBind) Type {-Term-} Type -- last Type is type of body!
  | LTypeBoundary TypeBoundaryMD Change {-Term-} -- the change goes from type inside to type outside. That is, getEndpoints gives inside type on left and outside on right.
  | LContextBoundary ContextBoundaryMD TermVarID VarChange {-Term-} -- the VarChange goes from outside to inside.
  | LHole HoleMD {-NEEDS WEAKENINGS! (A set of variables by which the context was weakened)-}
  | LBuffer BufferMD {-Term-} Type {-Term-} Type

newtype UTermID = UTermID UUID
type HLabel = Either Label LabelHoleID
data UTerm = UTerm HLabel (List UTerm) | UHole UTermID
data UTooth = UTooth HLabel (List UTerm) (List UTerm) -- The left and right children
type UPath = List UTooth

termToUTerm :: Term -> UTerm
termToUTerm (App md t1 t2 tyArg tyOut) = UTerm (Left (LApp md tyArg tyOut)) ((termToUTerm t1) : (termToUTerm t2) : Nil)
termToUTerm (Lambda md tBind argTy body bodyTy) = UTerm (Left (LLambda md tBind argTy bodyTy)) ((termToUTerm body) : Nil)
termToUTerm (Var md x tyArgs) = UTerm (Left (LVar md x tyArgs)) (Nil)
termToUTerm (Let md tBind tyBinds def defTy body bodyTy) = UTerm (Left (LLet md tBind tyBinds defTy bodyTy)) ((termToUTerm def) : (termToUTerm body) : Nil)
termToUTerm (Data md tyBind tyBinds ctrs body bodyTy) = UTerm (Left (LData md tyBind tyBinds ctrs bodyTy)) ((termToUTerm body) : Nil)
termToUTerm (TLet md tyBind tyBinds def body bodyTy) = UTerm (Left (LTLet md tyBind tyBinds def bodyTy)) ((termToUTerm body) : Nil)
termToUTerm (TypeBoundary md ch body) = UTerm (Left (LTypeBoundary md ch)) ((termToUTerm body) : Nil)
termToUTerm (ContextBoundary md x vc body) = UTerm (Left (LContextBoundary md x vc)) ((termToUTerm body) : Nil)
termToUTerm (Hole md) = UTerm (Left (LHole md)) (Nil)
termToUTerm (Buffer md buf bufTy body bodyTy) = UTerm (Left (LBuffer md bufTy bodyTy)) ((termToUTerm buf) : (termToUTerm body) : Nil)

uTermToTerm :: UTerm -> Term
uTermToTerm (UTerm (Left (LApp md tyArg tyOut)) (t1 : t2 : Nil)) = (App md (uTermToTerm t1) (uTermToTerm t2) tyArg tyOut)
uTermToTerm (UTerm (Left (LLambda md tBind argTy bodyTy)) (body : Nil)) = (Lambda md tBind argTy (uTermToTerm body) bodyTy)
uTermToTerm (UTerm (Left (LVar md x tyArgs)) Nil) = (Var md x tyArgs)
uTermToTerm (UTerm (Left (LLet md tBind tyBinds defTy bodyTy)) (def :body : Nil)) = (Let md tBind tyBinds (uTermToTerm def) defTy (uTermToTerm body) bodyTy)
uTermToTerm (UTerm (Left (LTLet md tyBind tyBinds def bodyTy)) (body : Nil)) = (TLet md tyBind tyBinds def (uTermToTerm body) bodyTy)
uTermToTerm (UTerm (Left (LTypeBoundary md ch)) (body : Nil)) = (TypeBoundary md ch (uTermToTerm body))
uTermToTerm (UTerm (Left (LContextBoundary md x vc)) (body : Nil)) = (ContextBoundary md x vc (uTermToTerm body))
uTermToTerm (UTerm (Left (LHole md)) (Nil)) = (Hole md)
uTermToTerm (UTerm (Left (LBuffer md bufTy bodyTy)) (buf : body : Nil)) = (Buffer md (uTermToTerm buf) bufTy (uTermToTerm body) bodyTy)
uTermToTerm _ = unsafeThrow "nope"

toothToUTooth :: Tooth -> UTooth
toothToUTooth (App1 md {-Term-} t2 argTy bodyTy) = UTooth (Left (LApp md argTy bodyTy)) Nil ((termToUTerm t2) : Nil)
toothToUTooth (App2 md t1 {-Term-} argTy bodyTy) = UTooth (Left (LApp md argTy bodyTy)) ((termToUTerm t1) : Nil) Nil
toothToUTooth (Lambda3 md tBind defTy {-Term-} bodyTy) = UTooth (Left (LLambda md tBind defTy bodyTy)) Nil Nil
toothToUTooth (Let3 md tBind tyBinds {-Term-} defTy body bodyTy) = UTooth (Left (LLet md tBind tyBinds defTy bodyTy)) Nil ((termToUTerm body) : Nil)
toothToUTooth (Let5 md tBind tyBinds def defTy {-Term-} bodyTy) = UTooth (Left (LLet md tBind tyBinds defTy bodyTy)) ((termToUTerm def) : Nil) Nil
toothToUTooth (Buffer1 md {-Term-} bufTy body bodyTy) = UTooth (Left (LBuffer md bufTy bodyTy)) Nil ((termToUTerm body) : Nil)
toothToUTooth (Buffer3 md buf bufTy {-Term-} bodyTy) = UTooth (Left (LBuffer md bufTy bodyTy)) ((termToUTerm buf) : Nil) Nil
toothToUTooth (TypeBoundary1 md ch {-Term-}) = UTooth (Left (LTypeBoundary md ch)) Nil Nil
toothToUTooth (ContextBoundary1 md x vc {-Term-}) = UTooth (Left (LContextBoundary md x vc)) Nil Nil
toothToUTooth (TLet4 md tyBind tyBinds def {-Term-} bodyTy) = UTooth (Left (LTLet md tyBind tyBinds def bodyTy)) Nil Nil
toothToUTooth (Data4 md tyBind tyBinds ctrs {-Term-} bodyTy) = UTooth (Left (LData md tyBind tyBinds ctrs bodyTy)) Nil Nil
toothToUTooth _ = unsafeThrow "shouldn't happen toothToUTooth"

uToothToTooth :: UTooth -> Tooth
uToothToTooth (UTooth (Left (LApp md argTy bodyTy)) Nil (t2 : Nil)) = (App1 md {-Term-} (uTermToTerm t2) argTy bodyTy)
uToothToTooth (UTooth (Left (LApp md argTy bodyTy)) (t1 : Nil) Nil) = (App2 md (uTermToTerm t1) {-Term-} argTy bodyTy)
uToothToTooth (UTooth (Left (LLambda md tBind defTy bodyTy)) Nil Nil) = (Lambda3 md tBind defTy {-Term-} bodyTy)
uToothToTooth (UTooth (Left (LLet md tBind tyBinds defTy bodyTy)) Nil (body : Nil)) = (Let3 md tBind tyBinds {-Term-} defTy (uTermToTerm body) bodyTy)
uToothToTooth (UTooth (Left (LLet md tBind tyBinds defTy bodyTy)) (def : Nil) Nil) = (Let5 md tBind tyBinds (uTermToTerm def) defTy {-Term-} bodyTy)
uToothToTooth (UTooth (Left (LBuffer md bufTy bodyTy)) Nil (body : Nil)) = (Buffer1 md {-Term-} bufTy (uTermToTerm body) bodyTy)
uToothToTooth (UTooth (Left (LBuffer md bufTy bodyTy)) (buf : Nil) Nil) = (Buffer3 md (uTermToTerm buf) bufTy {-Term-} bodyTy)
uToothToTooth (UTooth (Left (LTypeBoundary md ch)) Nil Nil) = (TypeBoundary1 md ch {-Term-})
uToothToTooth (UTooth (Left (LContextBoundary md x vc)) Nil Nil) = (ContextBoundary1 md x vc {-Term-})
uToothToTooth (UTooth (Left (LTLet md tyBind tyBinds def bodyTy)) Nil Nil) = (TLet4 md tyBind tyBinds def {-Term-} bodyTy)
uToothToTooth (UTooth (Left (LData md tyBind tyBinds ctrs bodyTy)) Nil Nil) = (Data4 md tyBind tyBinds ctrs {-Term-} bodyTy)
uToothToTooth _ = unsafeThrow "shouldn't happen uToothToTooth"

------------------------------------------------------------------------------------------

appendUToothUTerm :: UTooth -> UTerm -> UTerm
appendUToothUTerm (UTooth label kids1 kids2) ut = UTerm label (kids1 <> (ut : kids2))

------------------------------------------------------------------------------------------

freshUTermID :: Unit -> UTermID
freshUTermID _ = UTermID $ unsafePerformEffect genUUID

freshLabelHoleID :: Unit -> LabelHoleID
freshLabelHoleID _ = LabelHoleID $ unsafePerformEffect genUUID

freshUHole :: Unit -> UTerm
freshUHole _ = UHole (freshUTermID unit)

------------------------------------------------------------------------------------------

derive instance genericLabelHoleID :: Generic LabelHoleID _
instance showLabelHoleID :: Show LabelHoleID  where show (LabelHoleID uuid) = "(LabelHoleID (readUUID \"" <> UUID.toString uuid <> "\"))"
instance eqLabelHoleID :: Eq LabelHoleID  where eq x y = genericEq x y
instance ordLabelHoleID :: Ord LabelHoleID  where compare x y = genericCompare x y

derive instance genericUTermID :: Generic UTermID _
instance showUTermID :: Show UTermID  where show (UTermID uuid) = "(UTermID (readUUID \"" <> UUID.toString uuid <> "\"))"
instance eqUTermID :: Eq UTermID  where eq x y = genericEq x y
instance ordUTermID :: Ord UTermID  where compare x y = genericCompare x y

derive instance genericLabel :: Generic Label _
instance eqLabel :: Eq Label where
  eq x = genericEq x
instance showLabel :: Show Label where
  show x = genericShow x

derive instance genericUTerm :: Generic UTerm _
instance eqUTerm :: Eq UTerm where
  eq x = genericEq x
instance showUTerm :: Show UTerm where
  show x = genericShow x

derive instance genericUTooth :: Generic UTooth _
instance eqUTooth :: Eq UTooth where
  eq x = genericEq x
instance showUTooth :: Show UTooth where
  show x = genericShow x