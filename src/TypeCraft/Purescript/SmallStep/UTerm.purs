module TypeCraft.Purescript.SmallStep.UTerm where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.Grammar
import Data.List (List(..), (:))
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

data UTerm = UTerm Label (List UTerm)
data UTooth = UTooth Label (List UTerm) (List UTerm) -- The left and right children
type UPath = List UTooth

termToUTerm :: Term -> UTerm
termToUTerm (App md t1 t2 tyArg tyOut) = UTerm (LApp md tyArg tyOut) ((termToUTerm t1) : (termToUTerm t2) : Nil)
termToUTerm (Lambda md tBind argTy body bodyTy) = UTerm (LLambda md tBind argTy bodyTy) ((termToUTerm body) : Nil)
termToUTerm (Var md x tyArgs) = UTerm (LVar md x tyArgs) (Nil)
termToUTerm (Let md tBind tyBinds def defTy body bodyTy) = UTerm (LLet md tBind tyBinds defTy bodyTy) ((termToUTerm def) : (termToUTerm body) : Nil)
termToUTerm (Data md tyBind tyBinds ctrs body bodyTy) = UTerm (LData md tyBind tyBinds ctrs bodyTy) ((termToUTerm body) : Nil)
termToUTerm (TLet md tyBind tyBinds def body bodyTy) = UTerm (LTLet md tyBind tyBinds def bodyTy) ((termToUTerm body) : Nil)
termToUTerm (TypeBoundary md ch body) = UTerm (LTypeBoundary md ch) ((termToUTerm body) : Nil)
termToUTerm (ContextBoundary md x vc body) = UTerm (LContextBoundary md x vc) ((termToUTerm body) : Nil)
termToUTerm (Hole md) = UTerm (LHole md) (Nil)
termToUTerm (Buffer md buf bufTy body bodyTy) = UTerm (LBuffer md bufTy bodyTy) ((termToUTerm buf) : (termToUTerm body) : Nil)

uTermToTerm :: UTerm -> Term
uTermToTerm (UTerm (LApp md tyArg tyOut) (t1 : t2 : Nil)) = (App md (uTermToTerm t1) (uTermToTerm t2) tyArg tyOut)
uTermToTerm (UTerm (LLambda md tBind argTy bodyTy) (body : Nil)) = (Lambda md tBind argTy (uTermToTerm body) bodyTy)
uTermToTerm (UTerm (LVar md x tyArgs) Nil) = (Var md x tyArgs)
uTermToTerm (UTerm (LLet md tBind tyBinds defTy bodyTy) (def :body : Nil)) = (Let md tBind tyBinds (uTermToTerm def) defTy (uTermToTerm body) bodyTy)
uTermToTerm (UTerm (LTLet md tyBind tyBinds def bodyTy) (body : Nil)) = (TLet md tyBind tyBinds def (uTermToTerm body) bodyTy)
uTermToTerm (UTerm (LTypeBoundary md ch) (body : Nil)) = (TypeBoundary md ch (uTermToTerm body))
uTermToTerm (UTerm (LContextBoundary md x vc) (body : Nil)) = (ContextBoundary md x vc (uTermToTerm body))
uTermToTerm (UTerm (LHole md) Nil) = (Hole md)
uTermToTerm (UTerm (LBuffer md bufTy bodyTy) (buf : body : Nil)) = (Buffer md (uTermToTerm buf) bufTy (uTermToTerm body) bodyTy)
uTermToTerm _ = unsafeThrow "nope"

toothToUTooth :: Tooth -> UTooth
toothToUTooth (App1 md {-Term-} t2 argTy bodyTy) = UTooth (LApp md argTy bodyTy) Nil ((termToUTerm t2) : Nil)
toothToUTooth (App2 md t1 {-Term-} argTy bodyTy) = UTooth (LApp md argTy bodyTy) ((termToUTerm t1) : Nil) Nil
toothToUTooth (Lambda3 md tBind defTy {-Term-} bodyTy) = UTooth (LLambda md tBind defTy bodyTy) Nil Nil
toothToUTooth (Let3 md tBind tyBinds {-Term-} defTy body bodyTy) = UTooth (LLet md tBind tyBinds defTy bodyTy) Nil ((termToUTerm body) : Nil)
toothToUTooth (Let5 md tBind tyBinds def defTy {-Term-} bodyTy) = UTooth (LLet md tBind tyBinds defTy bodyTy) ((termToUTerm def) : Nil) Nil
toothToUTooth (Buffer1 md {-Term-} bufTy body bodyTy) = UTooth (LBuffer md bufTy bodyTy) Nil ((termToUTerm body) : Nil)
toothToUTooth (Buffer3 md buf bufTy {-Term-} bodyTy) = UTooth (LBuffer md bufTy bodyTy) ((termToUTerm buf) : Nil) Nil
toothToUTooth (TypeBoundary1 md ch {-Term-}) = UTooth (LTypeBoundary md ch) Nil Nil
toothToUTooth (ContextBoundary1 md x vc {-Term-}) = UTooth (LContextBoundary md x vc) Nil Nil
toothToUTooth (TLet4 md tyBind tyBinds def {-Term-} bodyTy) = UTooth (LTLet md tyBind tyBinds def bodyTy) Nil Nil
toothToUTooth (Data4 md tyBind tyBinds ctrs {-Term-} bodyTy) = UTooth (LData md tyBind tyBinds ctrs bodyTy) Nil Nil
toothToUTooth _ = unsafeThrow "shouldn't happen toothToUTooth"

uToothToTooth :: UTooth -> Tooth
uToothToTooth (UTooth (LApp md argTy bodyTy) Nil (t2 : Nil)) = (App1 md {-Term-} (uTermToTerm t2) argTy bodyTy)
uToothToTooth (UTooth (LApp md argTy bodyTy) (t1 : Nil) Nil) = (App2 md (uTermToTerm t1) {-Term-} argTy bodyTy)
uToothToTooth (UTooth (LLambda md tBind defTy bodyTy) Nil Nil) = (Lambda3 md tBind defTy {-Term-} bodyTy)
uToothToTooth (UTooth (LLet md tBind tyBinds defTy bodyTy) Nil (body : Nil)) = (Let3 md tBind tyBinds {-Term-} defTy (uTermToTerm body) bodyTy)
uToothToTooth (UTooth (LLet md tBind tyBinds defTy bodyTy) (def : Nil) Nil) = (Let5 md tBind tyBinds (uTermToTerm def) defTy {-Term-} bodyTy)
uToothToTooth (UTooth (LBuffer md bufTy bodyTy) Nil (body : Nil)) = (Buffer1 md {-Term-} bufTy (uTermToTerm body) bodyTy)
uToothToTooth (UTooth (LBuffer md bufTy bodyTy) (buf : Nil) Nil) = (Buffer3 md (uTermToTerm buf) bufTy {-Term-} bodyTy)
uToothToTooth (UTooth (LTypeBoundary md ch) Nil Nil) = (TypeBoundary1 md ch {-Term-})
uToothToTooth (UTooth (LContextBoundary md x vc) Nil Nil) = (ContextBoundary1 md x vc {-Term-})
uToothToTooth (UTooth (LTLet md tyBind tyBinds def bodyTy) Nil Nil) = (TLet4 md tyBind tyBinds def {-Term-} bodyTy)
uToothToTooth (UTooth (LData md tyBind tyBinds ctrs bodyTy) Nil Nil) = (Data4 md tyBind tyBinds ctrs {-Term-} bodyTy)
uToothToTooth _ = unsafeThrow "shouldn't happen uToothToTooth"

------------------------------------------------------------------------------------------

appendUToothUTerm :: UTooth -> UTerm -> UTerm
appendUToothUTerm (UTooth label kids1 kids2) ut = UTerm label (kids1 <> (ut : kids2))

------------------------------------------------------------------------------------------

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