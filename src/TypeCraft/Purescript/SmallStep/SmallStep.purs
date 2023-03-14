module TypeCraft.Purescript.SmallStep.SmallStep where

import Prelude
import Prim hiding (Type)
import TypeCraft.Purescript.MD
import TypeCraft.Purescript.Grammar
import Data.List (List(..), (:))
import Data.UUID (UUID)
import Effect.Exception.Unsafe (unsafeThrow)
import TypeCraft.Purescript.SmallStep.UTerm
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested
import Data.Map (Map)
import Data.Map as Map
import Data.List as List
import Data.Traversable (sequence)
import TypeCraft.Purescript.Util (union', lookup')
import Data.Either (Either(..))
import Data.Tuple (fst, snd)
import TypeCraft.Purescript.TypeChangeAlgebra


type LSub = Map LabelHoleID HLabel
data Rule = Rule UTerm (LSub -> Maybe UTerm)

type USub = Map UTermID UTerm

subUTerm :: USub -> UTerm -> UTerm
subUTerm sub (UHole id) = case Map.lookup id sub of
    Nothing -> UHole id
    Just t -> t
subUTerm sub (UTerm label kids) = UTerm label (map (subUTerm sub) kids)

subUTooth :: USub -> UTooth -> UTooth
subUTooth sub (UTooth label kids1 kids2) = UTooth label (map (subUTerm sub) kids1) (map (subUTerm sub) kids2)

subUPath :: USub -> UPath -> UPath
subUPath sub path = map (subUTooth sub) path

unifyELabels :: HLabel -> HLabel -> Maybe LSub
unifyELabels (Right id) l2 = Just $ Map.insert id l2 Map.empty
unifyELabels l1 (Right id) = unifyELabels (Right id) l1
unifyELabels (Left l1) (Left l2) = if l1 == l2 then Just Map.empty else Nothing

unifyUTerm :: UTerm -> UTerm -> Maybe (UTerm /\ USub /\ LSub)
unifyUTerm (UHole id) t = Just (t /\ Map.insert id t Map.empty /\ Map.empty)
unifyUTerm t (UHole id) = unifyUTerm (UHole id) t
unifyUTerm (UTerm label1 kids1) (UTerm label2 kids2) =
    do lsub1 <- unifyELabels label1 label2
       kids' /\ sub /\ lsub <- unifyUTerms kids1 kids2
       pure (UTerm label1 kids' /\ sub /\ (union' lsub1 lsub))

unifyUTerms :: List UTerm -> List UTerm -> Maybe (List UTerm /\ USub /\ LSub)
unifyUTerms Nil Nil = Just (Nil /\ Map.empty /\ Map.empty)
unifyUTerms (t1 : ts1) (t2 : ts2) =
    do t /\ sub /\ lsub1 <- unifyUTerm t1 t2
       let ts1' = map (subUTerm sub) ts1
       let ts2' = map (subUTerm sub) ts2
       ts /\ sub2 /\ lsub2 <- unifyUTerms ts1' ts2'
       pure $ (t : ts) /\ union' sub sub2 /\ union' lsub1 lsub2
unifyUTerms _ _ = unsafeThrow "lengths of lists uneven in unifyUTerms"

applyRuleUTerm :: Rule -> UTerm -> Maybe UTerm
applyRuleUTerm (Rule tIn tOut) t =
    do _ /\ sub /\ lsub <- unifyUTerm tIn t
       term <- tOut lsub
       pure $ subUTerm sub term

recursivelyApplyRuleUTerm :: Rule -> UTerm -> UTerm
recursivelyApplyRuleUTerm rule t =
    let t' = applyRuleUTerm rule t in
    let t'' = case t' of
                Just t -> t
                Nothing -> t in
    case t'' of
        UHole id -> t''
        UTerm label kids -> UTerm label (map (recursivelyApplyRuleUTerm rule) kids)

applyRuleUTooth :: Rule -> UTooth -> UTerm -> Maybe (UTooth /\ UTerm)
applyRuleUTooth (Rule tIn tOut) tooth@(UTooth label kids1 kids2) term =
    do _ /\ sub /\ lsub <- unifyUTerm tIn (appendUToothUTerm tooth term)
       let subTerms = map (subUTerm sub)
       pure $ UTooth label (subTerms kids1) (subTerms kids2) /\ subUTerm sub term

exampleRule :: Rule
-- {lam x : A . e}_C -> lam x : A . {e}_(A -> C)
exampleRule =
    let e = freshUHole unit in
    let l1 = freshLabelHoleID unit in
    let l2 = freshLabelHoleID unit in
    Rule
        (UTerm (Right l1) ((UTerm (Right l2) (e : Nil)) : Nil)) -- {lam x : A . e}

        (\lsub -> case lookup' l1 lsub /\ lookup' l2 lsub of
            (Left (LTypeBoundary md1 (CArrow ch1 ch2))) /\ (Left (LLambda md2 tBind argTy bodyTy)) -> Just $
                UTerm (Left (LLambda md2 tBind (snd (getEndpoints ch1)) (fst (getEndpoints ch2))))
                    (UTerm (Left (LTypeBoundary md1 ch2)) (e : Nil) : Nil)
            _ -> Nothing
        )
