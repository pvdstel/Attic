module Attic.Tactics.Assumption where

open import Attic.Core
open import Attic.GlobalImports
open import Attic.Iterator using (fromList)
open import Attic.Monad
open import Attic.BasicTactics

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List as List using ([]; boolFilter; map; upTo; zip)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String)
open import Reflection using (Arg; arg)
open import Reflection.Term using (Term; Type; _≟_)
open import Relation.Nullary.Decidable using (isYes)

open Term using (var)

private
  -- Computes whether type B is assignable to type A.
  typeAssignable : Type → Type → Bool
  typeAssignable a b = isYes (a ≟ b)

  -- Computes whether type B in an indexed context element is assignable to type A.
  indexedContextTypeAssignable : Type → ℕ × (String × Arg Type) → Bool
  -- The below comment is the correct implementation, but due to being too strict
  -- has been disabled. This does not change the correctness of Attic, as the check
  -- is later performed by Agda.
  -- indexedContextTypeAssignable a (_ , _ , arg _ b) = typeAssignable a b
  indexedContextTypeAssignable _ _ = true

assumption : Attic ⊤
assumption = do
  goal ← getGoal
  context ← getContext
  let targetType = Goal.type goal
      indices = upTo (List.length context)
      indexedContext = zip indices context
      filteredContext = boolFilter (indexedContextTypeAssignable targetType) indexedContext
      candidateSolutions = map (λ i → (var (proj₁ i) [])) filteredContext
      solutionsIterator = fromList candidateSolutions
  solution ← branch solutionsIterator
  solveGoal goal solution
