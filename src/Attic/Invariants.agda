module Attic.Invariants where

open import Attic.Core
open import Attic.Development
open import Attic.GlobalImports
open import Attic.Monad

open import Data.Bool using (Bool; true; false; _∨_; not)
open import Data.String using (String) renaming (_++_ to _str+_)
open import Data.List using (List; all; any; boolFilter; length)
open import Data.Nat using (_≡ᵇ_)
open import Level using (Level)

private
  variable
    a b ℓs : Level
    A : Set a
    B : Set b

atticInvariant : String → (A → Bool) → A → Attic B {ℓs} → Attic B {ℓs}
atticInvariant msg pred val cont with pred val
... | false = error $ errStr ("Invariant did not hold: " str+ msg)
... | true = cont

goalExistsAndIsUnique : Goal → List Goal → Attic A {ℓs} → Attic A
goalExistsAndIsUnique goal = atticInvariant
  "The goal exists and is unique."
  let m = Goal.meta goal
  in (λ goals →
    let goalsWithSameMeta = boolFilter (λ g → (Goal.meta g) meta= m) goals
    in length goalsWithSameMeta ≡ᵇ 1)

goalDoesNotExistOrSolved : Goal → ProofState → Attic A {ℓs} → Attic A
goalDoesNotExistOrSolved goal = atticInvariant
  "The goal does not exist or is solved."
  let m = Goal.meta goal
  in (λ state →
    let hasGoalsWithSameMeta = any (λ g → (Goal.meta g) meta= m) (ProofState.goals state)
        hasSolutionWithSameMeta = any (λ s → (Goal.meta (Solution.goal s)) meta= m) (ProofState.solutions state)
    in not (hasGoalsWithSameMeta ∨ hasSolutionWithSameMeta))

goalsDoNotExistOrSolved : List Goal → ProofState → Attic A {ℓs} → Attic A
goalsDoNotExistOrSolved goals = atticInvariant
  "All goals do not exist or are solved."
  λ state →
    let hasGoalsWithSameMeta = λ m → any (λ g → (Goal.meta g) meta= m) (ProofState.goals state)
        hasSolutionWithSameMeta = λ m → any (λ s → (Goal.meta (Solution.goal s)) meta= m) (ProofState.solutions state)
        goalSatisfactory = λ g → let m = Goal.meta g in not (hasGoalsWithSameMeta m ∨ hasSolutionWithSameMeta m)
    in all goalSatisfactory goals
