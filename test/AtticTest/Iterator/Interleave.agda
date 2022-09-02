module AtticTest.Iterator.Interleave where

open import Attic.Iterator hiding (_∷_)

open import AtticTest.Util

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality

module Simple where
  odds : Iterator ℕ
  odds = iterator unbounded 1 next
    where
      next : ℕ → Step ℕ
      next i = Yield (suc (suc i)) i

  evens : Iterator ℕ
  evens = iterator unbounded 2 next
    where
      next : ℕ → Step ℕ
      next i = Yield (suc (suc i)) i

  _ : (toList odds  5) ≡ 1 ∷ 3 ∷ 5 ∷ 7 ∷ 9 ∷ []
  _ = refl

  _ : (toList evens 5) ≡ 2 ∷ 4 ∷ 6 ∷ 8 ∷ 10 ∷ []
  _ = refl

  nats = interleave odds evens

  _ : (toList nats 10) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []
  _ = refl


module Filtered where
  nats : Iterator ℕ
  nats = iterator unbounded 1 next
    where
      next : ℕ → Step ℕ
      next i = Yield (suc i) i

  _ : toList nats 6 ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []
  _ = refl

  evens = filter isEven nats
  _ : toList evens 10 ≡ 2 ∷ 4 ∷ 6 ∷ 8 ∷ 10 ∷ []
  _ = refl

  odds = filter isOdd nats
  _ : toList odds 10 ≡ 1 ∷ 3 ∷ 5 ∷ 7 ∷ 9 ∷ []
  _ = refl

  remadeNats = interleave odds evens
  
  _ : (toList remadeNats 20) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []
  _ = refl
