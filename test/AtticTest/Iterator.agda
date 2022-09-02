{-# OPTIONS --guardedness #-}

module AtticTest.Iterator where

open import Attic.Iterator hiding (_∷_)

open import Data.Bool using (true; false; _∨_)
open import Data.List as List using (List; []; _∷_; sum; foldr)
open import Data.Nat
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (⌊_⌋)

module Infinite where
  testSize = 10

  nats : Iterator ℕ
  nats = iterator unbounded 1 next
    where
      next : ℕ → Step ℕ
      next i = Yield (suc i) i

  natsTo50 : Iterator ℕ
  natsTo50 = iterator (bounded testSize) 1 next
    where
      next : ℕ → Step ℕ
      next i with ⌊ i ≤? testSize ⌋
      ...       | true  = Yield (suc i) i
      ...       | false = Done

  ubList = toList nats testSize
  bList  = toList natsTo50 (bound′ 0 natsTo50)

  _ : bList ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []
  _ = refl
  _ : ubList ≡ bList
  _ = refl

module Simple where
  _ : toList (single 234) 10 ≡ 234 ∷ []
  _ = refl

  double = _* 2
  list1to10 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []

  iter1to10 = fromList list1to10

  _ : toList iter1to10 (bound′ 0 iter1to10) ≡ list1to10
  _ = refl

  nats : Iterator ℕ
  nats = iterator unbounded 1 next
    where
      next : ℕ → Step ℕ
      next i = Yield (suc i) i

  _ : toList (take 10 nats) 100 ≡ list1to10
  _ = refl

  doubledList1to10 = List.map double list1to10
  doubledIter1to10 = map double iter1to10

  _ : toList doubledIter1to10 100 ≡ doubledList1to10
  _ = refl

  iter7and9 = filter (λ n → ⌊ n ≟ 7 ⌋ ∨ ⌊ n ≟ 9 ⌋) nats
  _ : toList iter7and9 10 ≡ 7 ∷ 9 ∷ []
  _ = refl

module FromListℓzero where
  list1to10 = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []

  iter1to10 = fromList′ list1to10
  _ : toList iter1to10 (bound′ 0 iter1to10) ≡ list1to10
  _ = refl

module Append where
  left  = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  right = 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []
  leftright = left List.++ right

  iterL = fromList left
  iterR = fromList right

  iterLR = iterL ++ iterR

  _ : Iterator.bound iterLR ≡ bounded 10
  _ = refl

  _ : toList iterLR (bound′ 0 iterLR) ≡ leftright
  _ = refl

  _ : toList (iterL ++ empty) 1000 ≡ left
  _ = refl

  _ : toList (empty ++ iterR) 1000 ≡ right
  _ = refl

  _ : toList (iterL ++ empty ++ iterR) 1000 ≡ leftright
  _ = refl

module Nested where
  source = fromList $ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []

  nested : Iterator (Iterator ℕ)
  nested = map single source

  doubleNested : Iterator (Iterator (Iterator ℕ))
  doubleNested = map single nested
