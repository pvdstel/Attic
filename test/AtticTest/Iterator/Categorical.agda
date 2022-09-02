module AtticTest.Iterator.Categorical where

open import AtticTest.Util using (isEven)

open import Attic.Iterator.Base hiding (_∷_)
open import Attic.Iterator.Categorical
open import Data.List using (List; _∷_; []; reverse)
open import Data.Nat using (ℕ; zero; suc; _*_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality

module BindSimple where
  source = fromList $ 1 ∷ 2 ∷ 3 ∷ []

  with10x = do
    n ← source
    fromList $ n ∷ n * 10 ∷ []

  _ : toList with10x 100 ≡ 1 ∷ 10 ∷ 2 ∷ 20 ∷ 3 ∷ 30 ∷ []
  _ = refl

module Guard where
  testSize = 20

  mkSource : ℕ → List ℕ
  mkSource zero = []
  mkSource n@(suc n') = n ∷ (mkSource n')

  sourceL = reverse $ mkSource testSize -- 1..testSize
  source = fromList sourceL

  evenSource = do
    n ← source
    guard $ isEven n
    return n

  evens = toList evenSource 500
  
  _ : evens ≡ 2 ∷ 4 ∷ 6 ∷ 8 ∷ 10 ∷ 12 ∷ 14 ∷ 16 ∷ 18 ∷ 20 ∷ []
  _ = refl
