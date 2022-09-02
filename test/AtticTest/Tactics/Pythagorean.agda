module AtticTest.Tactics.Pythagorean where

open import Attic.Iterator hiding (_∷_)
import Attic.Iterator.Categorical

open import Data.Bool using (true)
open import Data.List
open import Data.Maybe using (just)
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)
open import Reflection hiding (_>>=_; _>>_)

doublePair : Σ[ (x , y) ∈ (ℕ × ℕ) ] y ≡ x * 2
doublePair = (1 , 2) , refl

nats : Iterator ℕ
nats = iterator unbounded 1 next
  where
    next : ℕ → Step ℕ
    next i = Yield (suc i) i

pyTriples =
  do
    (a , b , c) ← cartesian₃ nats nats nats
    guard $ (a * a) + (b * b) ≡ᵇ (c * c)
    single (a , (b , c))
  where
    _>>=_ = Attic.Iterator.Categorical._>>=_
    _>>_  = Attic.Iterator.Categorical._>>_

firstTriple = first pyTriples 189

_ : firstTriple ≡ just (3 , (4 , 5))
_ = refl

makeTriple : ℕ → ℕ → ℕ → Term
makeTriple a b c =
  con (quote _,_) (argA ∷ innerArg ∷ [])
  where
    argA = arg (arg-info visible (modality relevant quantity-ω)) (lit (nat a))
    argB = arg (arg-info visible (modality relevant quantity-ω)) (lit (nat b))
    argC = arg (arg-info visible (modality relevant quantity-ω)) (lit (nat c))

    inner = con (quote _,_) (argB ∷ argC ∷ [])
    innerArg = arg (arg-info visible (modality relevant quantity-ω)) inner

macro
  pyTriple : Term → TC ⊤
  pyTriple hole =
    do
      just t@(a , (b , c)) ← return firstTriple
        where _ → typeError [ strErr "No triple was found." ]
      tsyntax ← quoteTC t
      unify hole tsyntax
    where
      _>>=_ = Reflection._>>=_
      _>>_  = Reflection._>>_

tripleExists : Σ (ℕ × ℕ × ℕ) (λ (x , y , z) → x * x + y * y ≡ z * z)
tripleExists = pyTriple , refl

fancySyntaxTripleExists : Σ[ (x , y , z) ∈ (ℕ × ℕ × ℕ) ] x * x + y * y ≡ z * z
fancySyntaxTripleExists = (3 , 4 , 5) , refl
