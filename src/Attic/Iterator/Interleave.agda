module Attic.Iterator.Interleave where

open import Attic.Iterator.Base
open import Attic.Iterator.Bound hiding (_⊔_)

open import Level using (Level; _⊔_)

private
  variable
    ℓa ℓs₁ ℓs₂ : Level

  data InterleaveState (S₁ : Set ℓs₁) (S₂ : Set ℓs₂) : Set (ℓs₁ ⊔ ℓs₂) where
    Iter₁ : S₁ → S₂ → InterleaveState S₁ S₂
    Iter₂ : S₁ → S₂ → InterleaveState S₁ S₂
    Done₁ : S₂ → InterleaveState S₁ S₂
    Done₂ : S₁ → InterleaveState S₁ S₂

interleave : {A : Set ℓa} →
             Iterator {_} {ℓs₁} A → Iterator {_} {ℓs₂} A → Iterator A
interleave {A = A} i₁ i₂ = iterator b s0 next
  where
    b = (Iterator.bound i₁ + Iterator.bound i₂)
    S = InterleaveState (Iterator.S₀ i₁) (Iterator.S₀ i₂)
    s0 : S
    s0 = Iter₁ (Iterator.state i₁) (Iterator.state i₂)

    next₁ = Iterator.next i₁
    next₂ = Iterator.next i₂

    next : S → Step A
    next (Iter₁ s1₁ s1₂) with (next₁ s1₁)
    ... | Done = Skip (Done₁ s1₂)
    ... | Skip s2₁ = Skip (Iter₂ s2₁ s1₂)
    ... | Yield s2₁ a₁ = Yield (Iter₂ s2₁ s1₂) a₁
    next (Iter₂ s1₁ s1₂) with (next₂ s1₂)
    ... | Done = Skip (Done₂ s1₁)
    ... | Skip s2₂ = Skip (Iter₁ s1₁ s2₂)
    ... | Yield s2₂ a₂ = Yield (Iter₁ s1₁ s2₂) a₂
    next (Done₁ s1₂) with (next₂ s1₂)
    ... | Done = Done
    ... | Skip s2₂ = Skip (Done₁ s2₂)
    ... | Yield s2₂ a₂ = Yield (Done₁ s2₂) a₂
    next (Done₂ s1₁) with (next₁ s1₁)
    ... | Done = Done
    ... | Skip s2₁ = Skip (Done₂ s2₁)
    ... | Yield s2₁ a₁ = Yield (Done₂ s2₁) a₁
