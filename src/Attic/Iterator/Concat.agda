module Attic.Iterator.Concat where

open import Attic.Iterator.Base
open import Attic.Iterator.Bound using (Bound; bounded; unbounded; _+_; _*_)

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level; _⊔_) renaming (suc to sucℓ)

private
  variable
    ℓt ℓs₁ ℓs₂ : Level

  record ConcatState (T : Set ℓt) (S₁ : Set ℓs₁) : Set (ℓt ⊔ ℓs₁ ⊔ (sucℓ ℓs₂)) where
    field
      {S₂} : Set ℓs₂
      s₁ : S₁
      s₂ : S₂
      next₂ : S₂ → Step T {S₂}

  concatBound : {T : Set ℓt} →
                Iterator {ℓs = ℓs₁} (Iterator {ℓs = ℓs₂} T) → Bound
  -- If the outer iterator's bound is unbounded, concat is unbounded.
  concatBound (iterator unbounded _ _) = unbounded
  -- If the outer iterator's bound is bounded, the bound of concat is
  -- Σ_(i = 1)^m (nᵢ + 1), which is the (sum of all n) + m. This is an
  -- implementation detail, see below for more explanation.
  concatBound (iterator mb@(bounded m) s0 next) = innerBoundSum + mb
    where
      sumInner : ℕ → _ → Bound
      sumInner ℕ.zero _ = bounded 0
      sumInner (ℕ.suc m′) s1 with (next s1)
      ... | Done = bounded 0
      ... | Skip s2 = sumInner m′ s2
      ... | Yield s2 inner = (Iterator.bound inner) + (sumInner m′ s2)

      innerBoundSum = sumInner m s0

concat : {T : Set ℓt} →
         Iterator {ℓs = ℓs₁} (Iterator {ℓs = ℓs₂} T) → Iterator T
concat {ℓs₂ = ℓs₂} {T = T} tss = iterator b s0 next′
  where
    b = concatBound tss

    next₁ = Iterator.next tss
    S₁ = Iterator.S₀ tss

    -- The state type of this iterator. The branches of ⊎ represent two cases:
    -- • inj₁ indicates that we are going through the outer iterator, looking
    --   for an inner iterator that we can go over. This operation will mostly
    --   produce Skip operations.
    -- • inj₂ indicates that we are going through the inner iterator, yielding
    --   the output that the inner iterator is producing. This branch of ⊎ has
    --   both the outer iterator's state (which we don't use, but need later
    --   once the inner iterator is exhausted), as well as the inner iterator's
    --   state and its `next` function.
    S = S₁ ⊎ (ConcatState {ℓs₂ = ℓs₂} T S₁)
    s0 : S
    s0 = inj₁ (Iterator.state tss)

    -- This onDone function is executed when the inner iterator is exhausted
    -- (i.e. it produces Done). This function is a mirror of the `inj₁` case of
    -- `next′`. Ideally, that case would immediately call `next′` again, but
    -- this is prevented by the termination checker. Thus, whenever an inner
    -- iterator is exhausted, a Skip is inserted. Although this has no effect
    -- on output of the iterator, it does affect the iterator's bound if it is
    -- finite. If the bound of inner iterator i is nᵢ and the number of inner
    -- iterators is m, the upper bound of the resulting iterator is:
    -- Σ_(i = 1)^m (nᵢ + 1), which is the (sum of all n) + m.
    onDone : S₁ → Step T {S}
    onDone s1₁ with next₁ s1₁
    ... | Done = Done
    ... | Skip s2₁ = Skip (inj₁ s2₁)
    ... | Yield s2₁ ts = Skip (inj₂ cs)
      where
        cs : ConcatState T S₁
        cs = record { s₁ = s2₁ ; s₂ = Iterator.state ts ; next₂ = Iterator.next ts }

    next′ : S → Step T
    -- This branch is executed when no inner iterator has been computed yet.
    next′ (inj₁ s1₁) with next₁ s1₁
    ... | Done = Done
    ... | Skip s2₁ = Skip (inj₁ s2₁)
    ... | Yield s2₁ ts = next′ (inj₂ cs)
      where
        cs : ConcatState T S₁
        cs = record { s₁ = s2₁ ; s₂ = Iterator.state ts ; next₂ = Iterator.next ts }
    next′ (inj₂ cs) with (ConcatState.next₂ cs) (ConcatState.s₂ cs)
    ... | Done = onDone (ConcatState.s₁ cs)
    ... | Skip s2₂ = Skip (inj₂ (record cs { s₂ = s2₂ }))
    ... | Yield s2₂ t = Yield (inj₂ (record cs { s₂ = s2₂ })) t
