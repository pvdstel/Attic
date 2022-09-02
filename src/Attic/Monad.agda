module Attic.Monad where

open import Attic.GlobalImports
open import Attic.Core using (MetaTerm; ProofState)
open import Attic.Iterator as Iterator using (Iterator; Iterator′)
import Attic.Iterator.Categorical as Iterator
open import Attic.Utils.Reflection using (fmapTC)

open import Category.Functor using (RawFunctor)
open import Category.Monad using (RawMonad)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; map₁)
open import Data.String using (String)
open import Function using (_$_; _∘_; flip)
open import Level using (Level) renaming (suc to sucℓ; _⊔_ to _⊔ℓ_)
open import Reflection using (ErrorPart; Meta; TC; Term; Type; bindTC; quoteTC; catchTC; typeError; strErr; termErr) renaming (return to returnTC)
open import Reflection.TypeChecking.Monad.Instances

private 
  variable
    ℓ ℓs : Level
    X : Set ℓ

{-# NO_POSITIVITY_CHECK #-}
data Attic (A : Set ℓ) {ℓs : Level} : Set (ℓ ⊔ℓ sucℓ ℓs) where
  -- Represents a value.
  value : A → Attic A
  -- Indicates a failure; the branch of execution will not yield a result.
  failure : List ErrorPart → Attic A
  -- Indicates an error; the computation should terminate immediately.
  error : List ErrorPart → Attic A
  -- Try to execute the first program, and on failure, run the second.
  tryCatch : (try : Attic A {ℓs}) → (catch : Attic A {ℓs}) → Attic A
  -- Represents the computation of a type checker primitive.
  primitiveTC : TC (Attic A {ℓs}) → Attic A
  -- Updates the state of the tactic evaluation engine.
  updateState : (ProofState → Attic A {ℓs} × ProofState) → Attic A
  branch′ : (iter : Iterator {ℓs = ℓs} (Attic A {ℓs})) → Attic A

showAttic : Attic X {ℓs} → String
showAttic (value _) = "value"
showAttic (failure _) = "failure"
showAttic (error _) = "error"
showAttic (tryCatch _ _) = "tryCatch"
showAttic (primitiveTC _) = "primitiveTC"
showAttic (updateState _) = "updateState"
showAttic (branch′ _) = "branch′"

useState : (ProofState → Attic X {ℓs}) → Attic X
useState stateConsumer = updateState λ state → stateConsumer state , state

branch : Iterator {ℓs = ℓs} X → Attic X
branch xs = branch′ (Iterator.map value xs)

branchList : List X → Attic X
branchList as = let iterA = Iterator.fromList as
                    iterAttic = Iterator.map value iterA
                in branch′ iterAttic

try : Attic ⊤ {ℓs} → Attic ⊤ {ℓs}
try a = tryCatch a (value _)

private
  liftTC' : TC (Attic X {ℓs}) → TC X → Attic X
  liftTC' errVal tcAction = primitiveTC $ catchTC
    (fmapTC value tcAction)
    errVal

liftTC! : TC X → Attic X {Level.zero}
liftTC! tcAction = liftTC' fatal tcAction
  where
    fatal : TC (Attic X)
    fatal = bindTC
      (quoteTC tcAction)
      (λ qTCAction →
        typeError $ strErr "Primitive TC action failed: " ∷ termErr qTCAction ∷ [])

unsafeLiftTC! : TC X → Attic X {Level.zero}
unsafeLiftTC! tcAction = primitiveTC (fmapTC value tcAction)

private
  {-# TERMINATING #-}
  liftAttic : {a s1 : Level} {A : Set a} → (s2 : Level) → Attic A {s1} → Attic A {s1 ⊔ℓ s2}
  liftAttic s2 (value a) = value a
  liftAttic s2 (failure s) = failure s
  liftAttic s2 (error s) = error s
  liftAttic s2 (tryCatch t c) = tryCatch (liftAttic s2 t) (liftAttic s2 c)
  liftAttic s2 (primitiveTC tcAction) = primitiveTC (fmapTC (liftAttic s2) tcAction)
  liftAttic s2 (updateState stateConsumer) = updateState (map₁ (liftAttic s2) ∘ stateConsumer)
  liftAttic s2 (branch′ iter) = branch′ (Iterator.mapℓ s2 (liftAttic s2) iter)

{-# TERMINATING #-}
fmap : ∀ {a b s1 s2} {A : Set a} {B : Set b} → (A → B) → Attic A {s1} → Attic B {s1 ⊔ℓ s2}
fmap g (value x) = value (g x)
fmap _ (failure s) = failure s
fmap _ (error s) = error s
fmap {s2 = s2} g (tryCatch t c) = tryCatch (fmap {s2 = s2} g t) (fmap {s2 = s2} g c)
fmap {s2 = s2} g (primitiveTC tcAction) = primitiveTC $ fmapTC (fmap {s2 = s2} g) tcAction
fmap {s2 = s2} g (updateState stateConsumer) = updateState λ state → map₁ (fmap {s2 = s2} g) (stateConsumer state)
fmap {s2 = s2} g (branch′ iter) = branch′ (Iterator.mapℓ s2 (fmap {s2 = s2} g) iter)

{-# TERMINATING #-}
bind : ∀ {a b s1 s2} {A : Set a} {B : Set b} → Attic A {s1} → (A → Attic B {s2}) → Attic B {s1 ⊔ℓ s2}
bind {s1 = s1} (value a) g = liftAttic s1 (g a)
bind (failure s) g = failure s
bind (error s) g = error s
bind (tryCatch t c) g = tryCatch (bind t g) (bind c g)
bind (primitiveTC tcAction) g = primitiveTC $ fmapTC ((flip bind) g) tcAction
bind (updateState stateConsumer) g = updateState λ state → map₁ (flip bind g) (stateConsumer state)
bind {s2 = s2} (branch′ iter) g = branch′ (Iterator.mapℓ s2 (λ x → bind x g) iter)

then : ∀ {a b s1 s2} {A : Set a} {B : Set b} → Attic A {s1} → Attic B {s2} → Attic B {s1 ⊔ℓ s2}
then aa ab = bind aa λ _ → ab

infixl 4 _<$>_
infixl 1 _>>=_ _>>_
_<$>_ = fmap
_>>=_ = bind
_>>_  = then
return : X → Attic X
return x = value {ℓs = Level.zero} x
