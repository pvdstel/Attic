module Attic.Tactics.Exact where

open import Attic.BasicTactics
open import Attic.GlobalImports
open import Attic.Monad
open import Attic.TCTactics

open import Reflection using (Term)

exactSyntax : Term → Attic ⊤
exactSyntax t = do
  goal ← getGoal
  solveGoal goal t

exactNormalised : ∀ {a} {A : Set a} → A → Attic ⊤
exactNormalised a = do
  quotedA ← quoteNormalisedTC a
  exactSyntax quotedA

exact : ∀ {a} {A : Set a} → A → Attic ⊤
exact a = do
  quotedA ← quoteTC a
  exactSyntax quotedA
