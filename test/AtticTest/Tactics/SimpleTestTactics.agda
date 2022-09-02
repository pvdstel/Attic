-- Simple tactics for testing

module AtticTest.Tactics.SimpleTestTactics where

open import Attic.BasicTactics
open import Attic.Development
open import Attic.GlobalImports
open import Attic.Monad
open import Attic.TCTactics

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Reflection using (Term)

open Term using (def; var)

fillNat : ℕ → Attic ⊤
fillNat n = do
  (goal , type) ← getGoalAndType
  (def (quote ℕ) []) ← reduce type
    where
      t →
        error $ strErr "The expected type is not a natural; this tactic cannot be used to solve " ∷ termErr t ∷ []
  nmbr ← quoteTC n
  solveGoal goal nmbr

fillVar0 : Attic ⊤
fillVar0 = do
  goal ← getGoal
  let solution = var 0 []
  solveGoal goal solution

