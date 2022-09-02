-- This is the code used for performance testing.

module AtticTest.Perftest where

open import Data.Nat using (ℕ)
open import Attic.BasicTactics
open import Attic.Macro
open import Attic.Monad
open import Attic.Tactics.Exact
open import Attic.Tactics.Intro

intros100Slow = repeat 100 (try intro)
intros100Fast = repeatTry 100 intro

solution′ = intros100Fast >> (exactSyntax (quoteTerm 5))

macro
  solution = asMacro solution′

-- Paste generated cases below this line

introTest0 : ℕ
introTest0 = solution

introTest1 : ℕ → ℕ
introTest1 = solution

introTest2 : ℕ → ℕ → ℕ
introTest2 = solution

introTest3 : ℕ → ℕ → ℕ → ℕ
introTest3 = solution
