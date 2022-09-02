-- Run the macros in the holes in this file to see the expected output
-- on the Agda debug buffer.

module AtticTest.Tactics.BranchTest where

open import Attic.BasicTactics using (guard)
open import Attic.Core
open import Attic.GlobalImports
open import Attic.Development
open import Attic.Macro
open import Attic.Monad
open import Attic.Iterator using (fromList)

open import AtticTest.Util

open import Data.List using (List; _∷_ ; [])
open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.String using (String) renaming (_++_ to _str+_)
import Level

someNaturals = fromList $ 1 ∷ 2 ∷ 3 ∷ []
someStrings = fromList $ "A" ∷ "B" ∷ "C" ∷ []

restTest′ : Attic ⊤ {Level.zero}
restTest′ = do
  n ← branch someStrings
  m ← branch someNaturals
  log "branch-test" Debug $ errStr $ "Got n=\"" str+ n str+ "\" and m=" str+ (showℕ m)
  failure $ errStr ""

macro
  restTest = asMacro restTest′

test : ℕ
test = {! restTest  !}

restTestSkip′ : Attic ⊤ {Level.zero}
restTestSkip′ = do
  n ← branch someStrings
  m ← branch someNaturals
  guard $ isEven m
  log "branch-test-skip" Debug $ errStr $ "Got n=\"" str+ n str+ "\" and m=" str+ (showℕ m)
  failure $ errStr ""

macro
  restTestSkip = asMacro restTestSkip′

testSkip : ℕ
testSkip = {! restTestSkip  !}
