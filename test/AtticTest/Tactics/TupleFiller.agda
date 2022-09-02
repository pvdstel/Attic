-- A tactic that can fill in an existential tuple.

module AtticTest.Tactics.TupleFiller where

open import Attic.BasicTactics
open import Attic.Core using (Goal)
open import Attic.Development
open import Attic.GlobalImports
open import Attic.Iterator using (fromList)
open import Attic.Macro
open import Attic.Monad
open import Attic.TCTactics

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; _∷_; []; [_])
open import Data.Nat
open import Data.Product
import Level
open import Reflection using (Literal; Term; abs)
open import Reflection.Argument
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open Term using (con; def; lam; lit; unknown)

makeTuple : Attic ⊤
makeTuple = do
  (goal , type) ← getGoalAndType
  -- Extract types and right-side name
  def (quote Σ) (_ ∷ _ ∷ arg _ tl ∷ arg _ (lam _ (abs nr tr)) ∷ []) ← reduce type
    where e → do
      quotedE ← quoteNormalisedTC e
      failure $ strErr "Expected a pair, got " ∷ termErr quotedE ∷ []
  -- Generate metavariables
  left ← newUnknownMeta
  leftMeta ← getMeta! left
  right ← newUnknownMeta
  rightMeta ← getMeta! right
  let term : Term
      term = con (quote _,_) (vArg left ∷ vArg right ∷ [])
  solveGoal goal term
  addFocusGoal (record { type = tl ; hole = left ; meta = leftMeta ; context = Goal.context goal })
  addGoal (record { type = tr ; hole = right ; meta = rightMeta ; context = Goal.context goal })

someNaturals = fromList $ 1 ∷ 2 ∷ 3 ∷ []

fillNat′ : Attic ℕ
fillNat′ = do
  -- Branch on the natural number options
  n ← branch someNaturals
  goal ← getGoal
  let term = lit (Literal.nat n)
  -- Fill in
  solveGoal goal term
  return n

fillInRefl : Attic ⊤
fillInRefl = do
  goal ← getGoal
  let term = Term.con (quote refl) []
  solveGoal goal term

fillInTuple : Attic ⊤
fillInTuple = do
  makeTuple
  makeTuple
  n ← fillNat′
  m ← fillNat′
  -- Do some debug logging
  theThing ← quoteNormalisedTC $ n ,′ m
  guard′ [ termErr theThing ] $ m ≡ᵇ 2 * n
  log "TupleFiller" Debug $ errStr "Guard passed"
  fillInRefl

macro fillInTuple′ = asMacro fillInTuple

-- doublePair : Σ[ (x , y) ∈ (ℕ × ℕ) ] y ≡ x * 2
doublePair : Σ (ℕ × ℕ) λ (x , y) → y ≡ x * 2
-- doublePair : ℕ × (1 ≡ 1)
doublePair = {! fillInTuple′  !}
