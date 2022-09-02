{-# OPTIONS --keep-pattern-variables #-}

module Attic.Tactics.Destruct where

open import Attic.BasicTactics
open import Attic.Core
open import Attic.Development
open import Attic.GlobalImports
open import Attic.Macro
open import Attic.Monad
open import Attic.TCTactics

open import Data.List as List using (List; _++_; _∷_; []; [_]; map; zip; zipWith)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_; map₁; proj₁)
open import Data.String using (String)
open import Level using (Level)
open import Reflection using (Clause; Name; Pattern; Term; Type; arg; vArg)

open Clause
open Pattern using (con; var)
open Term using (def; pat-lam; unknown)

case─match_of_ : ∀{a b} {A : Set a} {B : Set b} → A → (A → B) → B
case─match x of f = f x
{-# NOINLINE case─match_of_ #-}

private
  noDataOrRecord : ∀ {a} {A : Set a} → Term → Attic A {Level.zero}
  noDataOrRecord t = failure $ strErr "The type is not a data type or record: " ∷ termErr t ∷ []

  getConstructorNames : Type → Attic (List Name) {Level.zero}
  getConstructorNames t = do
    def tName tArgs ← reduce t
      where
        _ → noDataOrRecord t
    getDefinition tName >>= λ { 
        (Reflection.data-type pars cs) → return cs
      ; (Reflection.record-type c fs) → return [ c ]
      ; _ → noDataOrRecord t
      }

  getConstructorTypes : List Name → Attic (List Type) {Level.zero}
  getConstructorTypes [] = return []
  getConstructorTypes (n ∷ ns) = do
    t ← getType n
    rest ← getConstructorTypes ns
    return (t ∷ rest)
  
  unfoldConstructorType : Type → (Context × Type)
  unfoldConstructorType (Reflection.pi a (Reflection.abs argN tT)) =
    map₁ ((argN , a) ∷_) (unfoldConstructorType tT)
  unfoldConstructorType t = [] , t

  makePatterns : List Name → List (Context × Type) → List Pattern
  makePatterns (name ∷ names′) ((params , _) ∷ telescopes′) =
    -- con (quote ⌊_⌋) (vArg (con name conVars) ∷ []) ∷ rec
    (con name conVars) ∷ rec
    where
      varIndices = List.downFrom (List.length params)
      conVars = zipWith
        (λ { (_ , arg info _) i → arg info (var i) })
        params
        varIndices
      rec = makePatterns names′ telescopes′
  makePatterns _ _ = []

  makeClauses : Context → List (Context × Type) → List Pattern → Attic (List Clause) {Level.zero}
  makeClauses baseTel (tel ∷ telescopes′) (pat ∷ patterns′) = do
    newHole ← newUnknownMetaContext (baseTel ++ (proj₁ tel))
    rec ← makeClauses baseTel telescopes′ patterns′
    let result = clause (proj₁ tel) (vArg pat ∷ []) newHole ∷ rec
    return result
  makeClauses _ _ _ = return []

  makeGoals : Context → (goalType : Type) → List Clause → Attic (List Goal) {Level.zero}
  makeGoals baseTel goalType ((clause tel _ term) ∷ clauses′) = do
    meta ← getMeta! term
    rec ← makeGoals baseTel goalType clauses′
    let goal = record { type = goalType
                      ; hole = term
                      ; meta = meta
                      ; context = baseTel ++ tel
                      }
    return (goal ∷ rec)
  makeGoals _ _ ((absurd-clause _ _) ∷ _) = error (errStr "destruct/makeGoals/absurd-clause: impossible")
  makeGoals _ _ [] = return []

destruct : Term → Type → Attic ⊤
destruct term type = do
  goal ← getGoal
  names ← getConstructorNames type
  types ← getConstructorTypes names
  let context = Goal.context goal
      telescopes = map unfoldConstructorType types
      patterns   = makePatterns names telescopes
  clauses ← makeClauses context telescopes patterns
  newGoals ← makeGoals context (Goal.type goal) clauses

  let caseLambda = pat-lam clauses []
      solution   = def (quote case─match_of_) (vArg term ∷ vArg caseLambda ∷ [])

  solveGoal goal solution
  addFocusGoals newGoals

destructIndex : ℕ → Attic ⊤
destructIndex i = do
  (_ , (arg _ t)) ← getContextIndex i
  destruct (Term.var i []) t

destructName : String → Attic ⊤
destructName n = do
  (_ , (arg _ t)) , i ← getContextName n
  destruct (Term.var i []) t
