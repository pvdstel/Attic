module Attic.Core where

open import Attic.GlobalImports
open import Attic.Utils.Reflection public using (Binding; Context; TCBinding; TCContext; bindingToTCBinding; contextToTCContext; tcBindingToBinding; tcContextToContext)

open import Agda.Builtin.Reflection using (primMetaEquality)
open import Category.Monad using (RawMonad; RawMonadT)
open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; head)
open import Data.Maybe using (Maybe; _<∣>_)
open import Data.Nat
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec)
open import Reflection using (Arg; Meta; Term; Type)
import Relation.Binary.PropositionalEquality as Eq

record MetaTerm : Set where
  field
    meta : Meta
    context : List (Arg Term)

_meta=_ : MetaTerm → MetaTerm → Bool
_meta=_ a b = primMetaEquality (MetaTerm.meta a) (MetaTerm.meta b)

_meta≠_ : MetaTerm → MetaTerm → Bool
_meta≠_ a b = not (a meta= b)

-- Describes a proof state. A proof state consists of a goal and the context in which we are operating.
record Goal : Set where
  field
    -- The type for which an expression must still be produced.
    type : Type
    -- The term that needs to be unified with the constructed expression.
    hole : Term
    -- The actual meta that represents this hole. Is used to determine uniqueness.
    meta : MetaTerm
    -- The context in which we are constructing an expression.
    context : Context

record Solution : Set where
  field
    goal : Goal
    solution : Term

record ProofState : Set where
  field
    focusedGoal : Maybe Goal
    goals : List Goal
    solutions : List Solution

findGoal : List Goal → MetaTerm → Maybe Goal
findGoal [] meta = nothing
findGoal (goal ∷ goals′) meta with Goal.meta goal meta= meta
... | false = findGoal goals′ meta
... | true = just goal

findSolution : List Solution → MetaTerm → Maybe Solution
findSolution [] meta = nothing
findSolution (solution ∷ solutions′) meta with Goal.meta (Solution.goal solution) meta= meta
... | false = findSolution solutions′ meta
... | true = just solution

getFocusedGoal : ProofState → Maybe Goal
getFocusedGoal state = ProofState.focusedGoal state <∣> head (ProofState.goals state)

getMeta : Term → Maybe MetaTerm
getMeta (Reflection.meta m c) = just (record { meta = m ; context = c })
getMeta _ = nothing
