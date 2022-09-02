module Attic.BasicTactics where

open import Attic.Core
open import Attic.Development
open import Attic.GlobalImports
open import Attic.Invariants
open import Attic.Monad
open import Attic.TCTactics

open import Agda.Builtin.String using (primStringEquality)
open import Data.Bool using (Bool; true; false; not)
open import Data.List as List using (List; []; [_]; _∷_; _++_; boolFilter; all; any)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Maybe using (map; maybe′; is-just)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _str+_)
open import Function using (id; case_of_)
open import Level using (Level)
open import Reflection using (Term; Type)

private
  noGoalMessage = "No focused goal was found."

  -- If a focused goal exists, transform it using the function `f` and return it.
  -- If it does not exist, produce a fatal failure message.
  withFocusedGoal : {A : Set} → (Goal → A) → Attic A {Level.zero}
  withFocusedGoal f = useState λ state → maybe′ (return ∘ f) (failure $ errStr noGoalMessage) (getFocusedGoal state)

------ Proof abstraction tactics ------

getMeta! : Term → Attic MetaTerm {Level.zero}
getMeta! (Reflection.meta m c) = value (record { meta = m ; context = c })
getMeta! term = error $ strErr "Expected a meta term, but got " ∷ termErr term ∷ []

getGoalType : Attic Type
getGoalType = withFocusedGoal Goal.type

getContext : Attic Context
getContext = withFocusedGoal Goal.context

getGoal : Attic Goal
getGoal = withFocusedGoal id

getGoalAndType : Attic (Goal × Type)
getGoalAndType = withFocusedGoal λ goal → goal , (Goal.type goal)

getGoal′ : Attic (Maybe Goal) {Level.zero}
getGoal′ = useState λ state → return (getFocusedGoal state)

------ Debug helper tactics ------

debugLogGoals : Attic ⊤ {Level.zero}
debugLogGoals = do
  goals ← useState λ state → return (ProofState.goals state)
  quotedGoals ← quoteNormalisedTC goals
  log "basic" Debug $ strErr "Goals: " ∷ termErr quotedGoals ∷ []

debugLogSolutions : Attic ⊤ {Level.zero}
debugLogSolutions = do
  solutions ← useState λ state → return (ProofState.solutions state)
  quotedSolutions ← quoteNormalisedTC solutions
  log "basic" Debug $ strErr "Solutions: " ∷ termErr quotedSolutions ∷ []

debugLogGoalContext : Attic ⊤ {Level.zero}
debugLogGoalContext = do
  context ← getContext
  quotedContext ← quoteNormalisedTC context
  log "basic" Debug $ strErr "Context: " ∷ termErr quotedContext ∷ []

debugLogProofState : Attic ⊤ {Level.zero}
debugLogProofState = do
  proofState ← useState return
  quotedState ← quoteNormalisedTC proofState
  log "basic" Debug $ strErr "Proof state: " ∷ termErr quotedState ∷ []

------ General abstraction tactics ------

-- Solves the specified goal using the term as a solution.
solveGoal : Goal → Term → Attic ⊤ {Level.zero}
solveGoal goal term = updateState λ state → 
  goalExistsAndIsUnique goal (ProofState.goals state) (value _) ,
  record { focusedGoal = nothing
         ; goals = boolFilter
            (λ g → (Goal.meta g) meta≠ (Goal.meta goal))
            (ProofState.goals state)
         ; solutions = record { goal = goal ; solution = term } ∷ (ProofState.solutions state)
         }

guard : Bool → Attic ⊤ {Level.zero}
guard false = failure (errStr "Failed guard.")
guard true  = value _

guard′ : List Reflection.ErrorPart → Bool → Attic ⊤ {Level.zero}
guard′ err false = failure (strErr "Failed guard " ∷ err)
guard′ err true  = value _

-- Adds a goal.
addGoal : Goal → Attic ⊤ {Level.zero}
addGoal goal = updateState λ state →
  goalDoesNotExistOrSolved goal state (value _) ,
  record state { goals = goal ∷ ProofState.goals state }

-- Adds several goals.
addGoals : List Goal → Attic ⊤ {Level.zero}
addGoals [] = value _
addGoals goals@(_ ∷ _) = updateState λ state →
  goalsDoNotExistOrSolved goals state (value _) ,
  record state { goals = goals List.++ ProofState.goals state }

-- Adds a goal and immediately focuses it.
addFocusGoal : Goal → Attic ⊤ {Level.zero}
addFocusGoal goal = addGoal goal >> updateState λ state →
  value _ ,
  record state { focusedGoal = just goal }

-- Adds several goals and immediately focuses the first one.
addFocusGoals : List Goal → Attic ⊤ {Level.zero}
addFocusGoals [] = value _
addFocusGoals goals@(firstGoal ∷ _) = addGoals goals >> updateState λ state →
  value _ ,
  record state { focusedGoal = just firstGoal }

-- This tactic solves the currently focused goal, unifying it with itself.
-- It will be left as an open interaction point.
admit : Attic ⊤
admit = do
  goal ← getGoal
  solveGoal goal (Goal.hole goal)

-- This tactic clears the list of goals. Metas will be unified with themselves,
-- so they will remain as open interaction points.
admitAll : Attic ⊤ {Level.zero}
admitAll = updateState λ state →
  value _ ,
  record state { goals = []
               ; solutions = ProofState.solutions state ++
                             List.map (λ x → record { goal = x ; solution = (Goal.hole x) }) (ProofState.goals state)
               }

-- This tactic clears the list of goals. Any unknown metas will remain in the
-- unification stage, and will be left as an open interaction.
clearGoals : Attic ⊤ {Level.zero}
clearGoals = updateState λ state →
  value _ ,
  record state { goals = [] }

getContextIndex : ℕ → Attic Binding {Level.zero}
getContextIndex n = getContext >>= λ ctx → find n ctx
  where find : ℕ → Context → Attic Binding
        find i [] = failure $ errStr ("The context index " str+ (showℕ n) str+ " is out of bounds.")
        find zero (b ∷ _) = return b
        find (suc i′) (_ ∷ bs) = find i′ bs

getContextName : String → Attic (Binding × ℕ) {Level.zero}
getContextName n = getContext >>= λ ctx → find ctx zero
  where find : Context → ℕ → Attic (Binding × ℕ)
        find [] _ = failure $ errStr ("The context name " str+ n str+ " could not be found.")
        find (b@(bName , _) ∷ bs) i with primStringEquality bName n
        ... | false = find bs (suc i)
        ... | true = return (b , i)

multi : ∀ {a s} {A : Set a} → List Goal → Attic A {s} → Attic ⊤ {s}
multi {s = s} {A = A} [] attic = value {ℓs = s} _
multi {s = s} {A = A} (goal ∷ goals′) attic = updateState λ beforeState →
  let startState : ProofState
      startState = record { focusedGoal = just goal ; goals = [ goal ] ; solutions = [] }
      recursiveMulti = multi goals′ attic
      afterAttic : Attic _ {s}
      afterAttic = updateState λ endState →
        let goalMeta = Goal.meta goal
            solution = findSolution (ProofState.solutions endState) goalMeta
            afterProofState : ProofState
            afterProofState = case solution of λ {
                (just s) → record { focusedGoal = nothing
                                  ; goals = boolFilter (λ g → (Goal.meta g) meta≠ goalMeta) (ProofState.goals beforeState)
                                  ; solutions = (ProofState.solutions endState) List.++ (ProofState.solutions beforeState)
                                  }
              ; nothing  → beforeState
              }
        in recursiveMulti , afterProofState
      chained = attic >> afterAttic
  in chained , startState

infixl 10 _∶▷⁺·_
_∶▷⁺·_ : ∀ {a b s1 s2} {A : Set a} {B : Set b} → Attic A {s1} → Attic B {s2} → Attic ⊤
a ∶▷⁺· b = updateState (λ oldState → 
  let middle = a >> updateState (λ newState →
                  let newGoals = boolFilter
                        (λ ng → let ngMeta = Goal.meta ng
                                in  all (λ og → Goal.meta og meta≠ ngMeta) (ProofState.goals oldState))
                        (ProofState.goals newState)
                  in (multi newGoals b) , newState
               )
  in middle , oldState)

repeat : ∀ {a s} {A : Set a} → ℕ → Attic A {s} → Attic ⊤
repeat {s = s} zero _ = value {ℓs = s} _
repeat (suc n′) attic = attic >> repeat n′ attic

repeatTry : ∀ {a s} {A : Set a} → ℕ → Attic A {s} → Attic ⊤
repeatTry {s = s} zero _ = value {ℓs = s} _
repeatTry (suc n′) attic = try $ attic >> repeatTry n′ attic
