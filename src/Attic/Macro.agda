module Attic.Macro where

open import Attic.Core
open import Attic.Development
open import Attic.GlobalImports
open import Attic.Iterator as Iterator using (Iterator; Done; Skip; Yield; iterator; single; singleℓ; fromList)
import Attic.Iterator.Categorical as Iterator
import Attic.Iterator.Bound
open import Attic.Monad hiding (_>>_; _>>=_; _<$>_; return)
open import Attic.Utils.Reflection using (thenTC)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; []; [_]; length)
open import Data.Maybe using (maybe′)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _str+_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (⊤ to ⊤ℓ)
open import Function using (case_of_)
open import Level using (Level)
open import Reflection using (ErrorPart; TC; Arg; Term; Type; bindTC; catchTC; getContext; inContext; inferType; quoteTC; runSpeculative; typeError; unify; withNormalisation)
open import Reflection.TypeChecking.Monad.Instances

open StdM

private
  -- Options
  DEBUG─catchUnification = true
  defaultSearchDepth = 10000

  variable
    ℓa ℓs : Level
    A : Set ℓa

  AtticClosure : {a : Level} → Set a → Set (Level.suc a)
  AtticClosure A = Attic A × ProofState

  Rest : {s a : Level} → Set a → Set (Level.suc a Level.⊔ Level.suc s)
  Rest {s} A = Iterator {_} {s} (AtticClosure A)

  OptionalRest : {s a : Level} → Set a → Set (Level.suc a Level.⊔ Level.suc s)
  OptionalRest {s} A = Maybe (Rest {s} A)

  data AtticResult {s a : Level} (A : Set a) : Set (Level.suc (a Level.⊔ s)) where
    -- Indicates that the Attic evaluation has succeeded.
    atticSuccess : ProofState     → OptionalRest {s} A → AtticResult A
    -- Indicates that the Attic evaluation has failed, but backtracking is allowed.
    atticFailure : List ErrorPart → OptionalRest {s} A → AtticResult A
    -- Indicates that the Attic evaluation has failed fatally. Disallows backtracking.
    atticError   : List ErrorPart                      → AtticResult A

  data UnificationOutcome {s a : Level} (A : Set a) : Set (Level.suc (a Level.⊔ s)) where
    unificationSuccess :                      UnificationOutcome {s} A
    unificationFailure : OptionalRest {s} A → UnificationOutcome {s} A
    unificationError   : List ErrorPart     → UnificationOutcome {s} A

  data EvaluationOutcome : Set where
    -- Indicates that a working solution was found.
    finished   :                  EvaluationOutcome
    -- Indicates that no solution was found, and that the search depth was exceeded.
    incomplete :                  EvaluationOutcome
    -- Indicates that no solution was found, and all candidate solutions are exhausted.
    exhausted  :                  EvaluationOutcome
    -- Indicates that a fatal error occurred while evaluating candidate solutions.
    fatalError : List ErrorPart → EvaluationOutcome

  isUnificationSuccess : UnificationOutcome {ℓs} A → Bool
  isUnificationSuccess unificationSuccess = true
  isUnificationSuccess _                  = false

  -- does not require runSpeculative

  -- Changes the initial state of an iterator structure. Not really suitable for inclusion in the
  -- iterator base implementation due to potential issues with bounds, but fine here.
  offsetIterator : (it : Iterator {_} {ℓs = ℓs} A) → Iterator.S₀ it → Iterator {_} {ℓs = ℓs} A
  offsetIterator it s = record it {
    state = s ;
    bound = (Iterator.bound it) Attic.Iterator.Bound.∸ (Attic.Iterator.Bound.bounded 1) }

  -- runAttic evaluates a single branch of the given Attic instruction. If this instruction
  -- produces branching instructions, it will return these next Attic instruction for later
  -- execution.
  {-# TERMINATING #-}
  runAttic : Attic A →
             ProofState →
             TC (AtticResult A)
  runAttic (value x) p = return $ atticSuccess p nothing
  runAttic (failure s) p = return $ atticFailure s nothing
  runAttic (error s) p = return $ atticError s
  runAttic (tryCatch t c) p = do
    -- Try running the instruction first
    atticFailure _ _ ← runAttic t p
      where
        res@(atticSuccess _ _) → return res
        res@(atticError _) → return res
    -- If it's a soft failure, run the catch-instruction
    -- Capturing the rest does not make sense, since that defeats the point of the tryCatch
    runAttic c p
  runAttic (primitiveTC tcm) p = bindTC tcm (λ x → runAttic x p)
  runAttic (updateState stateConsumer) p =
    let (a , s) = stateConsumer p in
    runAttic a s
  runAttic {A = A} (branch′ iter) p = nextResult
    where
      nextStep = (Iterator.next iter) (Iterator.state iter)
      makeStateClosure : Attic A → Attic A × ProofState
      makeStateClosure a = a , p
      nextResult : TC (AtticResult A)
      nextResult with nextStep
      ... | Done = return $ atticFailure (errStr "runAttic/nextResult: done") nothing
      ... | Skip s2 = return $ atticFailure (errStr "runAttic/nextResult: skip") (just rest)
              where
                offsetIter = offsetIterator iter s2
                rest = Iterator.map makeStateClosure offsetIter
      ... | Yield s2 atc = do
              let offsetIter = offsetIterator iter s2
                  rest = Iterator.map makeStateClosure offsetIter
                  restWithRec : OptionalRest A → OptionalRest A
                  restWithRec nexts = maybe′ (λ recNexts → just (recNexts Iterator.++ rest)) (just rest) nexts

              atticError err ← runAttic atc p
                where
                  atticSuccess ps′ nexts → return (atticSuccess ps′ (restWithRec nexts))
                  atticFailure msg nexts → return (atticFailure msg (restWithRec nexts))
              return (atticError err)

  -- Unifies a list of solutions, i.e. the hole of every solution is unified with the corresponding
  -- solution term.
  unifyAll : List Solution → TC ⊤
  unifyAll [] = return _
  unifyAll (s ∷ ss) = unifyS >> unifyAll ss
    where
      unifyS = inContext
        (contextToTCContext $ Goal.context (Solution.goal s))
        (unify (Solution.solution s) (Goal.hole (Solution.goal s)))

  unifyAtticResult : AtticResult {ℓs} A →
                     TC (UnificationOutcome {ℓs} A)
  unifyAtticResult (atticSuccess ps rest) = case length (ProofState.goals ps) of λ
    { zero → let unification = thenTC (unifyAll (ProofState.solutions ps)) (return unificationSuccess)
             in if DEBUG─catchUnification
                then (catchTC unification (return (unificationFailure rest)))
                else unification
    ; n@(suc _) → return (unificationError (errStr ("Tactic incomplete; there is/are " str+ (showℕ n) str+ " goals remaining.")))
    }
  unifyAtticResult (atticFailure msg rest) = thenTC
    (log′ "macro" Debug (strErr "Tactic evaluation failed: " ∷ msg))
    (return (unificationFailure rest))
  unifyAtticResult (atticError        err) = return (unificationError err)

  -- -- Concatenates two iterators, but the first iterator is optional. Due to universe level issues,
  -- -- it isn't possible to return the second iterator if the first is `nothing`, so concat it with
  -- -- an empty iterator of the appropriate level.
  combineRests : ∀ {a b x} {X : Set x} → Maybe (Iterator {ℓs = a} X) → Iterator {ℓs = b} X → Iterator X
  combineRests {a = a} {x = x} nothing preExisting = Iterator.emptyℓℓ x a Iterator.++ preExisting
  combineRests         (just recursed) preExisting = recursed             Iterator.++ preExisting

evaluateAttic : (searchDepth : ℕ) →
                Attic A →
                ProofState →
                TC EvaluationOutcome
evaluateAttic {ℓa} {A} searchDepth attic initialState = runAtticClosure searchDepth (attic , initialState) (Iterator.emptyℓℓ (Level.suc ℓa) Level.zero)
  where
    skipPlaceholder : AtticClosure A
    skipPlaceholder = (failure (errStr "evaluateAttic/unificationFailure: skip")) , initialState

    runAtticClosure : (fuel : ℕ) → AtticClosure A → Rest {s = ℓs} A → TC EvaluationOutcome
    runAtticClosure zero _ _ = return incomplete
    runAtticClosure (suc fuel′) (attic , ps) rest =
      let run = runSpeculative do
            atticResult ← runAttic attic ps
            unifyOutcome ← unifyAtticResult atticResult
            -- The comment below is the correct implementation, but it may cause panics.
            -- For this reason, I have disabled it for now.
            -- return (unifyOutcome , isUnificationSuccess unifyOutcome)
            return (unifyOutcome , true)
      in bindTC run λ
        {  unificationSuccess        → return finished
        ; (unificationError err)     → return (fatalError err)
        ; (unificationFailure rest′) →
            let rests = combineRests rest′ rest
            in case (Iterator.next rests) (Iterator.state rests) of λ 
              { Done → return exhausted
              ; (Skip s2) → let offsetRests = offsetIterator rests s2
                            in runAtticClosure fuel′ skipPlaceholder offsetRests
              ; (Yield s2 closure) → let offsetRests = offsetIterator rests s2
                                     in runAtticClosure fuel′ closure offsetRests
              }
        }

asMacro′ : ℕ → Attic A → Term → TC ⊤
asMacro′ searchDepth attic hole = do
  holeType ← inferType hole
  context ← tcContextToContext <$> getContext
  just metaTerm ← return $ getMeta hole
    where _ → typeError (strErr "The given hole is not an unsolved meta: " ∷ termErr hole ∷ [])

  let
    -- Create the initial goal, based on the given hole
    initialGoal : Goal
    initialGoal = record { type = holeType
                         ; hole = hole
                         ; meta = metaTerm
                         ; context = context
                         }
    -- Create the initial proof state
    initialState : ProofState
    initialState = record { focusedGoal = just initialGoal
                          ; goals = [ initialGoal ]
                          ; solutions = []
                          }

  let result = evaluateAttic searchDepth attic initialState
  finished ← result
    where
      incomplete → typeError $ errStr "Search depth exceeded (no solution found). Try increasing the search depth (asMacro′) or optimize your tactic(s)."
      exhausted → typeError $ errStr "No solution was found (options exhausted)."
      (fatalError err) → typeError $ strErr "A fatal error occurred while evaluating proof candidates: " ∷ err
  
  return _

asMacro : Attic A → Term → TC ⊤
asMacro = asMacro′ defaultSearchDepth
