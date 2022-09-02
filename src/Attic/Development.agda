module Attic.Development where

open import Attic.GlobalImports
open import Attic.Monad

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.String using (String; _++_)
open import Reflection using (TC; debugPrint; ErrorPart)
open import Reflection using (strErr; termErr; nameErr) public

data LogLevel : Set where
  Debug : LogLevel
  Info  : LogLevel
  Error : LogLevel

private
  makeVerbosityId : String → String
  makeVerbosityId "" = "attic"
  makeVerbosityId component = "attic." ++ component

  logLevelToℕ : LogLevel → ℕ
  logLevelToℕ Debug = 0
  logLevelToℕ Info  = 0
  logLevelToℕ Error = 0

-- A simple wrapper for strErr.
errStr : String → List ErrorPart
errStr s = strErr s ∷ []

log′ : String → LogLevel → List ErrorPart → TC ⊤
log′ component logLevel messages = debugPrint verbosityId level messages
  where
    verbosityId = makeVerbosityId component
    level = logLevelToℕ logLevel

log : String → LogLevel → List ErrorPart → Attic ⊤
log component logLevel messages = liftTC! $ log′ component logLevel messages
