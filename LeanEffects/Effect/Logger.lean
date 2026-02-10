import LeanEffects.Program
import LeanEffects.Effect.State

variable {es : List Effect}

inductive Logger : Type → Type where
  | logOp : String → Logger PUnit

namespace Logger

open Program
open State

def log [Member Logger es] (s : String) : Program es PUnit :=
  .perform (Logger.logOp s)

def runViaState {α : Type} : Program (Logger :: es) α → Program (State (List String) :: es) α :=
  let handler {γ} : Logger γ → (γ → Program (State (List String) :: es) α) → Program (State (List String) :: es) α :=
    fun l k =>
      match l with
      | .logOp msg => do
        let xs ← get
        put (xs ++ [msg])
        k PUnit.unit
  reinterpret handler

end Logger
