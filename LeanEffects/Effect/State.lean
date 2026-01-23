import LeanEffects.Program

inductive State (S : Type) : Type → Type where
  | getOp : State S S
  | putOp : S → State S PUnit

namespace State

open Program

def get {S : Type} [Member (State S) es] : Program es S :=
  .perform State.getOp

def put {S: Type} [Member (State S) es] (s : S) : Program es PUnit :=
  .perform (State.putOp s)

abbrev StateM (S : Type) (es : List Effect) (α : Type) :=
  S → Program es (S × α)

instance (S : Type) (es : List Effect) : Monad (StateM S es) where
  pure a := fun s => .pure (s, a)
  bind m f := fun s => do
    let (s', a) ← m s
    f a s'

def run (s: S) (p : Program (State S :: es) α) : Program es (S × α) :=
  let handler : Handler (State S) es (StateM S es) := {
    handleEffect := fun op k =>
      match op with
      | .getOp => fun st => k st st
      | .putOp s' => fun _ => k .unit s',
    liftOther := fun e st => Program.op e (fun x => Program.pure (st, x))
  }
  interpret handler p s

end State
