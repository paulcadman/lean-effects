import LeanEffects.Program

inductive Reader (R : Type) : Type → Type where
  | askOp : Reader R R

namespace Reader

open Program

def ask [Member (Reader R) es] : Program es R :=
  Program.perform Reader.askOp

abbrev ReaderM (R : Type) (es : List Effect) (α : Type) :=
  R → Program es α

instance (R : Type) (es : List Effect) : Monad (ReaderM R es) where
  pure a := fun _ => ret a
  bind m f := fun r => do
    let r' ← m r
    f r' r

def run (r : R) (p : Program (Reader R :: es) α) : Program es α :=
  let handler : Handler (Reader R) es (ReaderM R es) := {
    handleEffect := fun op k =>
      match op with
      | .askOp => fun r => k r r,
    liftOther := fun e _ => Program.op e (fun x => ret x)

  }
  interpret handler p r

end Reader
