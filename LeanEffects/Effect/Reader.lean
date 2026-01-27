import LeanEffects.Program

inductive Reader (R : Type u) : Type u → Type u where
  | askOp : Reader R R

namespace Reader

open Program

def ask [Member (Reader R) es] : Program es R :=
  Program.perform Reader.askOp

def localEnv [Member (Reader R) es] (f : R → R) (p : Program es α) : Program es α := do
  let r ← ask
  let rec go : Program es α → Program es α
    | .ret a => .ret a
    | .op e k =>
        match (Member.prj (e:=Reader R) e) with
        | some .askOp => go (k (f r))
        | none => .op e (fun x => go (k x))
  go p

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
      | .askOp => fun r => k r r
    liftOther := fun e _ => Program.op e (fun x => ret x)
  }
  interpret handler p r

end Reader
