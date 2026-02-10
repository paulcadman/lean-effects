import LeanEffects.Program

variable {es : List Effect}

inductive IOEff (α : Type) : Type where
  | embedOp : IO α → IOEff α

namespace IOEff

open Program

def embed {α : Type} [Member IOEff es] (action : IO α) : Program es α :=
 .perform (IOEff.embedOp action)

def run {α : Type} (p : Program [IOEff] α) : IO α :=
  let handler : Handler IOEff [] IO := {
    handleEffect := fun op k =>
      match op with
      | .embedOp io => io >>= k,
    liftOther := fun e _ => nomatch e
  }
  interpret handler p

end IOEff
