import LeanEffectsContainer.Container
import LeanEffectsContainer.Prog
import LeanEffectsContainer.State

open scoped Container

inductive IOEffOps : Type 1 where
  | embedOp {α : Type} (action : IO α)

def IOEffOpsC : Container.{1, 0} where
  shape := IOEffOps
  pos
    | .embedOp (α:=α) _ => α

def IOEff : Effect where
  ops := IOEffOpsC
  scps := Container.void

namespace IOEff

variable
  {effs : List Effect}
  {α : Type}

section SmartConstructor

variable
  [IOEff ∈ effs]

def embed (action : IO α) : Prog effs α :=
  opEff (e := IOEff) ⟨.embedOp action, fun a => Prog.var a⟩

end SmartConstructor

def run (p : Prog [IOEff] α) : IO α :=
  Prog.foldP
    (P := fun _ => IO α)
    (var0 := pure)
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl (.embedOp io) => io >>= fun x => k x
      | .inr e => nomatch e)
    (scp := fun ⟨c, _⟩ =>
      match c with
      | .inl e => nomatch e
      | .inr e => nomatch e)
    p

end IOEff

section Examples

def logIO {effs : List Effect} [IOEff ∈ effs] (msg : String) : Prog effs Unit :=
  IOEff.embed (IO.println msg)

def exStateReaderIO : Prog [State Nat, IOEff] Unit := do
  let (n : Nat) ← State.get
  logIO s!"n={n}"
  State.put (n + 1)
  logIO "updated state"

def runStateReaderIO : IO Unit :=
  exStateReaderIO
    |> State.eval 1
    |> IOEff.run

/--
info: n=1
updated state
-/
#guard_msgs in
#eval runStateReaderIO

end Examples
