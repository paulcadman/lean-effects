import Effects.Container
import Effects.Prog

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

def logIO
  {effs : List Effect}
  [IOEff ∈ effs]
  (msg : String)
  : Prog effs Unit :=
  IOEff.embed (IO.println msg)

def exLog : Prog [IOEff] Unit := do
  logIO "a"
  logIO "b"

/--
info: a
b
-/
#guard_msgs in
#eval exLog |> IOEff.run

end Examples
