import LeanEffectsContainer.Container
import LeanEffectsContainer.Prog

open scoped Container

universe u

inductive StateOps (S : Type) : Type 1 where
  | getOp
  | putOp (s : S)

def StateOpsC (S : Type) : Container.{1, 0} where
  shape := StateOps S
  pos := fun
   | .getOp => S
   | .putOp _ => Unit

def State (S : Type) : Effect where
  ops := StateOpsC S
  scps := Container.void

namespace State

variable
  {effs : List Effect}
  {S : Type}
  {α : Type u}

section SmartConstructor

variable
  [State S ∈ effs]

def get : Prog effs S :=
  opEff (e:=State S) ⟨StateOps.getOp, fun s => Prog.var s⟩

def put (s : S) : Prog effs Unit :=
  opEff (e:=State S) ⟨StateOps.putOp s, fun _ => Prog.var .unit⟩

end SmartConstructor

def run'
  (p : Prog (State S :: effs) α) :
  S → Prog effs (S × α) :=
  Prog.foldP
    (P := fun _ => S → Prog effs (S × α))
    (var0 := fun x => fun st => pure (st, x))
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl StateOps.getOp => fun st => k st st
      | .inl (StateOps.putOp s') => fun _ => k () s'
      | .inr s => fun st =>
        Prog.op ⟨s, fun p => k p st⟩)
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl x => nomatch x
      | .inr s => fun st => Prog.scp ⟨s, fun p => ProgN.varS (k p st)⟩)
    p

def run
  (s : S)
  (p : Prog (State S :: effs) α) :
  Prog effs (S × α) :=
  run' p s

def eval (s : S) (p : Prog (State S :: effs) α) : Prog effs α :=
  Prod.snd <$> run s p

end State

section Examples

open State

def tick {effs} [State Nat ∈ effs] : Prog effs Unit := do
  let i ← get
  put (1 + i)

#guard Prog.run (State.run 0 (do tick; tick)) = (2, ())

end Examples
