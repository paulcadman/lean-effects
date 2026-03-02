import LeanEffectsContainer.Container
import LeanEffectsContainer.Prog

open scoped Container

universe u

inductive ReaderOps (S : Type) : Type 1 where
  | askOp

inductive ExceptionScps : Type 1 where
  | localOp

def ReaderOpsC (S : Type) : Container.{1, 0} where
  shape := ReaderOps S
  pos := fun
   | .askOp => S

-- def ReaderScpsC : Container.{1, 0} where
--   shape := ExceptionScps
--   pos
--     | .localOp => Unit

def Reader (S : Type) : Effect where
  ops := ReaderOpsC S
  scps := Container.void

namespace Reader

variable
  {effs : List Effect}
  {S : Type}
  {α : Type u}

section SmartConstructor

variable
  [Reader S ∈ effs]

def ask : Prog effs S :=
  opEff (e:=Reader S) ⟨ReaderOps.askOp, fun s => Prog.var s⟩

end SmartConstructor

def run'
  (p : Prog (Reader S :: effs) α) :
  S → Prog effs α :=
  Prog.foldP
    (P := fun _ => S → Prog effs α)
    (var0 := fun x => fun _st => pure x)
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl ReaderOps.askOp => fun st => k st st
      | .inr s => fun st =>
        Prog.op ⟨s, fun p => k p st⟩)
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl x => nomatch x
      | .inr s => fun st => Prog.scp ⟨s, fun p => ProgN.varS (k p st)⟩)
    p

def run
  (s : S)
  (p : Prog (Reader S :: effs) α) :
  Prog effs α :=
  run' p s

end Reader

section Examples

open Reader

def tick {effs} [Reader Nat ∈ effs] : Prog effs Nat := do
  ask

#guard Prog.run (Reader.run 0 (do ask)) = 0

end Examples
