import LeanEffectsContainer.Container
import LeanEffectsContainer.Prog

open scoped Container

universe u

inductive ReaderOps (S : Type) : Type 1 where
  | askOp

inductive ReaderScps (S : Type) : Type 1 where
  | localOp (f : S → S)

def ReaderOpsC (S : Type) : Container.{1, 0} where
  shape := ReaderOps S
  pos := fun
   | .askOp => S

def ReaderScpsC (S : Type) : Container.{1, 0} where
  shape := ReaderScps S
  pos
    | .localOp _ => Unit

def Reader (S : Type) : Effect where
  ops := ReaderOpsC S
  scps := ReaderScpsC S

namespace Reader

def ReaderP (effs : List Effect) (α : Type u) : Nat → Type (max 1 u)
  | 0 => Prog effs α
  | n + 1 => ProgN effs α (n + 1)

variable
  {effs : List Effect}
  {S : Type}
  {α : Type u}

section SmartConstructor

variable
  [Reader S ∈ effs]

def tmp (p : ProgN effs (Prog effs α) 1) : ProgN effs α 2 := sorry

def ask : Prog effs S :=
  opEff (e:=Reader S) ⟨ReaderOps.askOp, fun s => Prog.var s⟩

def localR (f : S → S) (p : Prog effs α) : Prog effs α :=
  scpEff (e:=Reader S) ⟨ReaderScps.localOp f, fun .unit => tmp (Prog.var p)
⟩

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
      | .inl x => match x with
        | .localOp f =>
          fun s =>
          do let (r : α) ← k .unit (f s)
             pure r
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

def prog : Prog [Reader Nat] (List Nat) := do
  let l1 ← ask
  let l2 ← localR (fun x => x + 1) ask
  let l3 ← ask
  pure [l1, l2, l3]

#guard Prog.run (Reader.run 0 prog) = [0,1,1]

#guard Prog.run (Reader.run 0 (do ask)) = 0



end Examples
