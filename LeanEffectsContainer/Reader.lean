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

-- (λ i → (λ X → Γ → Prog effs X) ^ i $ A)

def ReaderP (effs : List Effect) (S : Type) (α : Type u) : Nat → Type (max u 1)
  | 0 => ULift α
  | n + 1 => S → ProgN effs (ReaderP effs S α n) (n + 1)

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

-- {n : Nat} → ReaderP effs S α n → S → ProgN effs (ReaderP effs S α n) (n + 1)
def run'
  (p : Prog (Reader S :: effs) (ULift α)) :
  S → Prog effs (ULift α) :=
  Prog.foldP
    (effs:=Reader S :: effs)
    (n:=1)
    (P := fun n => ReaderP effs S α n)
    (var0 := id)
    (varS := sorry)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl .askOp => fun st => k st st
      | .inr s => fun st => Prog.op ⟨s, fun p => by
      simp [Reader, ops, Container.sum, Container.coproduct] at k
      exact k p st⟩)
      -- fun ⟨c, k⟩ s =>
      -- sorry
      -- match c with
      -- | .inl ReaderOps.askOp => fun st => k st st
      -- | .inr s => fun st =>
      --   Prog.op ⟨s, fun p => k p st⟩)
    (scp := sorry)
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
