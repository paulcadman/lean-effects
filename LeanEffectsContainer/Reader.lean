import LeanEffectsContainer.Container
import LeanEffectsContainer.Prog
import LeanEffectsContainer.Exception

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

abbrev Reader (S : Type) : Effect where
  ops := ReaderOpsC S
  scps := Container.void

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

-- def tmp (p : ProgN effs (Prog effs α) 1) : ProgN effs α 2 := sorry

def ask : Prog effs S :=
  opEff (e:=Reader S) ⟨ReaderOps.askOp, fun s => Prog.var s⟩

-- def localR (f : S → S) (p : Prog effs α) : Prog effs α :=
--   scpEff (e:=Reader S) ⟨ReaderScps.localOp f, fun .unit => tmp (Prog.var p)
-- ⟩

end SmartConstructor

-- {n : Nat} → ReaderP effs S α n → S → ProgN effs (ReaderP effs S α n) (n + 1)
def runL
  (p : Prog (Reader S :: effs) α) :
  S → Prog effs (ULift α) :=
  Prog.foldP
    (effs:=Reader S :: effs)
    (n:=1)
    (P := fun n => ReaderP effs S α n)
    (var0 := ULift.up)
    (varS := by
      intro n p
      simp [ReaderP]; intro s
      apply ProgN.varS
      apply Prog.var
      exact p)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl .askOp => fun st => k st st
      | .inr op' => by
        simp [ReaderP]; intro s
        apply ProgN.op _
        intro resp
        simp [ReaderP] at k
        rw [pos_ops_inr] at k -- wut
        apply k (((fun a => resp) ∘ k resp) s) s)
      -- fun ⟨c, k⟩ s =>
      -- sorry
      -- match c with
      -- | .inl ReaderOps.askOp => fun st => k st st
      -- | .inr s => fun st =>
      --   Prog.op ⟨s, fun p => k p st⟩)
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl x => nomatch x
      | .inr op' => by
        simp [ReaderP]; intro s
        simp [ReaderP, Reader] at k
        rw [pos_scps_inr] at k
        apply ProgN.scp op'
        intro resp
        specialize k resp s
        apply Prog.bindN' k
        intro scoped_prog
        specialize scoped_prog s
        exact ProgN.varS scoped_prog)
    p

def run' (p : Prog (Reader S :: effs) α) (s : S) : Prog effs α :=
  Prog.mapU ULift.down (runL p s)

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
  -- let l2 ← localR (fun x => x + 1) ask
  let l3 ← ask
  pure [l1, l3]

def prog2 : Prog [Reader Nat, Exception Nat] (List Nat) := do
  Exception.catchE
    (do
      let l1 ← ask
      Exception.throwE 99
      let l3 ← ask
      pure [l1, l3])
    (fun e => pure [e])

#guard Prog.run (Reader.run 0 prog) = [0, 0]
#guard match Prog.run (Exception.run (Reader.run 0 prog2)) with
  | .ok l => l == [99]
  | _ => false

-- #guard Prog.run (Reader.run 0 (do ask)) = 0

end Examples
