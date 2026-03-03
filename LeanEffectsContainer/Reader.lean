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
  scps := ReaderScpsC S

namespace Reader

def ReaderP (effs : List Effect) (S : Type) (α : Type u) : Nat → Type (max u 1)
  | 0 => ULift α
  | n + 1 => S → Prog effs (ReaderP effs S α n)

variable
  {effs : List Effect}
  {S : Type}
  {α : Type u}

section SmartConstructor

variable
  [Reader S ∈ effs]

def ask : Prog effs S :=
  opEff (e:=Reader S) ⟨ReaderOps.askOp, fun s => Prog.var s⟩

def xxxxxx {n} (p : ProgN effs α n) : ProgN effs α (n + 1) := ProgN.varS p

def localR (f : S → S) (p : Prog effs α) : Prog effs α :=
  scpEff (e:=Reader S) ⟨ReaderScps.localOp f, fun _ =>
    -- xxxxxx p
    Prog.flatten (p.bind (Prog.var ∘ pure))
    ⟩

end SmartConstructor

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
      | .inr op' => fun st => ProgN.op op' (fun resp => k resp st))
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl op'' =>
        match op'' with
        | .localOp f => by
          simp [ReaderP]; intro devil
          simp [ReaderP, Reader] at k
          rw [pos_scps_inl] at k
          simp [ReaderScpsC] at k
          exact Prog.bind (k .unit (f devil)) (fun r => r devil)
      | .inr op' => by
        simp [ReaderP]; intro s
        simp [ReaderP, Reader] at k
        rw [pos_scps_inr] at k
        apply ProgN.scp op'
        intro resp
        specialize k resp s
        apply ProgN.varS
        apply Prog.bind k
        intro scoped_prog
        specialize scoped_prog s
        exact scoped_prog)
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
  let l2 ← localR (fun x => x + 1) ask
  let l3 ← ask
  pure [l1, l2, l3]

def prog2 {effs} [Reader Nat ∈ effs] [Exception Nat ∈ effs] : Prog effs (List Nat) := do
  Exception.catchE
    (do
      let l1 ← ask
      Exception.throwE 99
      let l3 ← ask
      pure [l1, l3])
    (fun e => pure [e])

def prog3 : Prog [Reader Nat] Nat := localR (fun x => x + 777) ask

#eval Prog.run (Reader.run 0 prog3)


def f : False := by
  have p : Reader.run 666 prog3 = sorry := sorry
  conv at p =>
    unfold run
    unfold run'
    lhs
    arg 2
    -- unfold to scp node
    simp only [runL, prog3, localR, scpEff, Container.instMemberCons, scpsMem, Container.inject]
    simp only [Prog.scp, Prog.foldP]
    --- we are in the op branch of ProgP
    lhs
    simp
    simp only [pure]
  conv at p =>
    lhs
    arg 2
    arg 1
    ext x
    arg 1
    arg 6
    simp only [Prog.bind, Prog.bindN, Prog.var, Prog.foldP, Prog.bindVarLift, Function.comp, Prog.flatten]




-- p : run 666 prog3 = sorry
-- | fun devil =>
--     Prog.bind
--       (Prog.foldP (fun n => ReaderP [] Nat Nat n) ULift.up (fun {n} p s => ProgN.varS (Prog.var p))
--         (fun {n} x =>
--           match Container.Extension.shape x, Container.Extension.point x with
--           | Sum.inl ReaderOps.askOp, k => fun st => k st st
--           | Sum.inr op', k => fun st => ProgN.op op' fun resp => k resp st)
--         (fun {n} x =>
--           match Container.Extension.shape x, Container.Extension.point x with
--           | Sum.inl op'', k =>
--             match op'', k with
--             | ReaderScps.localOp f, k => fun devil => Prog.bind (k () (f devil)) fun r => r devil
--           | Sum.inr op', k => fun s =>
--             ProgN.scp op' fun resp => ProgN.varS (Prog.bind (k resp s) fun scoped_prog => scoped_prog s))
--         (xxxxxx ask) (devil + 777))
--       fun r => r devil

Goals (1)
-- p : run 666 prog3 = sorry
-- | fun devil =>
--     Prog.bind
--       (Prog.foldP (fun n => ReaderP [] Nat Nat n) ULift.up (fun {n} p s => ProgN.varS (Prog.var p))
--         (fun {n} x =>
--           match Container.Extension.shape x, Container.Extension.point x with
--           | Sum.inl ReaderOps.askOp, k => fun st => k st st
--           | Sum.inr op', k => fun st => ProgN.op op' fun resp => k resp st)
--         (fun {n} x =>
--           match Container.Extension.shape x, Container.Extension.point x with
--           | Sum.inl op'', k =>
--             match op'', k with
--             | ReaderScps.localOp f, k => fun devil => Prog.bind (k () (f devil)) fun r => r devil
--           | Sum.inr op', k => fun s =>
--             ProgN.scp op' fun resp => ProgN.varS (Prog.bind (k resp s) fun scoped_prog => scoped_prog s))
--         (Prog.flatten (Prog.bind ask (Prog.var ∘ Prog.var))) (devil + 777))
--       fun r => r devil

















#guard Prog.run (Reader.run 0 prog) = [0, 1, 0]
#guard match Prog.run (Exception.run (E := Nat) (Reader.run 0 prog2)) with
  | .ok l => l == [99]
  | _ => false

-- #guard Prog.run (Reader.run 0 (do ask)) = 0

end Examples
