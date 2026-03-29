import Effects.Container
import Effects.Prog
import Effects.IOEff

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

def runViaIO'
  [IOEff ∈ effs]
  (p : Prog (State S :: effs) α) :
  IO.Ref S → Prog effs (S × α) :=
  Prog.foldP
    (P := fun _ => IO.Ref S → Prog effs (S × α))
    (var0 := fun x => fun iost =>
      IOEff.embed iost.get |>.bind (fun st => pure (st, x)))
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl StateOps.getOp => fun iost =>
        IOEff.embed iost.get |>.bind (fun st => k st iost)
      | .inl (StateOps.putOp s') => fun iost =>
        IOEff.embed (iost.set s') |>.bind (fun _ => k () iost)
      | .inr s => fun iost =>
        Prog.op ⟨s, fun p => k p iost⟩)
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl x => nomatch x
      | .inr s => fun iost => Prog.scp ⟨s, fun p => ProgN.varS (k p iost)⟩)
    p

def runViaIO
  [IOEff ∈ effs]
  (s : IO.Ref S)
  (p : Prog (State S :: effs) α)
  : Prog effs (S × α) :=
  runViaIO' p s

def evalViaIO
  [IOEff ∈ effs]
  (s : IO.Ref S)
  (p : Prog (State S :: effs) α)
  : Prog effs α :=
  Prod.snd <$> runViaIO' p s

end State

section Examples

open State

def ticks
  {effs}
  [State Nat ∈ effs]
  : Prog effs Nat := do
  let n ← get
  put (n + 1)
  let m ← get
  pure (n + 2 * m)

def runTicksPure : Nat × Nat :=
  ticks
  |> State.run 0
  |> Prog.run

#guard runTicksPure = (1, 2)

def runTicksIO : IO (Nat × Nat × Nat) := do
  let ref ← IO.mkRef 0
  let res ← ticks
    |> State.runViaIO ref
    |> IOEff.run
  -- also check that the IO.Ref was updated
  (← ref.get, res) |> pure

/--
info: (1, 1, 2)
-/
#guard_msgs in
#eval runTicksIO

def twoState
  {effs}
  [State Bool ∈ effs]
  [State Nat ∈ effs]
  : Prog effs Unit := do
  let b ← get
  let n ← get
  put (n + 1)
  let n ← get
  put (b && n > 5)

def runTwoStatePure : Nat × Bool × Unit :=
  twoState
  |> State.run true
  |> State.run 4
  |> Prog.run

#guard runTwoStatePure = (5, false, ())

def runTwoStateIO : IO (Nat × Nat × Bool × Unit) := do
  let ref : IO.Ref Nat ← IO.mkRef 4
  let res ← twoState
    |> State.run true
    |> State.runViaIO ref
    |> IOEff.run
  -- Also check that the IO.Ref was updated
  (← ref.get, res) |> pure

/--
info: (5, 5, false, ())
-/
#guard_msgs in
#eval runTwoStateIO

end Examples
