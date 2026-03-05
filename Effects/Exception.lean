import Effects.Container
import Effects.Prog
import Effects.State

open scoped Container

inductive ExceptionOps (E : Type) : Type 1 where
  | throwOp (e : E)

inductive ExceptionScps : Type 1 where
  | catchOp

def ExceptionOpsC (E : Type) : Container.{1, 0} where
  shape := ExceptionOps E
  pos
    | .throwOp _ => Empty

def ExceptionScpsC (E : Type) : Container.{1, 0} where
  shape := ExceptionScps
  pos
    | .catchOp => Unit ⊕ E

def Exception (E : Type) : Effect where
  ops := ExceptionOpsC E
  scps := ExceptionScpsC E

namespace Exception

variable
  {effs : List Effect}
  {E : Type}
  {α : Type}

section SmartConstructor

variable
  [Exception E ∈ effs]

def throwE (e : E) : Prog effs α :=
  opEff (e:=Exception E) ⟨.throwOp e, fun x => nomatch x⟩

def catchE
  (p : Prog effs α)
  (h : E → Prog effs α) :
  Prog effs α :=
  let response
    | .inl _ => ProgN.varS p
    | .inr e => ProgN.varS (h e)
  scpEff (e:=Exception E) ⟨.catchOp, response⟩

end SmartConstructor

def run (p : Prog (Exception E :: effs) α) : Prog effs (Except E α) :=
  Prog.foldP
    (P := fun _ => Prog effs (Except E α))
    (var0 := fun x => pure (.ok x))
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl (.throwOp e) => pure (.error e)
      | .inr s => Prog.op ⟨s, k⟩)
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl .catchOp => do
        let r ← k (.inl ())
        match r with
        | .ok x => pure (.ok x)
        | .error e => k (.inr e)
      | .inr s => Prog.scp ⟨s, fun p => ProgN.varS (k p)⟩)
    p

-- taken from https://brandonrozek.com/blog/writing-unit-tests-lean-4/
instance {α β} [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := by
  unfold DecidableEq
  intro a b
  cases a <;> cases b <;>
  -- Get rid of obvious cases where .ok != .err
  try { apply isFalse ; intro h ; injection h }
  case error.error c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)
  case ok.ok c d =>
    match decEq c d with
      | isTrue h => apply isTrue (by rw [h])
      | isFalse _ => apply isFalse (by intro h; injection h; contradiction)

end Exception

section Examples

open Exception

def exThrow {effs} [Exception String ∈ effs] : Prog effs Nat :=
  throwE "boom"

def exCatch {effs} [Exception String ∈ effs] : Prog effs Nat :=
  catchE exThrow (fun (_ : String) => pure 42)

def exCatchNoThrow {effs} [Exception String ∈ effs] : Prog effs Nat :=
  catchE (pure 7) (fun (_ : String) => pure 42)

#guard Prog.run (run exThrow) = .error "boom"
#guard Prog.run (run exCatch (E:=String)) = .ok 42
#guard Prog.run (run exCatchNoThrow (E:=String)) = .ok 7

def decr
  {effs}
  [State Int ∈ effs]
  [Exception Unit ∈ effs] :
  Prog effs Unit := do
    let x ← State.get
    if x > (0 : Int) then State.put (x - 1) else throwE ()

def tripleDecr
  {effs}
  [State Int ∈ effs]
  [Exception Unit ∈ effs] :
  Prog effs Unit := do
    decr
    catchE (do decr; decr) pure

#guard Prog.run (State.run (2 : Int) (Exception.run (E:=Unit) tripleDecr)) = (0, .ok ())
#guard Prog.run (Exception.run (E:=Unit) (State.run (2 : Int) tripleDecr)) = .ok (1, ())

end Examples
