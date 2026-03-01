import LeanEffectsContainer.Container
import LeanEffectsContainer.Prog

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

end Exception

section Examples

open Exception

def exThrow {effs} [Exception String ∈ effs] : Prog effs Nat :=
  throwE "boom"

def exCatch {effs} [Exception String ∈ effs] : Prog effs Nat :=
  catchE exThrow (fun (_ : String) => pure 42)

def exCatchNoThrow {effs} [Exception String ∈ effs] : Prog effs Nat :=
  catchE (pure 7) (fun (_ : String) => pure 42)

#guard (match Prog.run (run exThrow) with | .error "boom" => true | _ => false)
#guard (match Prog.run (run exCatch (E:=String)) with | .ok 42 => true | _ => false)
#guard (match Prog.run (run exCatchNoThrow (E:=String)) with | .ok 7 => true | _ => false)

end Examples
