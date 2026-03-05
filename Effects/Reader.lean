import Effects.Container
import Effects.Prog
import Effects.Exception

open scoped Container

universe u

inductive ReaderOps (S : Type) : Type 1 where
  | askOp

inductive ReaderScps (S : Type) : Type 1 where
  | localOp (f : S → S)

def ReaderOpsC (S : Type) : Container where
  shape := ReaderOps S
  pos := fun
   | .askOp => S

def ReaderScpsC (S : Type) : Container where
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

def localR (f : S → S) (p : Prog effs α) : Prog effs α :=
  scpEff (e:=Reader S) ⟨ReaderScps.localOp f, fun _ => Prog.flatten (p.bind (Prog.var ∘ pure))⟩

end SmartConstructor

def runL
  (p : Prog (Reader S :: effs) α) :
  S → Prog effs (ULift α) :=
  Prog.foldP
    (effs:=Reader S :: effs)
    (n:=1)
    (P := fun n => ReaderP effs S α n)
    (var0 := ULift.up)
    (varS := fun p => fun _ => ProgN.varS (Prog.var p))
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl .askOp => fun st => k st st
      | .inr op' => fun st => ProgN.op op' (fun resp => k resp st))
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl (.localOp f) => fun st => k .unit (f st) >>= fun r => r st
      | .inr op' => fun s =>
          Prog.scp ⟨op', fun resp => ProgN.varS (k resp s >>= fun scoped_prog => scoped_prog s)⟩)
    p

def run (s : S) (p : Prog (Reader S :: effs) α) : Prog effs α :=
  Prog.mapU ULift.down (runL p s)

namespace Examples

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

#guard Prog.run (Reader.run 0 prog) = [0, 1, 0]

#guard Prog.run (Exception.run (E := Nat) (Reader.run 0 prog2)) = .ok [99]

end Examples

end Reader
