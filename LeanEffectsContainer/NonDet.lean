import LeanEffectsContainer.Prog
import LeanEffectsContainer.State

open scoped Container

inductive NonDetOps where
  | choiceOp
  | failOp

inductive NonDetScps where
  | once

def NonDetOpsC : Container where
  shape := NonDetOps
  pos := fun
    | .choiceOp => Bool
    | .failOp => Empty

def NonDetScpsC : Container where
  shape := NonDetScps
  pos := fun
    | .once => PUnit

def NonDet : Effect where
  ops := NonDetOpsC
  scps := NonDetScpsC

namespace NonDet

variable
  {effs : List Effect}
  {α : Type}

section SmartConstructor

variable
  [NonDet ∈ effs]

def choiceBool : Prog effs Bool :=
  opEff (e:=NonDet) ⟨NonDetOps.choiceOp, fun b => Prog.var b⟩

def choice (p : Prog effs α) (q : Prog effs α) : Prog effs α := do
  let b : Bool ← choiceBool
  if b then p else q

scoped notation p " ?? " q => choice p q

def fail : Prog effs α :=
  opEff (e:=NonDet) ⟨NonDetOps.failOp, fun e => nomatch e⟩

def once (p : Prog effs α) : Prog effs α :=
  scpEff (e:=NonDet) ⟨NonDetScps.once, fun _ => ProgN.varS p⟩

end SmartConstructor

def runList {α : Type} :
  Prog (NonDet :: effs) α → Prog effs (List α) :=
  Prog.foldP
    (P := fun _ => Prog effs (List α))
    (var0 := fun x => pure [x])
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl .choiceOp => do
        let xs ← k true
        let ys ← k false
        pure (xs ++ ys)
      | .inl .failOp => pure []
      | .inr s => Prog.op ⟨s, k⟩)
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl .once => do
        let xs ← k PUnit.unit
        match xs with
        | [] => pure []
        | x :: _ => pure [x]
      | .inr s => Prog.scp ⟨s, fun p => ProgN.varS (k p)⟩)

def runFirst :
    Prog (NonDet :: effs) α → Prog effs (Option α) :=
  Prog.foldP
    (P := fun _ => Prog effs (Option α))
    (var0 := fun x => pure (some x))
    (varS := fun {_} x => x)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl .choiceOp => do
          let l <- k true
          match l with
          | some x => pure (some x)
          | none => k false
      | .inl .failOp => pure none
      | .inr s => Prog.op ⟨s, k⟩)
    (fun ⟨c, k⟩ =>
      match c with
      | .inl .once => k PUnit.unit
      | .inr s => Prog.scp ⟨s, (fun p => ProgN.varS (k p))⟩)

def lower2
    {effs : List Effect} {α : Type} {n : Nat} :
    ProgN effs α (n + 2) → ProgN effs α (n + 1)
  | .varS x => x
  | .op c k => .op c (fun p => lower2 (k p))
  | .scp c k => .scp c (fun p => lower2 (n := n + 1) (k p))
termination_by x => sizeOf x
decreasing_by
  all_goals sorry

partial def msplit :
    Prog (NonDet :: effs) α → Prog effs (Option (α × Prog (NonDet :: effs) α))
  | ProgN.varS (ProgN.var0 x) => pure (some (x, fail))
  | ProgN.op c k =>
      match c with
      | .inl .choiceOp => do
          let l ← msplit (k true)
          match l with
          | some (x, rest) => pure (some (x, rest ?? k false))
          | none => msplit (k false)
      | .inl .failOp => pure none
      | .inr s => Prog.op ⟨s, fun p => msplit (k p)⟩
  | ProgN.scp c k =>
      match c with
      | .inl .once => do
          let r ← msplit (lower2 (k ()))
          match r with
          | some (x, _) => pure (some (x, fail))
          | none => pure none
      | .inr s =>
          Prog.scp ⟨s, fun p => ProgN.varS (msplit (lower2 (k p)))⟩

end NonDet

section Examples

open NonDet

def exOne : Prog [NonDet] Nat :=
  pure 1 ?? fail

#guard Prog.run (runList exOne) = [1]
#guard Prog.run (runFirst exOne) = .some 1

def exBoth : Prog [NonDet] Nat :=
  pure 1 ?? pure 2

#guard Prog.run (runList exBoth) = [1, 2]
#guard Prog.run (runFirst exBoth) = .some 1

def exOnce : Prog [NonDet] Nat :=
  once <| pure 1 ?? pure 2

#guard Prog.run (runList exOnce) = [1]
#guard Prog.run (runFirst exOnce) = .some 1

def exSplitNone : Prog [] (Option (Nat × Prog [NonDet] Nat)) :=
  msplit (fail (effs := [NonDet]))

#guard Prog.run exSplitNone = none

def exSplitOne : Prog [] (Option (Nat × Prog [NonDet] Nat)) :=
  msplit (pure 7)

#guard
  match Prog.run exSplitOne with
  | some (7, rest) => Prog.run (runList rest) = []
  | _ => false

def exSplitBoth : Prog [] (Option (Nat × Prog [NonDet] Nat)) :=
  msplit (pure 1 ?? pure 2 ?? fail ?? pure 3)

#guard
  match Prog.run exSplitBoth with
  | some (1, rest) => Prog.run (runList rest) = [2, 3]
  | _ => false

def exSplitOnce : Prog [] (Option (Nat × Prog [NonDet] Nat)) :=
  msplit (once (pure 1 ?? pure 2))

#guard
  match Prog.run exSplitOnce with
  | some (1, rest) => Prog.run (runList rest) = []
  | _ => false

def exStateNonDet : Prog [NonDet, State Nat] Nat := do
  let n ← State.get
  NonDet.choice
    (pure n)
    (do
      State.put (n + 1)
      State.get)

#guard Prog.run (State.run 0 (NonDet.runList exStateNonDet)) = (1, [0, 1])

def exStateNonDetSplit : Prog [State Nat] (Option (Nat × Prog [NonDet, State Nat] Nat)) :=
  msplit exStateNonDet

#guard
  match Prog.run (State.run 0 exStateNonDetSplit) with
  | (0, some (0, rest)) => Prog.run (State.run 0 (NonDet.runList rest)) = (1, [1])
  | _ => false

end Examples
