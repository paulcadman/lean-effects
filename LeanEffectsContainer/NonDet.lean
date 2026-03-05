import LeanEffectsContainer.Exception
import LeanEffectsContainer.IOEff
import LeanEffectsContainer.NonDet.PStream
import LeanEffectsContainer.Prog
import LeanEffectsContainer.State

open scoped Container

universe u

inductive NonDetOps : Type 1 where
  | choiceOp
  | failOp

inductive NonDetScps : Type 1 where
  | once

def NonDetOpsC : Container.{1, 0} where
  shape := NonDetOps
  pos := fun
    | NonDetOps.choiceOp => Bool
    | NonDetOps.failOp => Empty

def NonDetScpsC : Container.{1, 0} where
  shape := NonDetScps
  pos := fun
    | NonDetScps.once => Unit

def NonDet : Effect where
  ops := NonDetOpsC
  scps := NonDetScpsC

namespace NonDet

variable
  {effs : List Effect}

section SmartConstructor

variable
  [m : NonDet ∈ effs]

def choiceBool : Prog effs Bool :=
  opEff (e:=NonDet) ⟨NonDetOps.choiceOp, fun b => Prog.var b⟩

variable
  {α : Type u}

def choice (p : Prog effs α) (q : Prog effs α) : Prog effs α :=
  Prog.bind choiceBool (fun b => if b then p else q)

scoped notation p " ?? " q => choice p q

def fail : Prog effs α :=
  opEff (e:=NonDet) ⟨NonDetOps.failOp, fun e => nomatch e⟩

def once (p : Prog effs α) : Prog effs α :=
  scpEff (e:=NonDet) ⟨NonDetScps.once, fun _ => ProgN.varS p⟩

def reflectM (p : Prog effs (Option (α × Prog effs α))) : Prog effs α :=
  Prog.bind p (fun
    | none => fail
    | some (x, rest) => choice (α := α) (pure x) rest)

def msplit : Prog effs α → Prog effs (Option (α × Prog effs α)) :=
  Prog.foldP
    (P := fun _ => Prog effs (Option (α × Prog effs α)))
    (var0 := fun x => pure (some (x, fail)))
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match Container.project (opsMem m) ⟨c, k⟩ with
      | some ⟨.choiceOp, k'⟩ => do
          let l ← k' true
          match l with
          | some (x, rest) =>
              pure (some (x, choice (α := α) rest (reflectM (effs := effs) (k' false))))
          | none => k' false
      | some ⟨.failOp, _⟩ => pure none
      | none => Prog.op ⟨c, k⟩)
    (scp := fun ⟨c, k⟩ =>
      match Container.project (scpsMem m) ⟨c, k⟩ with
      | some ⟨.once, k'⟩ => do
          let r ← k' PUnit.unit
          match r with
          | some (x, _) => pure (some (x, fail))
          | none => pure none
      | none => Prog.scp ⟨c, fun p => ProgN.varS (k p)⟩)

end SmartConstructor

variable
  {α : Type u}

def runList :
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
        let xs ← k ()
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
      | .inl .once => k ()
      | .inr s => Prog.scp ⟨s, (fun p => ProgN.varS (k p))⟩)

def runPStream :
    Prog (NonDet :: effs) α → Prog effs (PStream effs α) :=
  Prog.foldP
    (P := fun _ => Prog effs (PStream effs α))
    (var0 := fun x => pure (PStream.singleton x))
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl .choiceOp => do
          let l ← k true
          pure (PStream.append l (fun _ => PStream.squash (fun _ => k false)))
      | .inl .failOp => pure PStream.nil
      | .inr s => Prog.op ⟨s, k⟩)
    (fun ⟨c, k⟩ =>
      match c with
      | .inl .once => do
          let xs ← k ()
          let h ← PStream.uncons xs
          match h with
          | none => pure PStream.nil
          | some (x, _) => pure (PStream.singleton x)
      | .inr s => Prog.scp ⟨s, (fun p => ProgN.varS (k p))⟩)

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

def exBothIO : Prog [NonDet, IOEff] Nat :=
  (do
    IOEff.embed (IO.println "head")
    pure 1)
  ??
  (do
    IOEff.embed (IO.println "tail")
    pure 2)

def gBothIO : Prog [IOEff] (List Nat) :=
  Prog.bind (runPStream exBothIO) PStream.force

/--
info: head
tail
---
info: [1, 2]
-/
#guard_msgs in
#eval IOEff.run gBothIO

def exOnceIO : Prog [NonDet, IOEff] Nat :=
  once exBothIO

def gOnceIO : Prog [IOEff] (List Nat) :=
  Prog.bind (runPStream exOnceIO) PStream.force

/--
info: head
---
info: [1]
-/
#guard_msgs in
#eval IOEff.run gOnceIO

def exSplitNone : Prog [NonDet] (Option (Nat × Prog [NonDet] Nat)) :=
  msplit fail

#guard
  match Prog.run (runFirst exSplitNone) with
  | some none => true
  | _ => false

def exSplitOne : Prog [NonDet] (Option (Nat × Prog [NonDet] Nat)) :=
  msplit (pure 7)

#guard
  match Prog.run (runFirst exSplitOne) with
  | some (some (7, rest)) => Prog.run (runList rest) = []
  | _ => false

def exSplitBoth : Prog [NonDet] (Option (Nat × Prog [NonDet] Nat)) :=
  msplit (pure 1 ?? pure 2 ?? fail ?? pure 3)

#guard
  match Prog.run (runFirst exSplitBoth) with
  | some (some (1, rest)) => Prog.run (runList rest) = [2, 3]
  | _ => false

def exSplitOnce : Prog [NonDet] (Option (Nat × Prog [NonDet] Nat)) :=
  msplit (once (pure 1 ?? pure 2))

#guard
  match Prog.run (runFirst exSplitOnce) with
  | some (some (1, rest)) => Prog.run (runList rest) = []
  | _ => false

def exStateNonDet : Prog [NonDet, State Nat] Nat := do
  let n ← State.get
  NonDet.choice
    (pure n)
    (do
      State.put (n + 1)
      State.get)

#guard Prog.run (State.run 0 (NonDet.runList exStateNonDet)) = (1, [0, 1])

def exStateNonDetSplit : Prog [NonDet, State Nat] (Option (Nat × Prog [NonDet, State Nat] Nat)) :=
  msplit exStateNonDet

#guard
  match Prog.run (State.run 0 (runFirst exStateNonDetSplit)) with
  | (0, some (some (0, rest))) => Prog.run (State.run 0 (NonDet.runList rest)) = (1, [1])
  | _ => false

def exSplitNonHead : Prog [State Nat, NonDet] (Option (Nat × Prog [State Nat, NonDet] Nat)) :=
  Prog.bind State.get (fun n =>
    msplit (NonDet.choice
      (pure n)
      (do
        State.put (n + 1)
        State.get)))

#guard
  match Prog.run (NonDet.runFirst (effs := []) (State.run 0 exSplitNonHead)) with
  | some (0, some (0, _)) => true
  | _ => false

open Exception

def action1 {eff}
  [NonDet ∈ eff]
  [Exception Unit ∈ eff] :
  Prog eff Bool := catchE (pure true ?? throwE ()) (fun () => pure false)

def action2 {eff}
  [NonDet ∈ eff]
  [Exception Unit ∈ eff] :
  Prog eff Bool := catchE (throwE () ?? pure true) (fun () => pure false)


#guard Prog.run (NonDet.runList (Exception.run (E:=Unit) action1)) = [.ok true, .ok false]
#guard Prog.run (Exception.run (E:=Unit) (NonDet.runList action1)) = .ok [false]

end Examples
