import LeanEffectsContainer.Free
import LeanEffectsContainer.Prog

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

section

universe u

variable
{effs : List Effect}
[NonDet ∈ effs]

def choiceBool : Prog effs Bool :=
  opEff (e:=NonDet) ⟨.choiceOp, fun b => Prog.var b⟩

def choice {α : Type} (p : Prog effs α) (q : Prog effs α) : Prog effs α := do
  let b ← choiceBool
  if b then p else q

scoped notation p " ?? " q => choice p q

def fail {α : Type} : Prog effs α :=
  opEff (e:=NonDet) ⟨.failOp, fun e => nomatch e⟩

def once {α : Type} (p : Prog effs α) : Prog effs α :=
  scpEff (e:=NonDet) ⟨.once, fun _ => ProgN.varS p⟩

def run {α : Type u} :
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

end

end NonDet

section Examples

open NonDet

def exOne : Prog [NonDet] Nat :=
  pure 1 ?? fail

def exOneResults : List Nat :=
  Prog.run (run exOne)

#guard Prog.run (run exOne) = [1]

def exBoth : Prog [NonDet] Nat :=
  pure 1 ?? pure 2

#guard Prog.run (run exBoth) = [1, 2]

def exOnce : Prog [NonDet] Nat :=
  once <| pure 1 ?? pure 2

#guard Prog.run (run exOnce) = [1]

end Examples
