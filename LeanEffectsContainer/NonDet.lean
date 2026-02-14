import LeanEffectsContainer.Free

open scoped Container

inductive NonDetOps : Type where
  | choiceOp : NonDetOps
  | failOp : NonDetOps

def NonDet : Container :=
  let pos := fun
    | .choiceOp => Bool
    | .failOp => Empty
  NonDetOps ▷ pos

namespace NonDet

variable
  (ops : List Container)
  [NonDet ∈ ops]
  (α : Type)

def choice (p : Free ops α) (q : Free ops α) : Free ops α := do
  let b : Bool ← Free.op (C:=NonDet) NonDetOps.choiceOp
  if b then p else q

scoped notation p "??" q => choice p q

def fail : Free ops α := do
  let x ← Free.op (C:=NonDet) NonDetOps.failOp
  nomatch x

end NonDet
