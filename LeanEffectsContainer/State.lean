import LeanEffectsContainer.Free

open scoped Container

inductive StateOps (S : Type) where
  | getOp
  | putOp : S → StateOps S

def State (S : Type) : Container where
  shape := StateOps S
  pos := fun
   | .getOp => S
   | .putOp _ => Unit

namespace State

variable
  {ops : List Container}
  {S α : Type}
  [State S ∈ ops]

def get : Free ops S := Free.op (C:=State _) StateOps.getOp

def put (s : S) : Free ops Unit := Free.op (C:=State _) (StateOps.putOp s)

def runState (s : S) : Free (State S :: ops) α → Free ops (S × α)
  | .pure x => .pure (s, x)
  | .impure ⟨sh, k⟩ => match sh with
    | .inl op => match op with
      | .getOp => runState s (k s)
      | .putOp s' => runState s' (k .unit)
    | .inr sh => .impure ⟨sh, fun p => runState s (k p)⟩

end State
