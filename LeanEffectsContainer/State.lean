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

section SmartConstructor

variable
  [State S ∈ ops]

def get : Free ops S := Free.op (C:=State _) StateOps.getOp

def put (s : S) : Free ops Unit := Free.op (C:=State _) (StateOps.putOp s)

end SmartConstructor

def run (s : S) : Free (State S :: ops) α → Free ops (S × α)
  | .pure x => .pure (s, x)
  | .impure ⟨sh, k⟩ => match sh with
    | .inl op => match op with
      | .getOp => run s (k s)
      | .putOp s' => run s' (k .unit)
    | .inr sh => .impure ⟨sh, fun p => run s (k p)⟩

def eval (s : S) (p : Free (State S :: ops) α) : Free ops α := Prod.snd <$> run s p

section Examples

def tick {ops} [State Nat ∈ ops] : Free ops Unit := do
  let i ← get
  put (1 + i)


#guard Free.run (State.run 0 (do tick; tick)) = (2, Unit.unit)

end Examples

end State
