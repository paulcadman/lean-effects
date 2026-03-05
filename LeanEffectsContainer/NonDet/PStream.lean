import Batteries.Data.MLList.Basic
import LeanEffectsContainer.Prog

universe u

abbrev PStream (effs : List Effect) (α : Type u) : Type (u + 1) :=
  MLList (Prog.{u + 1} effs) (ULift.{u + 1} α)

namespace PStream

variable
  {effs : List Effect}
  {α : Type u}

def nil : PStream effs α :=
  MLList.nil

def singleton (x : α) : PStream effs α :=
  MLList.singleton (ULift.up x)

def squash (k : Unit → Prog effs (PStream effs α)) : PStream effs α :=
  MLList.squash k

def append (xs : PStream effs α) (ys : Unit → PStream effs α) : PStream effs α :=
  MLList.append xs ys

def uncons (xs : PStream effs α) : Prog effs (Option (α × PStream effs α)) := do
  let r ← MLList.uncons xs
  pure (r.map (fun ⟨head, tail⟩ => (head.down, tail)))

private def forceU (xs : PStream effs α) : Prog.{u + 1} effs (ULift.{u + 1} (List α)) := do
  let ys ← MLList.force xs
  pure (ULift.up (ys.map ULift.down))

def force (xs : PStream effs α) : Prog effs (List α) :=
  Prog.bind (forceU xs) (fun ys => pure ys.down)

end PStream
