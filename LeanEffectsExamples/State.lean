import LeanEffects

namespace StateExample

open State
open Reader
open Program

def tick [Member (State Nat) es] : Program es PUnit := do
  let n ← get
  put (n + 1)

#guard Program.run (State.run 0 (do tick; tick)) = (2, PUnit.unit)

def appendBang [Member (State String) es] : Program es PUnit := do
  let s ← get
  put (s ++ "!")

def combination
  [Member (State Nat) es]
  [Member (State String) es]
  [Member (Reader Nat) es]
  : Program es Nat := do
  tick
  appendBang
  let n ← get
  let (s : String) ← get
  put (n + s.length)
  let m ← ask
  let n' ← get
  pure (m + n')

def runCombination1 : String × Nat × Nat :=
  combination
  |> State.run 0
  |> State.run "x"
  |> Reader.run 4
  |> Program.run

#guard runCombination1 = ("x!", 3, 7)

def runCombination2 : Nat × String × Nat :=
  combination (es := [State String, State Nat, Reader Nat])
  |> State.run "x"
  |> State.run 0
  |> Reader.run 5
  |> Program.run

#guard runCombination2 = (3, "x!", 8)

end StateExample
