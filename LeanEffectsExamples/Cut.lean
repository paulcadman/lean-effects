import LeanEffects

def exNondet : List Nat :=
  NonDet.choose2 (pure 1) (pure 2)
  |> NonDet.runViaList
  |> Program.run

#guard exNondet == [1, 2]

def exOnce : List Nat :=
  NonDet.choose2 (pure 1) (pure 2)
  |> Cut.once
  |> NonDet.runViaList
  |> Program.run

#guard exOnce == [1]

def exCutFail : List Nat :=
  Cut.call (do
    let x ← NonDet.choose2 (pure 1) (pure 2)
    Cut.cutfail
    pure x)
  |> NonDet.runViaList
  |> Program.run

#guard exCutFail == []
