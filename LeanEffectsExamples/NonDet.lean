import LeanEffects

namespace NonDetExample

open Program

def p [Member NonDet es] : Program es Nat := do
  let x ← NonDet.choose2 (.pure 1) (.pure 2)
  let y ← NonDet.choose2 (.pure 10) (.pure 20)
  let z ← NonDet.choose2 NonDet.empty (.pure 3)
  .pure (x + y + z)

#guard Program.run (NonDet.runViaList p) == [14, 24, 15, 25]

#guard Program.run (NonDet.runViaOption p) == some 14

def pFails [Member NonDet es] : Program es Nat := do
  let x ← NonDet.choose2 (.pure 1) (.pure 2)
  let y ← NonDet.empty
  .pure (x + y)

#guard Program.run (NonDet.runViaList pFails) == []

#guard Program.run (NonDet.runViaOption pFails) == none

end NonDetExample
