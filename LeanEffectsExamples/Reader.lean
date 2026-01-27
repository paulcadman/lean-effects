import LeanEffects

namespace ReaderExample

open Reader
open Program

def addEnv [Member (Reader Nat) es] : Program es Nat := do
  let r ← ask
  let r' ← ask
  ret (r + r')

#guard Program.run (run 10 addEnv) = 20

end ReaderExample
