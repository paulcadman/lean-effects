import LeanEffects

namespace ReaderExample

open Reader

def addEnv [Member (Reader Nat) es] : Program es Nat := do
  let r ← ask
  let r' ← localEnv (fun _ => r + 30) ask
  let r'' ← ask
  pure (r + r' + r'')

#guard Program.run (Reader.run 10 addEnv) = 60

end ReaderExample
