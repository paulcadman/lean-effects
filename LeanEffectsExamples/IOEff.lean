import LeanEffects

namespace IOEffExample

variable {es : List Effect}

open Program
open IOEff
open Reader

def prog [Member IOEff es] [Member (Reader Nat) es] : Program es Nat := do
  let r ← embed (IO.mkRef 0)
  let n ← ask
  embed (r.set n)
  embed r.get

/--
info: 10
-/
#guard_msgs in
#eval (IOEff.run (Reader.run 10 prog))

end IOEffExample
