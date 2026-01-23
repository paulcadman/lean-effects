import LeanEffects

namespace LoggerExample

open Logger
open State

def ex [Member Logger es] [Member (State Nat) es]: Program es Nat := do
  log "log1"
  let n ← get
  put (n + 1)
  log "log2"
  get

def result : List String × Nat :=
  ex |> State.eval 0 |> Logger.runViaState |> State.run [] |> Program.run

#guard result = (["log1", "log2"], 1)

end LoggerExample
