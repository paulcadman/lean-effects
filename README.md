# lean-effects

`lean-effects` is an algebraic effects library for Lean that supports scoped effects.

The implementation is based on an [Agda library](https://github.com/JonasHoefer/scoped-effects-agda) by Jonas Höfer.

## Example:

```lean
import Effects

open scoped Container

open State

def tickTwice {effs : List Effect} [State Nat ∈ effs] : Prog effs Nat := do
  let n ← get
  put (n + 1)
  let n ← get
  put (n + 1)
  get

def ex : Nat :=
  tickTwice
  |> State.eval 0
  |> Prog.run

#guard ex = 2
```
