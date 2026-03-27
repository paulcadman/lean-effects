import Effects

open scoped Container


namespace Tutorial

variable
  {m}
  [Monad m]
  {effs : List Effect}

namespace StateExample
  namespace Effects

    open State

    def tick [State Nat ∈ effs] : Prog effs Unit := do
      let n ← get
      put (n + 1)

    def tickTwice [State Nat ∈ effs] : Prog effs Nat := do
      tick
      tick
      get

    def tickTwiceResult : Nat :=
      tickTwice
      |> State.eval 0
      |> Prog.run

  end Effects

  namespace MTL

    def tick [MonadState Nat m] : m Unit := do
      modify (fun n => n + 1)

    def tickTwice [MonadState Nat m] : m Nat := do
      tick
      tick
      get

    def tickTwiceResult : Nat :=
      (tickTwice : StateM Nat Nat).run' 0

    end MTL

  #guard Effects.tickTwiceResult = 2
  #guard MTL.tickTwiceResult = 2

end StateExample

namespace ExceptStateComposition

  namespace Effects

    open State
    open Exception

    def decr
      [State Int ∈ effs]
      [Exception Unit ∈ effs]
      : Prog effs Unit := do
        let x ← get
        if x > (0 : Int) then
          put (x - 1)
        else
          throwE ()

    def tripleDecr
      [State Int ∈ effs]
      [Exception Unit ∈ effs]
      : Prog effs Unit := do
        decr
        catchE (do decr; decr) pure

    def stateThenExcept : Except Unit (Int × Unit) :=
      tripleDecr
      |> State.run 2
      |> Exception.run (E := Unit)
      |> Prog.run

    def exceptThenState : Int × Except Unit Unit :=
      tripleDecr
      |> Exception.run (E := Unit)
      |> State.run 2
      |> Prog.run

  end Effects

  namespace MTL
    def decr [MonadStateOf Int m] [MonadExcept Unit m] : m Unit := do
      let x ← get
      if x > 0 then
        set (x - 1)
      else
        throw ()

    def tripleDecr [MonadStateOf Int m] [MonadExcept Unit m] : m Unit := do
      decr
      tryCatch (do decr; decr) (fun _ => pure ())

    def stateThenExcept : Except Unit (Unit × Int) :=
      (tripleDecr : StateT Int (Except Unit) Unit).run 2

    def exceptThenState : Except Unit Unit × Int :=
      (tripleDecr : ExceptT Unit (StateM Int) Unit).run 2

  end MTL


  #guard MTL.stateThenExcept = .ok ((), 1)
  #guard Effects.stateThenExcept = .ok (1, ())

  #guard MTL.exceptThenState = (.ok (), 0)
  #guard Effects.exceptThenState = (0, .ok ())

end ExceptStateComposition

namespace ChooseWithStateExample

  namespace Effects

  open State
  open NonDet

  def chooseWithState
    [NonDet ∈ effs]
    [State Nat ∈ effs] :
    Prog effs Nat := do
      let n ← get
      choice
        (pure n)
        (do
          put (n + 1)
          get)

  def localState : List (Nat × Nat) :=
    chooseWithState
    |> State.run 0
    |> NonDet.runList
    |> Prog.run

  def globalState : Nat × List Nat :=
    chooseWithState
    |> NonDet.runList
    |> State.run 0
    |> Prog.run

  end Effects

  #guard Effects.localState = [(0, 0), (1, 1)]
  #guard Effects.globalState = (1, [0, 1])

end ChooseWithStateExample

end Tutorial
