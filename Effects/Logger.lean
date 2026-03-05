import Effects.Prog
import Effects.State
import Effects.IOEff

open scoped Container

inductive LoggerOps : Type 1 where
  | logOp (msg : String)

def LoggerOpsC : Container where
  shape := LoggerOps
  pos
    | .logOp _ => Unit

def Logger : Effect where
  ops := LoggerOpsC
  scps := Container.void

namespace Logger

variable
  {effs : List Effect}

section SmartConstructors

def log [Logger ∈ effs] (msg : String) : Prog effs Unit :=
  opEff (e := Logger) ⟨.logOp msg, fun _ => Prog.var ()⟩

end SmartConstructors

variable
  {α : Type}

def runViaState :
  Prog (Logger :: effs) α → Prog (State (List String) :: effs) α :=
  Prog.reinterpret
    (handleOp := fun ⟨op, k⟩ =>
      match op with
      | .logOp msg => do
          let xs ← State.get
          State.put (xs ++ [msg])
          k ())
    (handleScp := fun ⟨c, _⟩ => nomatch c)

def runViaIO [IOEff ∈ effs] :
  Prog (Logger :: effs) α → Prog effs α :=
  Prog.foldP
    (P := fun _ => Prog effs α)
    (var0 := pure)
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl (.logOp msg) => do
          IOEff.embed (IO.println msg)
          k ()
      | .inr s => Prog.op ⟨s, k⟩)
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl scp => nomatch scp
      | .inr s => Prog.scp ⟨s, fun p => ProgN.varS (k p)⟩)

namespace Examples

open State (get put)

def exLogger
  {es}
  [Logger ∈ es]
  [State Nat ∈ es]
  : Prog es Nat := do
  log "log1"
  let n ← get
  put (n + 1)
  log "done"
  get

#guard
  (exLogger
  |> runViaState
  |> State.run []
  |> State.eval 1
  |> Prog.run)
  = (["log1", "done"], 2)

/--
info: log1
done
---
info: 2
-/
#guard_msgs in
#eval
  (exLogger
  |> runViaIO
  |> State.eval 1
  |> IOEff.run)

end Examples

end Logger
