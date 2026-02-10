import LeanEffects.Program
import LeanEffects.Effect.NonDet

universe u
variable {es : List Effect}

-- The cutfail operation immediately ends the search with failure,
-- dropping all extant unexplored branches
inductive Cut : Type → Type where
  | cutfailOp {α : Type} : Cut α

inductive Call : Type → Type where
  | callBeginOp : Call PUnit
  | callEndOp : Call PUnit

namespace Call

def begin_ [Member Call es] : Program es PUnit :=
  .perform Call.callBeginOp

def end_ [Member Call es] : Program es PUnit :=
  .perform Call.callEndOp

def call'
  {α : Type}
  [Member Call es]
  (p : Program es α) : Program es α := do
    begin_
    let x ← p
    end_
    pure x

end Call

namespace Cut

def cutfail {α : Type} [Member Cut es] : Program es α :=
  .perform Cut.cutfailOp

def call
  {α : Type u}
  [Member NonDet es]
  (p : Program (Cut :: es) α)
  : Program es α :=
  let rec go : Program (Cut :: es) α → Program es α → Program es α
    | .ret a, q => NonDet.choose2 (Program.ret a) q
    | .op h k, q =>
        match h with
        | HSum.here Cut.cutfailOp => NonDet.fail
        | HSum.there h' =>
            match (Member.prj (e:=NonDet) h') with
            | some NonDet.failOp => q
            | some NonDet.chooseOp =>
                go (k Choice.left) (go (k Choice.right) q)
            | none =>
                Program.op h' (fun x => go (k x) q)
  go p NonDet.fail

partial def ecall
  {α : Type u}
  [Inhabited α]
  [Member NonDet es]
  : Program (Call :: Cut :: es) α → Program (Cut :: es) (Program (Call :: Cut :: es) α)
  | .ret a => Program.ret (.ret a)
  | .op h k =>
    match h with
    | HSum.here Call.callBeginOp =>
        let p' := k PUnit.unit
        Program.bind
          (Program.upcast (e:=Cut) (call (ecall p')))
          (fun q => ecall q)
    | HSum.here Call.callEndOp => Program.ret (k PUnit.unit)
    | HSum.there h' => Program.op h' (fun x => ecall (k x))

partial def bcall
  {α : Type u}
  [Inhabited α]
  [Member NonDet es]
  : Program (Call :: Cut :: es) α → Program (Cut :: es) α
  | .ret a => Program.ret a
  | .op h k =>
    match h with
    | HSum.here Call.callBeginOp =>
        let p' := k PUnit.unit
        Program.bind
            (Program.upcast (e:=Cut) (call (ecall p')))
            (fun q => bcall q)
    | HSum.here Call.callEndOp => panic! "Mismatched ECall"
    | HSum.there h' => Program.op h' (fun x => bcall (k x))

def runCut
  {α : Type u}
  [Inhabited α]
  [Member NonDet es]
  (p : Program (Call :: Cut :: es) α) : Program es α :=
   bcall p |> call

mutual

def cut
  [Member NonDet es]
  [Member Cut es]
  : Program es PUnit :=
    NonDet.choose2 skip cutfail

def skip
  {m : Type → Type 1}
  [Monad m]
  : m PUnit :=
    pure PUnit.unit

end

-- Once commits to the first solution that's found in `p`
def once
  {α : Type}
  [Member NonDet es]
  (p : Program (Cut :: es) α)
  : Program es α :=
    call do
      let x ← p
      cut
      pure x

end Cut
