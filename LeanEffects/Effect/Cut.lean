import LeanEffects.Program
import LeanEffects.Effect.NonDet

-- The cutfail operation immediately ends the search with failure,
-- dropping all extant unexplored branches
inductive Cut : Type → Type where
  | cutfailOp : Cut α

namespace Cut

def cutfail [Member Cut es] : Program es α :=
  .perform Cut.cutfailOp

def call
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

mutual

def cut
  [Member NonDet es]
  [Member Cut es]
  : Program es PUnit :=
    NonDet.choose2 skip cutfail

def skip
  [Monad m]
  : m PUnit :=
    pure PUnit.unit
end

-- Once commits to the first solution that's found in `p`
def once
  [Member NonDet es]
  (p : Program (Cut :: es) α)
  : Program es α :=
    call do
      let x ← p
      cut
      pure x

end Cut
