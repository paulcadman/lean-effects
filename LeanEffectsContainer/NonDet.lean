import LeanEffectsContainer.Free

open scoped Container

inductive NonDetOps where
  | choiceOp
  | failOp

def NonDet : Container where
  shape := NonDetOps
  pos := fun
    | .choiceOp => Bool
    | .failOp => Empty

namespace NonDet

section

variable
{ops : List Container}
[NonDet ∈ ops]
{α : Type}

def choice (p : Free ops α) (q : Free ops α) : Free ops α := do
  let choose
    | true => p
    | false => q
  Free.inj (ops:=ops) (C:=NonDet) ⟨.choiceOp, choose⟩

scoped notation p " ?? " q => choice p q

def fail : Free ops α := do
  Free.inj (ops:=ops) (C:=NonDet) ⟨.failOp, fun e => nomatch e⟩

end

section

variable
{ops : List Container}
{α : Type}

def run : Free (NonDet :: ops) α → Free ops (List α)
  | .pure x => .pure [x]
  | .impure ⟨s, k⟩ =>
    match s with
    | .inl .failOp => .pure []
    | .inl .choiceOp => do
      let ls ← k true |> run
      let rs ← k false |> run
      .pure (ls ++ rs)
    | .inr s => .impure ⟨s, fun p => run (k p)⟩

theorem bind_fail {β : Type} {k : α → Free (NonDet :: ops) β} : run (fail >>= k) = run fail := rfl

theorem run_fail_is_empty : run (ops:=ops) (α:=α) fail = .pure [] := by
  simp only [fail, Free.inj, Container.inject, Function.comp_apply]
  rfl

theorem pure_append_nil_left_id (x : Free ops (List α)) : Free.pure List.append <*> Free.pure [] <*> x = x := by
  calc
    Free.pure List.append <*> Free.pure [] <*> x
      = List.append <$> Free.pure [] <*> x := rfl
    _ = Free.pure (List.append []) <*> x := rfl
    _ = List.append [] <$> x := rfl
    _ = id <$> x := rfl
    _ = x := id_map x

theorem run_fail_choice {q : Free (NonDet :: ops) α} :
    run (fail ?? q) = Free.pure List.append <*> run fail <*> run q := by
  calc
    run (fail ?? q) = run q := by
      simp [choice, fail, run, Free.inj, Container.inject]
    _ = Free.pure List.append <*> run fail <*> run q := by
      rw [run_fail_is_empty]
      symm
      exact pure_append_nil_left_id (run q)

theorem choice_ident_left_id {q : Free (NonDet :: ops) α} : run (fail ?? q) = run q := by
  calc
    run (fail ?? q) = List.append <$> run fail <*> run q := run_fail_choice
    _ = List.append <$> Free.pure [] <*> run q := rfl
    _ = Free.pure (fun x => List.append [] x) <*> run q := rfl
    _ = (fun x => List.append [] x) <$> run q := rfl
    _ = id <$> run q := by rfl
    _ = run q := id_map (run q)

theorem run_choice_right_fail {p : Free (NonDet :: ops) α} 
  : run (p ?? fail) = List.append <$> run p <*> Pure.pure [] := by
  simp [choice, fail, run, Free.inj, Container.inject]

theorem choice_ident_right_id {p : Free (NonDet :: ops) α} 
  : run (p ?? fail) = run p := by
  calc
    run (p ?? fail) = List.append <$> run p <*> pure [] := run_choice_right_fail
    _ = pure (fun x => x []) <*> (List.append <$> run p) := Free.interchange
    _ = (fun x => x []) <$> List.append <$> run p := by rfl
    _ = ((fun x => x []) ∘ List.append) <$> run p := by rw [LawfulFunctor.comp_map]
    _ = (fun x => x ++ []) <$> run p := by rfl
    _ = id <$> run p := by congr; funext x; exact List.append_nil x
    _ = run p := id_map (run p)

end

section Examples

def exOne : Free [NonDet] Nat :=
  choice (.pure 1) fail

def exOneResults : List Nat :=
  Free.run (run exOne)

#guard exOneResults = [1]

def exBoth : Free [NonDet] Nat :=
  choice (.pure 1) (.pure 2)

def exBothResults : List Nat :=
  Free.run (run exBoth)

#guard exBothResults = [1, 2]

end Examples

end NonDet
