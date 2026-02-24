import LeanEffectsContainer.Container

open scoped Container

structure Effect : Type 1 where
  ops : Container
  scps : Container

def ops : List Effect → Container := Container.sum ∘ List.map Effect.ops

def scps : List Effect → Container := Container.sum ∘ List.map Effect.scps

-- inductive Prog (effs : List Effect) (α : Type) : Type where
--   | var : α → Prog effs α
--   | op : ⟦ ops effs ⟧ (Prog effs α) → Prog effs α
--   | scps : ⟦ scps effs ⟧ (Prog effs (Prog effs α)) → Prog effs α
