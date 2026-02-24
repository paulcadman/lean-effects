import LeanEffectsContainer.Container

open scoped Container

structure Effect : Type 1 where
  ops : Container
  scps : Container

def ops : List Effect → Container := Container.sum ∘ List.map Effect.ops

def scps : List Effect → Container := Container.sum ∘ List.map Effect.scps

inductive Prog (effs : List Effect) : Type → Type 1 where
  | var {α : Type} : α → Prog effs α
  | op {α : Type} (s : (ops effs).shape) :
    ((ops effs).pos s → Prog effs α) → Prog effs α
  | scp {α β : Type} (s : (scps effs).shape) :
    ((scps effs).pos s → Prog effs β) → (β → Prog effs α) → Prog effs α
