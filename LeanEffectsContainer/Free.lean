import LeanEffectsContainer.Container

open scoped Container

inductive Free (ops : List Container) (α : Type) : Type where
  | pure : α → Free ops α
  | impure : ⟦Container.sum ops⟧ (Free ops α) → Free ops α

export Free (pure impure)

namespace Free

/--
To prove a property `motive t` for all `t : Free ops α` you must provide:

* hPure - base case if `t` is a pure value
* hImpure - If `t` is an impure node with shape `s` and continuation `k` then:
     - Assume the property holds for every continuation branch `k p`
     - Prove the property for the impure node impure ⟨s, k⟩
-/
@[elab_as_elim] def induction
  {ops : List Container}
  {α : Type}
  {motive : Free ops α → Prop}
  (hPure : ∀ a, motive (pure a))
  (hImpure : ∀ e, (∀ p, motive (e.point p)) → motive (impure e))
  : ∀ t : Free ops α, motive t :=
  Free.rec
    (motive_1 := motive)
    (motive_2 := fun ⟨_, k⟩ => ∀ p, motive (k p))
    (pure := hPure)
    (impure := hImpure)
    (mk := fun _ _ ih => ih)

/--
To prove two impure nodes are equal, it is enough to prove their continuation
functions are pointwise equal on all positions.
-/
theorem impure_ext
  {ops : List Container}
  {α : Type}
  {s : (Container.sum ops).shape}
  {k₁ k₂ : (Container.sum ops).pos s → Free ops α}
  (h : ∀ p, k₁ p = k₂ p)
  : impure ⟨s, k₁⟩ = impure ⟨s, k₂⟩ := by
  apply congrArg (fun k => impure ⟨s, k⟩)
  funext p
  exact h p

section

variable
  {C : Container}
  {α : Type}
  {ops : List Container}
  [p : C ∈ ops]

def inj : ⟦C⟧ (Free ops α) → Free ops α := impure ∘ Container.inject p

def prj : Free ops α → Option (⟦C⟧ (Free ops α))
  | pure _ => none
  | impure x => Container.project p x

def op (s : C.shape) : Free ops (C.pos s) := inj ⟨s, pure⟩

def upcast : Free ops α → Free (C :: ops) α
  | pure x => pure x
  | impure ⟨s, k⟩ => impure ⟨.inr s, fun x => upcast (k x)⟩

end

def Free.map {F : List Container} {α β : Type} (f : α → β) : Free F α → Free F β
  | pure x => pure (f x)
  | impure ⟨s, pf⟩ => impure ⟨s, fun x => Free.map f (pf x)⟩

def Free.bind {F : List Container} {α β : Type} : Free F α → (α → Free F β) → Free F β
  | pure x, k => k x
  | impure ⟨s, pf⟩, k => impure ⟨s, fun x => Free.bind (pf x) k⟩

def Free.seq {F : List Container} {α β : Type} : Free F (α → β) → (Unit → Free F α) → Free F β
  | pure f, ma => Free.map f (ma ())
  | impure ⟨s, f⟩, ma => impure ⟨s, fun x => Free.seq (f x) ma⟩

instance {F : List Container} : Functor (Free F) where
  map := Free.map

instance {F : List Container} : Applicative (Free F) where
  pure := Free.pure
  seq := Free.seq

instance {F : List Container} : Monad (Free F) where
  bind := Free.bind

instance {F : List Container} {α β : Type} : HAndThen (Free F α) (Free F β) (Free F β) where
  hAndThen (ma : Free F α) (mb : Unit → Free F β) : Free F β := ma >>= (fun _ => mb ())

-- TODO: Add Lawful instances

def run {α : Type} : Free [] α → α
  | pure x => x

end Free
