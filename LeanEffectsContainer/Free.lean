import LeanEffectsContainer.Container

open scoped Container

inductive Free (ops : List Container) (α : Type) : Type where
  | pure : α → Free ops α
  | impure : ⟦Container.sum ops⟧ (Free ops α) → Free ops α

export Free (pure impure)

namespace Free

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
