structure Container : Type 1 where
  shape : Type
  pos : shape → Type

namespace Container

abbrev extension (C : Container) (A : Type) : Type :=
  Σ x : C.shape, C.pos x → A

scoped notation "⟦" C "⟧" => extension C
scoped notation s "▷" p => Container.mk s p

instance (C : Container) : Functor ⟦ C ⟧ where
  map {α β : Type} (f : α → β) (ca : ⟦C⟧ α) : ⟦C⟧ β :=
    ⟨ca.fst, f ∘ ca.snd⟩

instance (C : Container) : LawfulFunctor ⟦ C ⟧ where
  map_const := by simp only [Functor.mapConst, Functor.map, implies_true]

  id_map := by intro _ y; simp only [Functor.map, Function.id_comp]

  comp_map := by intro _ _ _ g h; simp [Functor.map]; intro _; rfl

def coproduct (C C' : Container) := (C.shape ⊕ C'.shape) ▷ Sum.elim C.pos C'.pos

def void : Container where
  shape := Empty
  pos := nofun

def sum : List Container → Container := List.foldr coproduct void

end Container

open scoped Container

inductive Free (C : Container) (A : Type) : Type where
  | pure : A → Free C A
  | impure : (Σ x : C.shape, C.pos x → Free C A) → Free C A

universe u

inductive Member {A : Type u} (x : A) : List A → Type u where
  | here {xs} : Member x (x :: xs)
  | there {y xs} : Member x xs → Member x (y :: xs)
