universe uC vC u v

structure Container : Type (max uC vC + 1)  where
  shape : Type uC
  pos : shape → Type vC

namespace Container

structure Extension (C : Container.{uC, vC}) (α : Type u) : Type (max uC vC u) where
  shape : C.shape
  point : C.pos shape → α

scoped notation "⟦" C "⟧ " => Extension C
scoped notation s " ▷ " p => Container.mk s p

instance (C : Container.{uC, vC}) : Functor ⟦ C ⟧ where
  map {α β : Type u} (f : α → β) (ca : ⟦C⟧ α) : ⟦C⟧ β :=
    ⟨ca.shape, f ∘ ca.point⟩

instance (C : Container) : LawfulFunctor ⟦ C ⟧ where
  map_const := by simp only [Functor.mapConst, Functor.map, implies_true]

  id_map := by intro _ y; simp only [Functor.map, Function.id_comp]

  comp_map := by intro _ _ _ g h; simp [Functor.map]; intro _; rfl

def coproduct (C C' : Container) := (C.shape ⊕ C'.shape) ▷ Sum.elim C.pos C'.pos

def void : Container.{uC, vC} where
  shape := ULift.{uC, 0} Empty
  pos := nofun

def sum : List Container.{uC, vC} → Container.{uC, vC} := List.foldr coproduct void

class inductive Member {α : Type u} (x : α) : List α → Type u where
  | here {xs} : Member x (x :: xs)
  | there {y xs} : Member x xs → Member x (y :: xs)

export Member (here there)

instance (priority := high) {α : Type u} {x : α} {xs} : Member x (x :: xs) := .here
instance (priority := low) {α : Type u} {y x : α} {xs} [m : Member x xs] : Member x (y :: xs) := .there m
scoped notation (priority := high) x " ∈ " xs:50 => Member x xs

section

variable
  {C : Container.{uC, vC}}
  {α : Type v}

def inject {ops : List Container.{uC, vC}} : C ∈ ops → ⟦C⟧ α → ⟦sum ops⟧ α
  | here, ⟨s, pf⟩ => ⟨.inl s , pf⟩
  | there m, prog =>
      match inject m prog with
      | ⟨s, p⟩ => by
          -- ⟨.inr s, p⟩ is enough, but for pedagogical reasons we keep the step by step definition
          refine ⟨.inr s, ?_⟩
          unfold sum; simp only [List.foldr]
          unfold coproduct; simp only [Sum.elim]
          unfold sum coproduct at p
          exact p

def project {ops : List Container.{uC, vC}} : C ∈ ops → ⟦sum ops⟧ α → Option (⟦C⟧ α)
 | here, ⟨.inl s, pf⟩ => some ⟨s, pf⟩
 | here, ⟨.inr _, _⟩ => none
 | there _, ⟨.inl _, _⟩ => none
 | there p, ⟨.inr s, pf⟩ => project p ⟨s, pf⟩

end

end Container

section List

open Container

abbrev ListContainer : Container where
  shape := Nat
  pos := Fin

def list_3_int : ⟦ ListContainer ⟧ Int where
  shape := 3
  point := fun _ => 0

abbrev OptionContainer : Container where
  shape := Bool
  pos
    | true => Unit
    | false => Empty

def just_int : ⟦ OptionContainer ⟧ Int where
  shape := true
  point := fun _ => 3

def nothing_int : ⟦ OptionContainer ⟧ Int where
  shape := false
  point := nofun

end List
