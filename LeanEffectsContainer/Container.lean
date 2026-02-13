universe u v w

structure Container : Type (max u v + 1)  where
  shape : Type u
  pos : shape → Type v

namespace Container

structure Extension (C : Container.{u, v}) (A : Type w) : Type (max u v w) where
  shape : C.shape
  point : C.pos shape → A

scoped notation "⟦" C "⟧" => Extension C
scoped notation s " ▷ " p => Container.mk s p

instance (C : Container.{u, v}) : Functor ⟦ C ⟧ where
  map {α β : Type u} (f : α → β) (ca : ⟦C⟧ α) : ⟦C⟧ β :=
    ⟨ca.shape, f ∘ ca.point⟩

instance (C : Container) : LawfulFunctor ⟦ C ⟧ where
  map_const := by simp only [Functor.mapConst, Functor.map, implies_true]

  id_map := by intro _ y; simp only [Functor.map, Function.id_comp]

  comp_map := by intro _ _ _ g h; simp [Functor.map]; intro _; rfl

def coproduct (C C' : Container) := (C.shape ⊕ C'.shape) ▷ Sum.elim C.pos C'.pos

def void : Container where
  shape := Empty
  pos := nofun

def sum : List Container → Container := List.foldr coproduct void

inductive Free (ops : List Container) (A : Type) : Type where
  | pure : A → Free ops A
  | impure : ⟦sum ops⟧ (Free ops A) → Free ops A

export Free (pure impure)

class inductive Member {A : Type u} (x : A) : List A → Type u where
  | here {xs} : Member x (x :: xs)
  | there {y xs} : Member x xs → Member x (y :: xs)

export Member (here there)

instance (priority := high) {A : Type u} {x : A} {xs} : Member x (x :: xs) := .here
instance (priority := low) {A : Type u} {y x : A} {xs} [m : Member x xs] : Member x (y :: xs) := .there m

notation (priority := high) x " ∈ " xs:50 => Member x xs

section

variable
  {C : Container}
  {A : Type u}

def inject {ops : List Container} : C ∈ ops → ⟦C⟧ A → ⟦sum ops⟧ A
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

def project {ops : List Container} : C ∈ ops → ⟦sum ops⟧ A → Option (⟦C⟧ A)
 | here, ⟨.inl s, pf⟩ => some ⟨s, pf⟩
 | here, ⟨.inr _, _⟩ => none
 | there _, ⟨.inl _, _⟩ => none
 | there p, ⟨.inr s, pf⟩ => project p ⟨s, pf⟩

end

section

variable
  {C : Container}
  {A : Type}
  {ops : List Container}
  [p : C ∈ ops]

def inj : ⟦C⟧ (Free ops A) → Free ops A := impure ∘ inject p

def prj : Free ops A → Option (⟦C⟧ (Free ops A))
  | pure _ => none
  | impure x => project p x

def op (s : C.shape) : Free ops (C.pos s) := inj ⟨s, pure⟩

def upcast : Free ops A → Free (C :: ops) A
  | pure x => pure x
  | impure ⟨s, k⟩ => impure ⟨.inr s, fun x => upcast (k x)⟩

end

def Free.map {F : List Container} {α β : Type} (f : α → β) : Free F α → Free F β
    | pure x => pure (f x)
    | impure ⟨s, pf⟩ => impure ⟨s, fun x => map f (pf x)⟩

instance {F : List Container} : Functor (Free F) where
  map := Free.map

end Container
