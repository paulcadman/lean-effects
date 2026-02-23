import LeanEffectsContainer.Container

open scoped Container

inductive Free (ops : List Container) (α : Type) : Type where
  | pure : α → Free ops α
  | impure : ⟦Container.sum ops⟧ (Free ops α) → Free ops α

export Free (impure)

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

def map {F : List Container} {α β : Type} (f : α → β) : Free F α → Free F β
  | pure x => pure (f x)
  | impure ⟨s, pf⟩ => impure ⟨s, fun x => map f (pf x)⟩

def bind {F : List Container} {α β : Type} : Free F α → (α → Free F β) → Free F β
  | pure x, k => k x
  | impure ⟨s, pf⟩, k => impure ⟨s, fun x => bind (pf x) k⟩

instance {F : List Container} : Functor (Free F) where
  map := map

def seq {F : List Container} {α β : Type} : Free F (α → β) → (Unit → Free F α) → Free F β
  | pure f, ma => Functor.map f (ma ())
  | impure ⟨s, f⟩, ma => impure ⟨s, fun x => seq (f x) ma⟩

instance {F : List Container} : Applicative (Free F) where
  pure := Free.pure
  seq := Free.seq

instance {F : List Container} : Monad (Free F) where
  bind := bind

instance {F : List Container} {α β : Type} : HAndThen (Free F α) (Free F β) (Free F β) where
  hAndThen (ma : Free F α) (mb : Unit → Free F β) : Free F β := ma >>= (fun _ => mb ())

instance {F : List Container} : LawfulFunctor (Free F) where
  map_const := by
    intro x y
    rfl

  id_map x := by
    refine induction ?_ ?_ x
    · intro
      rfl
    · intro _ ih
      exact impure_ext ih

  comp_map g h x := by
    refine induction ?_ ?_ x
    · intro
      rfl
    · intro _ ih
      exact impure_ext ih


instance {F : List Container} : LawfulApplicative (Free F) where
  seqLeft_eq x y := by rfl
  seqRight_eq x y := by rfl
  pure_seq g x := by rfl
  map_pure g x := by rfl
  seq_pure g := by
    intro x
    refine induction ?_ ?_ g
    · intro f
      rfl
    · intro _ ih
      exact impure_ext ih
  seq_assoc x g h := by
    refine induction ?_ ?_ h
    · intro f
      have hmapSeq : f <$> (g <*> x) = ((Function.comp f) <$> g) <*> x := by
        refine induction ?_ ?_ g
        · intro gfun
          exact (LawfulFunctor.comp_map (f:=Free F) (g:=gfun) (h:=f) (x:=x)).symm
        · intro _ ih
          exact impure_ext ih
      apply hmapSeq
    · intro _ ih
      exact impure_ext ih

-- Is @[simp] a good idea? probably not
@[simp] theorem pure_eq_pure {F : List Container} {α} {x : α} :
  (Free.pure x : Free F α) = Pure.pure x := rfl

instance {F : List Container} : LawfulMonad (Free F) where
  pure_bind {α β} (x : α) (f : α → Free F β)
    : Pure.pure x >>= f = f x := by simp [Bind.bind, bind]

  bind_assoc {α β γ} (x : Free F α) (f : α → Free F β) (g : β → Free F γ)
    : x >>= f >>= g = x >>= fun x => f x >>= g := by
    refine induction ?_ ?_ x
    · simp [Bind.bind, bind]
    · intro _ ih; apply impure_ext; apply ih

  bind_pure_comp {α β} (f : α → β) (x : Free F α)
    : x >>= (fun a => Pure.pure (f a)) = f <$> x := by
    refine induction ?_ ?_ x
    · simp [Bind.bind, bind]
    · intro _ ih; apply impure_ext; apply ih

  bind_map {α β} (f : Free F (α → β)) (x : Free F α)
    : f >>= (fun f' => f' <$> x) = f <*> x := by
    refine induction ?_ ?_ f
    · intro a; simp [Bind.bind, bind, pure_seq]
    · intro _ ih; apply impure_ext; apply ih

def run {α : Type} : Free [] α → α
  | pure x => x

theorem interchange {α β} {ops} {a} {f : Free ops (α → β)}
  : f <*> pure a = pure (fun x => x a) <*> f := match f with
  | pure f' => by rfl
  | impure ⟨s, k⟩ => by
    simp [Seq.seq, seq, Functor.map, map]; ext x
    simpa only [Functor.map, instApplicative] using seq_pure (g := k x) (x := a)

theorem interchange_ind {α β} {ops} {a} {f : Free ops (α → β)}
  : f <*> pure a = pure (fun x => x a) <*> f := by
  refine induction ?_ ?_ f
  · intro x; rfl
  · intro e ih
    exact impure_ext ih

theorem interchange_rec {α β} {ops} {a} {f : Free ops (α → β)}
  : f <*> pure a = pure (fun x => x a) <*> f := match f with
  | pure f' => by rfl
  | impure ⟨s, k⟩ => by apply impure_ext; intro p; apply interchange_rec

end Free
