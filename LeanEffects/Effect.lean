universe u v

abbrev Effect := Type u → Type v

-- A HSum is a heterogeneous sum of `Effect`s.
-- A value `HSum es α` is an operation from some effect in `es` that returns an `α`.
inductive HSum : List Effect.{u, v} → Type u → Type ((max v u) + 1) where
  | here {e : Effect} {α : Type u} {es : List Effect} : e α → HSum (e :: es) α
  | there {e : Effect} {α : Type u} {es : List Effect} : HSum es α → HSum (e :: es) α

-- A typeclass to express that `e` is in the list `es`
class Member (e : Effect.{u, v}) (es : List Effect.{u, v}) : Type ((max v u) + 1) where
  inj : {α : Type u} → e α → HSum es α

instance (e : Effect) (es : List Effect) : Member e (e :: es) where
  inj := fun x => HSum.here x

instance (e e' : Effect) (es : List Effect) [Member e es] : Member e (e' :: es) where
  inj := fun x => HSum.there (Member.inj x)
