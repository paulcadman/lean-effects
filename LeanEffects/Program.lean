import LeanEffects.Effect

/-!
This file introduces an explicit-continuation encoding of effectul programs.

In Haskell it's common to encode effectful programs using the Free-monad for a
functor:

  Free f a = Pure a | Impure (f (Free f a))

For example the State effect is defined using the Free monad with the following
functor:

  StateF S a = Get (S -> a) | Put S a

Here `f` (e.g. `StateF S`) stores the continuation in the falue: for
`Get`, the continuation is `S -> a`; for `Put`, it is just `a`.

In Lean, the continuation is stored explicitly in `Program.op`:

  op : StateOp S β → (β → Program es α) → Progran es α

So `StateOp` only describes the operation tag (get/put), while the continuation
is carried by `Program`. This avoids Lean's positivity issues with `Free f a`
for an arbitrary `f`, and it matches the Agda container encoding once unpacked.

Haskell-style Free encoding (as a value):

  prog :: Free (StateF Int) ()
  prog =
    Impure (Get (\s ->
      Impure (Put (s+1) (Pure ()))
    ))

Lean Program:

  def prog : Program [StateOp Nat] PUnit :=
    Program.op (HSum.here StateOp.get) (fun s =>
      Program.op (HSum.here (StateOp.put (s + 1))) (fun _ =>
        Program.pure PUnit.unit))
-/

universe u v

-- Programs over a list of `EffectOp`s
-- A value is either pure or an effect followed by a continuation.
inductive Program (es : List Effect) (α : Type u) : Type (u+1) where
  | ret : α → Program es α
  | op : {β : Type u} → HSum es β → (β → Program es α) → Program es α

namespace Program

def map (f : α → β) : Program es α → Program es β
  | ret a => ret (f a)
  | .op e k => .op e (fun x => map f (k x))

def bind : Program es α → (α → Program es β) → Program es β
  | ret a, f => f a
  | .op e k, f => .op e (fun x => bind (k x) f)

instance : Monad (Program es) where
  map := map
  pure := ret
  bind := bind

-- Inject a single operation from effect e into a program.
def perform {e : Effect} [Member e es] (x : e α) : Program es α :=
  .op (Member.inj x) ret

-- Extract the value from a program with no effects
def run : Program [] α → α
  | ret a => a

-- foldP folds a Program into any monad m by providing handlers for pure and op.
-- The op handler receives the current op and a continuation in m.
def foldP
  [Monad m]
  (op : {γ : Type u} → HSum es γ → (γ → m α) → m α)
  : Program es α → m α
  | ret a => pure a
  | .op e k => op e (fun x => foldP op (k x))

structure Handler (e : Effect) (es : List Effect) (m : Type u → Type v) [Monad m] where
  handleEffect {α γ : Type u} : e γ → (γ → m α) → m α
  liftOther {γ : Type u} : HSum es γ → m γ

-- Interpret a Program into any monad by providing a Handler
def interpret {e : Effect} {es : List Effect} {α : Type u} {m : Type u → Type v} [Monad m]
  (handler : Handler e es m)
  : Program (e :: es) α → m α :=
  let handleOther {γ : Type u} := fun e k => handler.liftOther (γ:=γ) e >>= k
  let op := fun {γ} h k =>
    match h with
    | HSum.here opE => handler.handleEffect (γ:=γ) opE k
    | HSum.there opEs => handleOther (γ:=γ) opEs k
  foldP op

def reinterpret {e f : Effect} {es : List Effect} {α : Type u}
  (handler : {γ : Type u} → e γ → (γ → Program (f :: es) α) → Program (f :: es) α)
  : Program (e :: es) α → Program (f :: es) α :=
  foldP
    (op := fun {γ} h k =>
      match h with
      | HSum.here opE => handler (γ:=γ) opE k
      | HSum.there opR => Program.op (HSum.there opR) (fun x => k x))

end Program
