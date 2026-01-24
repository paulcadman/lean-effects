import LeanEffects.Program
inductive Choice : Type u
  | left
  | right

inductive NonDetEmpty : Type u where

inductive NonDet : Type u → Type u where
  | failOp : NonDet NonDetEmpty
  | chooseOp : NonDet Choice

namespace NonDet

open Program

def empty [Member NonDet es] : Program es α := do
  let x ← .perform NonDet.failOp
  nomatch x

def fail [Member NonDet es] : Program es α :=
  empty

def choose2 [Member NonDet es] (p q : Program es α) : Program es α := do
  let b ← .perform NonDet.chooseOp
  match b with
  | .left => p
  | .right => q

def runViaAlternative
  {m : Type u → Type v}
  [Monad m]
  [Alternative m]
  (liftOther : {γ : Type u} → HSum es γ → m γ)
  (p : Program (NonDet :: es) α) : m α :=
  let handler : Handler NonDet es m := {
    handleEffect := fun opE k =>
      match opE with
      | NonDet.failOp => Alternative.failure
      | NonDet.chooseOp => Alternative.orElse (k .left) (fun _ => k .right:),
    liftOther := liftOther
  }
  interpret handler p

abbrev ListM (es : List Effect) (α : Type u) := Program es (List α)

instance (es : List Effect) : Monad (ListM es) where
  pure a := Program.pure [a]
  bind {α β} m f := do
    Program.bind m (fun xs =>
        let rec go : List α → Program es (List β)
            | [] => Program.pure []
            | x :: xs' => do
              let ys ← f x
              let zs ← go xs'
              Program.pure (ys ++ zs)
        go xs)

instance (es : List Effect) : Alternative (ListM es) where
  failure := Program.pure []
  orElse {α} := fun xs ys =>
    let p : Program es (List α) := do
      let xs' ← xs
      let ys' ← ys ()
      Program.pure (xs' ++ ys')
    p

def runViaList (p : Program (NonDet :: es) α) : Program es (List α) :=
  let liftOther {γ} : HSum es γ → ListM es γ :=
    fun e => Program.op e (fun x => Program.pure [x])
  runViaAlternative (m:=ListM es) liftOther p

abbrev OptionM (es : List Effect) (α : Type u) := Program es (Option α)

instance (es : List Effect) : Monad (OptionM es) where
  pure a := Program.pure (some a)
  bind m f := Program.bind m (
    fun
    | none => Program.pure none
    | some x => f x
  )

instance (es : List Effect) : Alternative (OptionM es) where
  failure := Program.pure none
  orElse := fun mx my =>
    Program.bind mx (
      fun
      | none => my ()
      | some x => Program.pure (some x)
    )

def runViaOption (p : Program (NonDet :: es) α) : Program es (Option α) :=
  let liftOther {γ} : HSum es γ -> OptionM es γ :=
    fun e => Program.op e (fun x => Program.pure (some x))
  runViaAlternative (m:=OptionM es) liftOther p

end NonDet
