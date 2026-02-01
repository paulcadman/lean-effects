import LeanEffects

inductive Symbol : Type → Type where
  | charOp : Char → Symbol Char

namespace Symbol

def char [Member Symbol es] (c : Char) : Program es Char :=
  .perform (Symbol.charOp c)

def ParseM (es : List Effect) (α : Type u) := List Char → Program es (List Char × α)

instance (es : List Effect) : Monad (ParseM es) where
  pure a := fun cs => Program.ret (cs, a)
  bind m f :=
    fun cs => Program.bind (m cs) (fun (cs', a) => f a cs')

def parseM [Member NonDet es] (p : Program (Symbol :: es) α) : ParseM es α :=
  let handler : Program.Handler Symbol es (ParseM es) := {
    ret := fun a cs =>
      if cs.isEmpty
      then Pure.pure (cs, a)
      else NonDet.fail
    handleEffect := fun op k =>
      match op with
      | .charOp c =>
          fun cs =>
            match cs with
            | x :: xs =>
                if x == c
                then k x xs
                else NonDet.fail
            | [] => NonDet.fail
    liftOther := fun e =>
      fun cs => Program.op e (fun x => Program.ret (cs, x))
  }
  Program.interpret handler p

def parse [Member NonDet es] (s : String) (p : Program (Symbol :: es) α) : Program es α :=
  parseM p (s.toList) |>.map Prod.snd

end Symbol

def digit
  [Member NonDet es]
  [Member Symbol es]
  : Program es Char := Id.run do
  let mut r := NonDet.fail
  for n in [0:9] do
    r := NonDet.choose2 r (Symbol.char (Char.ofNat (n + '0'.toNat)))
  r

mutual

partial def many
  [Member NonDet es]
  (p : Program es α) : Program es (List α) :=
  NonDet.choose2 (pure []) (many1 p)

partial def many1
  [Member NonDet es]
  (p : Program es α) : Program es (List α) := do
    let a ← p
    let as ← many p
    pure (a :: as)

end

mutual

open Symbol

partial def expr
  [Member NonDet es]
  [Member Symbol es]
  : Program es Nat :=
  let plus := do
    let i ← term
    let _ ← char '+'
    let j ← term
    pure (i + j)
  NonDet.choose2 plus term

partial def term
  [Member NonDet es]
  [Member Symbol es]
  : Program es Nat :=
  let times := do
    let i ← factor
    let _ ← char '*'
    let j ← term
    pure (i * j)
  NonDet.choose2 times factor

partial def factor
  [Member NonDet es]
  [Member Symbol es]
  : Program es Nat :=
  let num := do
    let ds ← many1 digit
    pure (String.ofList ds |> String.toNat!)
  let bracketed := do
    let _ ← char '('
    let i ← expr
    let _ ← char ')'
    pure i
  NonDet.choose2 num bracketed

end

def ex1 :=
  Symbol.parse "" (many digit)
  |> NonDet.runViaOption
  |> Program.run

#guard (ex1 |>.map String.ofList) == some ""

def ex2 :=
  Symbol.parse "1234" (many digit)
  |> NonDet.runViaOption
  |> Program.run

#guard (ex2 |>.map String.ofList) == some "1234"

def ex3 :=
  Symbol.parse "" (many1 digit)
  |> NonDet.runViaOption
  |> Program.run

#guard (ex3 |>.map String.ofList) == none

def ex4 :=
  Symbol.parse "1234" (many1 digit)
  |> NonDet.runViaOption
  |> Program.run

#guard (ex4 |>.map String.ofList) == some "1234"

def ex5 :=
  Symbol.parse "1234a" (many1 digit)
  |> NonDet.runViaOption
  |> Program.run

#guard (ex5 |>.map String.ofList) == none

def ex6 :=
  Symbol.parse "(2+8)*5" expr
  |> NonDet.runViaOption
  |> Program.run

#guard ex6 == some 50
