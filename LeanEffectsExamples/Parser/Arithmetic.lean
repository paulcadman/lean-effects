import LeanEffectsExamples.Parse

mutual

open Symbol

partial def expr
  {es : List Effect}
  [Member NonDet es]
  [Member Symbol es]
  : Program es Nat :=
  let plus := do
    let i ← term
    let _ ← char '+'
    let j ← term
    pure (i + j)
  NonDet.choose2 plus term

partial def expr1
  {es : List Effect}
  [Member NonDet es]
  [Member Symbol es]
  : Program es Nat := do
    let i ← term
    let plus := do
      let _ ← char '+'
      let j ← expr1
      pure (i + j)
    NonDet.choose2 plus (pure i)

partial def expr2
  {es : List Effect}
  [Member NonDet es]
  [Member Symbol es]
  : Program es Nat := do
    let i ← term
    let plus := do
      let _ ← char '+'
      -- cut commits to this branch, i.e it prevents backtracking to i after + is consumed
      Cut.cut
      let j ← expr2
      pure (i + j)
    Cut.call <| NonDet.choose2 plus (pure i)

partial def expr3
  {es : List Effect}
  [Member NonDet es]
  [Member Symbol es]
  [Member Call es]
  [Member Cut es]
  : Program es Nat := do
    let i ← term
    let plus := do
      let _ ← char '+'
      Cut.cut
      let j ← expr3
      pure (i + j)
    Call.call' <| NonDet.choose2 plus (pure i)

partial def term
  {es : List Effect}
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
  {es : List Effect}
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

def ex6_1 :=
  Symbol.parse "(2+8)*5" expr1
  |> NonDet.runViaOption
  |> Program.run

#guard ex6_1 == some 50

def ex7 :=
  Symbol.parse "1" expr2
  |> NonDet.runViaOption
  |> Program.run

-- expected to be `some 1` but fails because of
-- the ordering of the parse and call handlers
-- #guard ex7 == some 1

def ex8 :=
  Symbol.parse "1" expr3
  |> Cut.runCut
  |> NonDet.runViaOption
  |> Program.run

#guard ex8 == some 1
