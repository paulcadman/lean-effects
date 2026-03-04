import LeanEffectsContainer.Container
import LeanEffectsContainer.Prog
import LeanEffectsContainer.NonDet

open scoped Container

inductive ParserOps : Type 1 where
  | charOp (c : Char)

def ParserOpsC : Container where
  shape := ParserOps
  pos
    | .charOp _ => Char

def Parser : Effect where
  ops := ParserOpsC
  scps := Container.void

namespace Parser

variable
  {effs : List Effect}

section SmartConstructor

variable
  [Parser ∈ effs]

def char (c : Char) : Prog effs Char :=
  opEff (e:=Parser) ⟨ParserOps.charOp c, fun s => Prog.var s⟩

end SmartConstructor

variable
  {α : Type}
  [NonDet ∈ effs]

def run
  (p : Prog (Parser :: effs) α) : List Char → Prog effs (List Char × α) :=
  Prog.foldP
    (P := fun _ => List Char → Prog effs (List Char × α))
    (var0 := fun x => fun rest => if rest.isEmpty then pure (rest, x) else NonDet.fail)
    (varS := id)
    (op := fun ⟨c, k⟩ =>
      match c with
      | .inl (.charOp c) => fun st =>
        match st with
        | x :: xs => if x == c then k x xs else NonDet.fail
        | [] => NonDet.fail
      | .inr s => fun st => Prog.op ⟨s, fun p => k p st⟩)
    (scp := fun ⟨c, k⟩ =>
      match c with
      | .inl x => nomatch x
      | .inr s => fun st => Prog.scp ⟨s, fun p => ProgN.varS (k p st)⟩)
    p

def parse (s : String) (p : Prog (Parser :: effs) α) : Prog effs α := do
  let (_, res) ← run p (s.toList)
  pure res

namespace Examples

open scoped NonDet

def digit
  [NonDet ∈ effs]
  [Parser ∈ effs] : Prog effs Char :=
  let natToChar n := Char.ofNat (n + '0'.toNat)
  List.range 10 |>.foldl (fun r d => r ?? char (natToChar d)) NonDet.fail

mutual

partial def many
  {α : Type}
  [NonDet ∈ effs]
  (p : Prog effs α) : Prog effs (List α) :=
  pure [] ?? many1 p

partial def many1
  {α : Type}
  [NonDet ∈ effs]
  (p : Prog effs α) : Prog effs (List α) := do
    let a ← p
    let as ← many p
    pure (a :: as)
end

#guard
  (many digit
  |> parse "123"
  |> NonDet.runFirst
  |> Prog.run) = some ['1', '2', '3']

#guard
  (many digit
  |> parse ""
  |> NonDet.runFirst
  |> Prog.run) = some []

#guard
  (many1 digit
  |> parse "123"
  |> NonDet.runFirst
  |> Prog.run) = some ['1', '2', '3']

#guard
  (many1 digit
  |> parse ""
  |> NonDet.runFirst
  |> Prog.run) = none

#guard
  (digit
  |> parse "a123"
  |> NonDet.runFirst
  |> Prog.run) = none

section Arithmetic

mutual

partial def expr
  [NonDet ∈ effs]
  [Parser ∈ effs]
  : Prog effs Nat := do
    let i ← term
    let plus := do
      let _ ← NonDet.once <| char '+'
      let j ← expr
      pure (i + j)
     plus ?? pure i

partial def term
  [NonDet ∈ effs]
  [Parser ∈ effs]
  : Prog effs Nat :=
  let times := do
    let i ← factor
    let _ ← char '*'
    let j ← term
    pure (i * j)
  times ?? factor

partial def factor
  [NonDet ∈ effs]
  [Parser ∈ effs]
  : Prog effs Nat :=
  let num := do
    let ds ← many1 digit
    pure (String.ofList ds |> String.toNat!)
  let bracketed := do
    let _ ← char '('
    let i ← expr
    let _ ← char ')'
    pure i
  num ?? bracketed

end

def exScoped :=
  parse "1" expr
  |> NonDet.runFirst
  |> Prog.run

#guard exScoped = some 1

def exFactor :=
  parse "(2+8)*5" expr
  |> NonDet.runFirst
  |> Prog.run

#guard exFactor = some 50

end Arithmetic

end Examples

end Parser
