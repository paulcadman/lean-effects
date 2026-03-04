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
    (var0 := fun x => fun rest => pure (rest, x))
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

def parse (s : String) (p : Prog (Parser :: effs) α) : Prog effs (String × α) := do
  let (rest, res) ← run p (s.toList)
  pure (String.ofList rest, res)

namespace Examples

open scoped NonDet

def digit
  [NonDet ∈ effs]
  [Parser ∈ effs] : Prog effs Char :=
  let natToChar n := Char.ofNat (n + '0'.toNat)
  List.range 10 |>.foldl (fun r d => r ?? char (natToChar d)) NonDet.fail

#guard
  (digit
  |> parse "123"
  |> NonDet.runFirst
  |> Prog.run) = some ("23", '1')

#guard
  (digit
  |> parse "a123"
  |> NonDet.runFirst
  |> Prog.run) = none

end Examples

end Parser
