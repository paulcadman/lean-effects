import LeanEffects

variable {es : List Effect}
universe u

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

def parseM {α : Type} [Member NonDet es] (p : Program (Symbol :: es) α) : ParseM es α :=
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

def parse {α : Type} [Member NonDet es] (s : String) (p : Program (Symbol :: es) α) : Program es α :=
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
  {α : Type u}
  [Member NonDet es]
  (p : Program es α) : Program es (List α) :=
  NonDet.choose2 (pure []) (many1 p)

partial def many1
  {α : Type u}
  [Member NonDet es]
  (p : Program es α) : Program es (List α) := do
    let a ← p
    let as ← many p
    pure (a :: as)
end
