-- A translation of the Agda code from https://cse.sc.edu/~pfu/document/papers/ind-nest.pdf
-- Towards an induction principle for nested data types - Peng Fu and Peter Selinger
universe u v

inductive BushN (α : Type u) : Nat → Type (u + 1) where
  | atom0 : α → BushN α 0
  | atomS {n : Nat} : BushN α n → BushN α (n + 1)
  | leaf {n : Nat} : BushN α n
  | cons {n : Nat} : BushN α n → BushN α (n + 1) → BushN α n

abbrev Bush (α : Type u) : Type (u + 1) := BushN α 0

namespace Bush

variable
  {α : Type u}

def zipAux {n : Nat} : BushN (Bush α) n → BushN α (n + 1)
  | .atom0 x => .atomS x
  | .atomS x => .atomS (zipAux x)
  | .leaf => .leaf
  | .cons x y => .cons (zipAux x) (zipAux y)

def unzipAux : (n : Nat) → BushN α (n + 1) → BushN (Bush α) n
  | 0, .atomS x => .atom0 x
  | n + 1, .atomS x => .atomS (unzipAux n x)
  | _, .leaf => .leaf
  | n, .cons x y => .cons (unzipAux n x) (unzipAux (n + 1) y)

def zip : Bush (Bush α) → BushN α 1 := zipAux (n:=0)

def unzip : BushN α 1 → Bush (Bush α) := unzipAux 0

def cons (x : α) (xs : Bush (Bush α)) : Bush α :=
  BushN.cons (BushN.atom0 x) (zip xs)

def leaf : Bush α :=
  BushN.leaf

def singleton (x : α) : Bush α :=
  cons x leaf

section Map

variable {β : Type u}

def mapN {n : Nat} (f : α → β) : BushN α n → BushN β n
 | .atom0 x => .atom0 (f x)
 | .atomS x => .atomS (mapN f x)
 | .leaf => .leaf
 | .cons x y => .cons (mapN f x) (mapN f y)

def map (f : α → β) : Bush α → Bush β := mapN f

end Map

def foldN
  (P : Nat → Type v)
  (atom0 : α → P 0)
  (atomS : {n : Nat} → P n → P (n + 1))
  (leaf : {n : Nat} → P n)
  (cons : {n : Nat} → P n → P (n + 1) → P n)
  {n : Nat} :
  BushN α n → P n
  | .atom0 x => atom0 x
  | .atomS x => atomS (foldN P atom0 atomS leaf cons x)
  | .leaf => leaf
  | .cons x y =>
    cons
      (foldN P atom0 atomS leaf cons x)
      (foldN P atom0 atomS leaf cons y)

end Bush

def BushN.sumN {n : Nat} : BushN Nat n → Nat :=
  Bush.foldN
    (P := fun _ => Nat)
    (atom0 := id)
    (atomS := id)
    (leaf := fun {_} => 0)
    (cons := fun x y => x + y)

def Bush.sum : Bush Nat → Nat := BushN.sumN

def BushN.lengthN {α : Type} {n : Nat} : BushN α n → Nat :=
  Bush.foldN
    (P := fun _ => Nat)
    (atom0 := fun _ => 0)
    (atomS := id)
    (leaf := fun {_} => 0)
    (cons := fun {_} _ y => y + 1)

def Bush.length {α : Type} : Bush α → Nat := BushN.lengthN

section Examples

open Bush

def bush1 : Bush Nat :=
  cons 3 (cons (singleton 4) leaf)

#guard length bush1 = 2
#guard sum bush1 = 7

end Examples
