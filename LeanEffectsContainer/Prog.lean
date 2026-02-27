import LeanEffectsContainer.Container

open scoped Container

structure Effect : Type 1 where
  ops : Container
  scps : Container

def ops : List Effect → Container := Container.sum ∘ List.map Effect.ops

def scps : List Effect → Container := Container.sum ∘ List.map Effect.scps

universe u v

inductive ProgN (effs : List Effect) (α : Type u) : Nat → Type (u + 1) where
  | var0 : α → ProgN effs α 0
  | varS {n : Nat} : ProgN effs α n → ProgN effs α (n + 1)
  -- I want to write
  -- op {n : Nat} : ⟦ops eff⟧ (Prog effs α (n + 1)) → Prog effs α (n + 1)
  -- but this is rejected
  | op {n : Nat} (s : (ops effs).shape) :
    ((ops effs).pos s → ProgN effs α (n + 1)) → ProgN effs α (n + 1)
  -- I want to write
  -- scp {n : Nat} : ⟦scps eff⟧ (Prog effs α (n + 2)) → Prog effs α (n + 1)
  -- but this is rejected
  | scp {n : Nat} (s : (scps effs).shape) :
    ((scps effs).pos s → ProgN effs α (n + 2)) → ProgN effs α (n + 1)

abbrev Prog (effs : List Effect) (α : Type u) : Type (u + 1) := ProgN effs α 1

namespace Prog

variable
  {effs : List Effect}
  {α : Type u}

def var (x : α) : Prog effs α :=
  .varS (.var0 x)

def op : ⟦ ops effs ⟧ (Prog effs α) → Prog effs α
  | ⟨s, p⟩ => ProgN.op s p

def scp : ⟦ scps effs ⟧ (ProgN effs α 2) → Prog effs α
  | ⟨s, p⟩ => ProgN.scp s p

def foldP
  (P : Nat → Type v)
  (var0 : α → P 0)
  (varS : {n : Nat} → P n → P (n + 1))
  (op : {n : Nat} → ⟦ ops effs ⟧ (P (n + 1)) → P (n + 1))
  (scp : {n : Nat} → ⟦ scps effs ⟧ (P (n + 2)) → P (n + 1))
  {n : Nat} :
  ProgN effs α n → P n
  | ProgN.var0 x => var0 x
  | ProgN.varS x => varS (foldP P var0 varS op scp x)
  | ProgN.op c k => op ⟨c, fun p => foldP P var0 varS op scp (k p)⟩
  | ProgN.scp c k => scp ⟨c, fun p => foldP P var0 varS op scp (k p)⟩

def BindP (effs : List Effect) (α : Type u) : Nat → Type (u + 1)
  | 0 => Prog effs α
  | n + 1 => ProgN effs α (n + 1)

def bindVarLift : (n : Nat) → BindP effs α n → BindP effs α (n + 1)
  | 0, x => x
  | _ + 1, x => ProgN.varS x

section Bind

variable
  {β : Type u}

def bindN
  {n : Nat}
  (ma : ProgN effs α (n + 1))
  (k : α → Prog effs β) :
  ProgN effs β (n + 1) :=
  foldP
    (P := BindP effs β)
    (var0 := k)
    (varS := fun {i} x => bindVarLift i x)
    (op := fun ⟨c, k⟩ => ProgN.op c k)
    (scp := fun ⟨c, k⟩ => ProgN.scp c k)
    ma

def bind : Prog effs α → (α → Prog effs β) → Prog effs β :=
  bindN

end Bind

end Prog

def Prog.run {α : Type u} : Prog [] α → α :=
  Prog.foldP
    (P := fun _ => α)
    (var0 := id)
    (varS := id)
    (op := fun ⟨c, _⟩ => nomatch c)
    (scp := fun ⟨c, _⟩ => nomatch c)

instance {effs : List Effect} : Monad (Prog effs) where
  pure := Prog.var
  bind := Prog.bind

def opsMem
  {effs : List Effect}
  {e : Effect} :
  e ∈ effs → e.ops ∈ List.map Effect.ops effs
  | .here => .here
  | .there m => .there (opsMem m)

def scpsMem
  {effs : List Effect}
  {e : Effect} :
  e ∈ effs → e.scps ∈ List.map Effect.scps effs
  | .here => .here
  | .there m => .there (scpsMem m)

def opEff
  {effs : List Effect}
  {e : Effect}
  {α : Type u}
  [m : e ∈ effs]
  (ext : ⟦e.ops⟧ (Prog effs α)) : Prog effs α :=
    Container.inject (opsMem m) ext |> Prog.op

def scpEff
  {effs : List Effect}
  {e : Effect}
  {α : Type u}
  [m : e ∈ effs]
  (ext : ⟦e.scps⟧ (ProgN effs α 2)) : Prog effs α :=
    Container.inject (scpsMem m) ext |> Prog.scp
