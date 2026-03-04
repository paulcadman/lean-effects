import LeanEffectsContainer.Container

open scoped Container

universe u v

structure Effect : Type 2 where
  ops : Container.{1, 0}
  scps : Container.{1, 0}

def ops : List Effect → Container.{1, 0} := Container.sum ∘ List.map Effect.ops

@[simp] theorem ops_cons {e} {es} : ops (e :: es) = Container.coproduct (Effect.ops e) (ops es) := by simp [ops]

@[simp] theorem pos_ops_inl {c} {cs} {x}
  : Container.pos (ops (c :: cs)) (.inl x) = Container.pos c.ops x := by
  simp [ops]

@[simp] theorem pos_ops_inr {c} {cs} {x}
  : Container.pos (ops (c :: cs)) (.inr x) = Container.pos (ops cs) x := by
  simp [ops]

def scps : List Effect → Container.{1, 0} := Container.sum ∘ List.map Effect.scps

@[simp] theorem pos_scps_inl {c} {cs} {x}
  : Container.pos (scps (c :: cs)) (.inl x) = Container.pos c.scps x := by
  simp [scps]

@[simp] theorem pos_scps_inr {c} {cs} {x}
  : Container.pos (scps (c :: cs)) (.inr x) = Container.pos (scps cs) x := by
  simp [scps]

@[simp] theorem scps_cons {e} {es} : scps (e :: es) = Container.coproduct e.scps (scps es) := by simp [scps]

inductive ProgN (effs : List Effect) (α : Type u) : Nat → Type (max 1 u) where
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

abbrev Prog (effs : List Effect) (α : Type u) : Type (max 1 u) := ProgN effs α 1

namespace Prog

variable
  {effs : List Effect}
  {α : Type u}

def var {n : Nat} (x : α) : ProgN effs α n :=
  match n with
  | 0 => .var0 x
  | _ + 1 => .varS (var x)

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

def BindP (effs : List Effect) (α : Type u) : Nat → Type (max 1 u)
  | 0 => Prog effs α
  | n + 1 => ProgN effs α (n + 1)

def bindVarLift : (n : Nat) → BindP effs α n → BindP effs α (n + 1)
  | 0, x => x
  | _ + 1, x => ProgN.varS x

section Bind

variable
  {β : Type v}

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

def bindN'
  {n : Nat}
  (ma : ProgN effs α (n + 1))
  (k : α → ProgN effs β (n + 1)) :
  ProgN effs β (n + 1) :=
  foldP
    (P := fun _ => ProgN effs β (n + 1))
    (var0 := k)
    (varS := id)
    (op := fun ⟨c, k⟩ => ProgN.op c k)
    (scp := fun ⟨c, k⟩ => ProgN.scp c (ProgN.varS ∘ k))
    ma

def bind : Prog effs α → (α → Prog effs β) → Prog effs β := bindN

end Bind

end Prog

def Prog.run {α : Type u} : Prog [] α → α :=
  Prog.foldP
    (P := fun _ => α)
    (var0 := id)
    (varS := id)
    (op := fun ⟨c, _⟩ => nomatch c)
    (scp := fun ⟨c, _⟩ => nomatch c)

def Prog.mapU {α : Type u} {β : Type v} {effs : List Effect}
  (f : α → β) (p : Prog effs α) : Prog effs β :=
  p.bind (Prog.var ∘ f)

def Prog.flatten {n} {effs} {α} : ProgN effs (Prog effs α) n → ProgN effs α (n + 1)
  | .var0 a => a
  | .varS a => ProgN.varS (flatten a)
  | .op a b => ProgN.op a (fun x => flatten (b x))
  | .scp a b => ProgN.scp a (fun x => flatten (b x))

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
