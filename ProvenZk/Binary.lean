import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Bitvec.Defs

import ProvenZk.Ext.List
import ProvenZk.Ext.Vector
import ProvenZk.Subvector

inductive Bit : Type where
  | zero : Bit
  | one : Bit
  deriving BEq

instance : Repr Bit where
  reprPrec
    | Bit.zero, _  => "0"
    | Bit.one, _ => "1"

namespace Bit
def toNat : Bit -> Nat := fun b => match b with
  | Bit.zero => 0
  | Bit.one => 1

def toZMod {n} : Bit -> ZMod n := fun b => match b with
  | Bit.zero => 0
  | Bit.one => 1

instance : Coe Bit Nat where
  coe := toNat

instance {n} : Coe Bit (ZMod n) where
  coe := toZMod

instance : OfNat Bit 0 where
  ofNat := zero

instance : OfNat Bit 1 where
  ofNat := one

instance : Inhabited Bit where
  default := zero

end Bit

def bit_mod_two (inp : Nat) : Bit := match h:inp%2 with
 | 0 => Bit.zero
 | 1 => Bit.one
 | x + 2 => False.elim (by
    have := Nat.mod_lt inp (y := 2)
    rw [h] at this
    simp at this
    contradiction
 )

def nat_to_bits_le (l : Nat): Nat → Option (Vector Bit l) := match l with
  | 0 => fun i => if i = 0 then some Vector.nil else none
  | Nat.succ l => fun i => do
    let x := i / 2
    let y := bit_mod_two i
    let xs ← nat_to_bits_le l x
    some (y ::ᵥ xs)

def nat_to_bits_le_full_n (l : Nat): Nat → Vector Bit l := match l with
  | 0 => fun _ => Vector.nil
  | Nat.succ l => fun i =>
    let x := i / 2
    let y := bit_mod_two i
    let xs := nat_to_bits_le_full_n l x
    y ::ᵥ xs

def nat_to_bits_le_full : Nat → List Bit
  | 0 => [0]
  | 1 => [1]
  | n + 2 =>
    have : Nat.succ (n/2) < n+2 := by
      simp_arith
      apply Nat.div_le_self
    bit_mod_two (n+2) :: nat_to_bits_le_full ((n+2) / 2)

def binary_length (n : Nat) : Nat := List.length (nat_to_bits_le_full n)

def nat_to_bit (x : Nat) : Bit := match x with
  | 0 => Bit.zero
  | 1 => Bit.one
  | Nat.succ (Nat.succ _) => panic "Bit can only be 0 or 1"

def zmod_to_bit {n} (x : ZMod n) : Bit := match ZMod.val x with
  | 0 => Bit.zero
  | 1 => Bit.one
  | Nat.succ (Nat.succ _) => panic "Bit can only be 0 or 1"

@[reducible]
def is_bit (a : ZMod N): Prop := a = 0 ∨ a = 1

@[simp]
theorem is_bit_zero : is_bit (0 : ZMod n) := by tauto

@[simp]
theorem is_bit_one : is_bit (1 : ZMod n) := by tauto

abbrev bOne : {v : ZMod n // is_bit v} := ⟨1, by simp⟩

abbrev bZero : {v : ZMod n // is_bit v} := ⟨0, by simp⟩

def embedBit {n : Nat} : Bit → {x : (ZMod n) // is_bit x}
| Bit.zero => bZero
| Bit.one => bOne

def is_vector_binary {d n} (x : Vector (ZMod n) d) : Prop :=
  (List.foldr (fun a r => is_bit a ∧ r) True (Vector.toList x))

@[simp]
lemma is_vector_binary_reverse {depth} (ix : Vector (ZMod n) depth):
  is_vector_binary ix.reverse ↔ is_vector_binary ix := by
  simp only [is_vector_binary, Vector.toList_reverse]
  rw [List.foldr_reverse_assoc]
  { simp }
  { intros; simp; tauto }

theorem is_vector_binary_cons {a : ZMod n} {vec : Vector (ZMod n) d}:
  is_vector_binary (a ::ᵥ vec) ↔ is_bit a ∧ is_vector_binary vec := by
  unfold is_vector_binary
  conv => lhs; unfold List.foldr; simp

theorem is_vector_binary_dropLast {d n : Nat} {gate_0 : Vector (ZMod n) d} :
  is_vector_binary gate_0 → is_vector_binary (Vector.dropLast gate_0) := by
  simp [is_vector_binary, Vector.toList_dropLast]
  intro h
  induction gate_0 using Vector.inductionOn with
  | h_nil => simp [List.dropLast]
  | h_cons ih =>
    rename_i x xs
    cases xs using Vector.casesOn
    simp
    rw [Vector.toList_cons, Vector.toList_cons, List.dropLast_cons]
    simp [h]
    cases h
    tauto

lemma dropLast_symm {n} {xs : Vector Bit d} :
  Vector.map (fun i => @Bit.toZMod n i) (Vector.dropLast xs) = (Vector.map (fun i => @Bit.toZMod n i) xs).dropLast := by
  induction xs using Vector.inductionOn with
  | h_nil =>
    simp [Vector.dropLast, Vector.map]
  | h_cons ih₁ =>
    rename_i x₁ xs
    induction xs using Vector.inductionOn with
    | h_nil =>
      simp [Vector.dropLast, Vector.map]
    | h_cons _ =>
      rename_i x₂ xs
      simp [Vector.vector_list_vector]
      simp [ih₁]

lemma zmod_to_bit_to_zmod {n : Nat} [Fact (n > 1)] {x : (ZMod n)} (h : is_bit x):
  Bit.toZMod (zmod_to_bit x) = x := by
  simp [is_bit] at h
  cases h with
  | inl =>
    subst_vars
    simp [zmod_to_bit, Bit.toZMod]
  | inr =>
    subst_vars
    simp [zmod_to_bit, ZMod.val_one, Bit.toZMod]

lemma bit_to_zmod_to_bit {n : Nat} [Fact (n > 1)] {x : Bit}:
  zmod_to_bit (@Bit.toZMod n x) = x := by
  cases x with
  | zero =>
    simp [zmod_to_bit, Bit.toZMod]
  | one =>
    simp [zmod_to_bit, Bit.toZMod]
    simp [zmod_to_bit, ZMod.val_one, Bit.toZMod]

def vector_zmod_to_bit {n d : Nat} (a : Vector (ZMod n) d) : Vector Bit d :=
  Vector.map zmod_to_bit a

def vector_bit_to_zmod {n d : Nat} (a : Vector Bit d) : Vector (ZMod n) d :=
  Vector.map (fun x => Bit.toZMod x) a

lemma bit_to_zmod_equiv {d} [Fact (n > 1)] (x : Vector Bit d) (y : Vector (ZMod n) d) (h : is_vector_binary y):
  vector_bit_to_zmod x = y ↔ x = vector_zmod_to_bit y := by
  apply Iff.intro
  . intro hv
    rename_i d
    rw [<-hv]
    induction x, y using Vector.inductionOn₂ with
    | nil => simp
    | cons ih=>
      rename_i x y xs ys
      simp [vector_bit_to_zmod, vector_zmod_to_bit]
      simp [Vector.vector_eq_cons]
      refine ⟨?_, ?_⟩
      . simp [bit_to_zmod_to_bit]
      . rw [<-vector_bit_to_zmod, <-vector_zmod_to_bit]
        apply ih
        . simp [is_vector_binary_cons] at h
          tauto
        . simp [vector_bit_to_zmod] at hv
          simp [Vector.vector_eq_cons] at hv
          rw [<-vector_bit_to_zmod] at hv
          tauto
  . intro hv
    rename_i d
    rw [hv]
    induction x, y using Vector.inductionOn₂ with
    | nil => simp
    | cons ih=>
      rename_i x y xs ys
      simp [vector_bit_to_zmod, vector_zmod_to_bit]
      simp [Vector.vector_eq_cons]
      refine ⟨?_, ?_⟩
      . rw [zmod_to_bit_to_zmod]
        . simp [is_vector_binary_cons] at h
          tauto
      . rw [<-vector_bit_to_zmod, <-vector_zmod_to_bit]
        apply ih
        . simp [is_vector_binary_cons] at h
          tauto
        . simp [vector_zmod_to_bit] at hv
          simp [Vector.vector_eq_cons] at hv
          rw [<-vector_zmod_to_bit] at hv
          tauto

lemma vector_zmod_to_bit_last {n d : Nat} {xs : Vector (ZMod n) (d+1)} :
  (vector_zmod_to_bit xs).last = (zmod_to_bit xs.last) := by
  simp [vector_zmod_to_bit, Vector.last]

lemma vector_zmod_to_bit_to_zmod {n d : Nat} [Fact (n > 1)] {xs : Vector (ZMod n) d} (h : is_vector_binary xs) :
  Vector.map Bit.toZMod (vector_zmod_to_bit xs) = xs := by
  induction xs using Vector.inductionOn with
  | h_nil => simp
  | h_cons ih =>
    simp [is_vector_binary_cons] at h
    cases h
    simp [vector_zmod_to_bit]
    simp [vector_zmod_to_bit] at ih
    rw [zmod_to_bit_to_zmod]
    rw [ih]
    assumption
    assumption

lemma vector_bit_to_zmod_to_bit {d n : Nat} [Fact (n > 1)] {xs : Vector Bit d} :
  vector_zmod_to_bit (Vector.map (fun i => @Bit.toZMod n i) xs) = xs := by
  induction xs using Vector.inductionOn with
  | h_nil => simp
  | h_cons ih =>
    rename_i x xs
    simp [vector_zmod_to_bit]
    simp [vector_zmod_to_bit] at ih
    simp [ih]
    rw [bit_to_zmod_to_bit]

lemma vector_zmod_to_bit_dropLast {n d : Nat} [Fact (n > 1)] {xs : Vector (ZMod n) (d+1)} (h : is_vector_binary xs) :
  Vector.map Bit.toZMod (Vector.dropLast (vector_zmod_to_bit xs)) = (Vector.dropLast xs) := by
  simp [dropLast_symm]
  rw [vector_zmod_to_bit_to_zmod]
  assumption

@[simp]
theorem vector_zmod_to_bit_cons : vector_zmod_to_bit (x ::ᵥ xs) = (nat_to_bit x.val) ::ᵥ vector_zmod_to_bit xs := by
  rfl

def recover_binary_nat {d} (rep : Vector Bit d): Nat := match d with
  | 0 => 0
  | Nat.succ _ => rep.head.toNat + 2 * recover_binary_nat rep.tail

def recover_binary_zmod {d n} (rep : Vector Bit d) : ZMod n := match d with
  | 0 => 0
  | Nat.succ _ => rep.head.toZMod + 2 * recover_binary_zmod rep.tail

-- `rep` is the bit representation using `ZMod n` values
-- Elements of `rep` should be `0` or `1`, but it should be constrained externally using
-- `is_vector_binary` function
def recover_binary_zmod' {d n} (rep : Vector (ZMod n) d) : ZMod n := match d with
  | 0 => 0
  | Nat.succ _ => rep.head + 2 * recover_binary_zmod' rep.tail

@[simp]
theorem recover_binary_nat_zero {n : Nat} : recover_binary_nat (Vector.replicate n Bit.zero) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [recover_binary_nat, ih]

theorem recover_binary_zmod_bit {d n} [Fact (n > 1)]  {w : Vector (ZMod n) d}:
  is_vector_binary w → recover_binary_zmod' w = recover_binary_zmod (vector_zmod_to_bit w) := by
  intro h
  induction w using Vector.inductionOn with
  | h_nil => rfl
  | h_cons ih =>
    simp [recover_binary_zmod', recover_binary_zmod]
    rw [is_vector_binary_cons] at h
    cases h
    rw [ih]
    rotate_left
    . assumption
    rename (is_bit _) => isb
    cases isb <;> {
      subst_vars
      have : n > 1 := (inferInstance : Fact (n > 1)).elim
      induction n with
      | zero => simp
      | succ n =>
        induction n with
        | zero =>
          simp
        | succ =>
          rw [ZMod.val]
          simp
          rfl
    }

theorem mod_two_bit_back : (Bit.toNat $ bit_mod_two n) = n % 2 := by
  simp [bit_mod_two]
  split
  . simp [*]
  . simp [*]
  . contradiction

def is_binary_of {n d} (inp : ZMod n) (rep : Vector Bit d): Prop := inp = recover_binary_zmod rep

def nat_n_bits (a : Nat) (digits : Nat) : Nat :=
  Bitvec.bitsToNat (List.reverse (List.take digits (List.reverse (Nat.bits a))))

lemma even_ne_odd (a b : Nat): 2 * a ≠ 2 * b + 1 := by
  intro h
  induction a generalizing b with
  | zero => cases h
  | succ a1 ih =>
    rw [Nat.mul_succ] at h
    cases b
    . cases h
    . simp_arith at h
      apply ih _ h

lemma parity_bit_unique (a b : Bit) (c d : Nat) : a + 2 * c = b + 2 * d -> a = b ∧ c = d := by
  intro h; cases a <;> cases b <;> simp [Bit.toNat, *] at *
  . assumption
  . rw [add_comm] at h; apply even_ne_odd _ _ h
  . rw [add_comm, eq_comm] at h; apply even_ne_odd _ _ h
  . assumption

theorem binary_nat_unique {d} (rep1 rep2 : Vector Bit d):
  recover_binary_nat rep1 = recover_binary_nat rep2 ↔ rep1 = rep2 := by
  apply Iff.intro
  . intro h
    induction d with
    | zero => apply Vector.zero_subsingleton.allEq;
    | succ d1 ih =>
      simp [recover_binary_nat] at h
      rw [←Vector.cons_head_tail rep1]
      rw [←Vector.cons_head_tail rep2]
      have h := parity_bit_unique _ _ _ _ h
      cases h
      apply congr
      . apply congrArg; assumption
      . apply ih; assumption
  . tauto

theorem binary_nat_lt {d} (rep : Vector Bit d): recover_binary_nat rep < 2 ^ d := by
  induction d with
  | zero => simp [recover_binary_nat]
  | succ _ ih =>
    simp [recover_binary_nat]
    cases rep.head <;> (
      simp [*, Bit.toNat]
      simp_arith
      let h := ih rep.tail
      let h := Nat.le.dest h
      cases h; rename_i w h
      simp_arith at h
      rw [Nat.pow_succ]
    )
    . apply @Nat.le.intro _ _ (w + w + 1)
      linarith
    . apply @Nat.le.intro _ _ (w + w)
      linarith

theorem binary_nat_zmod_equiv {n d} (rep : Vector Bit d):
  (recover_binary_nat rep : ZMod n) = (recover_binary_zmod rep) := by
  induction d with
  | zero => simp [recover_binary_nat, recover_binary_zmod]
  | succ d' ih =>
    simp [recover_binary_nat, recover_binary_zmod]
    cases rep.head <;> simp [Bit.toNat, Bit.toZMod, *]

theorem binary_nat_zmod_equiv_mod_p {n d} (rep : Vector Bit d):
  (recover_binary_zmod rep : ZMod n).val = recover_binary_nat rep % n := by
  rw [←binary_nat_zmod_equiv]
  apply ZMod.val_nat_cast

theorem binary_zmod_same_as_nat {n d} (rep : Vector Bit d):
  2 ^ d < n ->
  (recover_binary_zmod rep : ZMod n).val = recover_binary_nat rep := by
  intro d_small
  rw [binary_nat_zmod_equiv_mod_p]
  apply Nat.mod_eq_of_lt
  apply @lt_trans _ _ _ (2^d)
  . apply binary_nat_lt
  . assumption

theorem binary_zmod_unique {n d} (rep1 rep2 : Vector Bit d):
  2 ^ d < n ->
  (recover_binary_zmod rep1 : ZMod n) = (recover_binary_zmod rep2 : ZMod n) ->
  rep1 = rep2 := by
  intro d_small
  intro same_recs
  have same_vals : (recover_binary_zmod rep1 : ZMod n).val = (recover_binary_zmod rep2 : ZMod n).val := by
    rw [same_recs]
  rw [binary_zmod_same_as_nat rep1 d_small] at same_vals
  rw [binary_zmod_same_as_nat rep2 d_small] at same_vals
  simp [binary_nat_unique] at same_vals
  tauto

theorem recover_binary_nat_to_bits_le {w : Vector Bit d}:
  recover_binary_nat w = v ↔
  nat_to_bits_le d v = some w := by
  apply Iff.intro
  . induction d generalizing v with
    | zero =>
      cases w using Vector.casesOn
      intro h; cases h; rfl
    | succ d ih =>
      cases w using Vector.casesOn; rename_i hd tl;
      simp [recover_binary_nat, nat_to_bits_le]
      intro h
      rw [ih (v := v/2) (w := tl)]
      . conv => lhs; whnf
        congr
        rw [←Nat.mod_add_div (m := v) (k := 2), ←mod_two_bit_back] at h
        have := And.left (parity_bit_unique _ _ _ _ h)
        apply Eq.symm
        assumption
      . subst_vars
        unfold Bit.toNat
        rw [Nat.add_div]
        cases hd
        . simp
        . simp
        . simp_arith
  . induction d generalizing v with
    | zero =>
      cases w using Vector.casesOn
      simp [recover_binary_nat, nat_to_bits_le]
      tauto
    | succ d ih =>
      cases w using Vector.casesOn
      simp [recover_binary_nat, nat_to_bits_le, Bind.bind]
      intro tl htl veq
      rw [Vector.vector_eq_cons] at veq
      cases veq
      subst_vars
      rw [ih (v := v/2)]
      . rw [mod_two_bit_back]
        simp [Nat.mod_add_div]
      . assumption

theorem recover_binary_zmod'_to_bits_le {n : Nat} [Fact (n > 1)] {v : ZMod n} {w : Vector (ZMod n) d}:
  2 ^ d < n →
  is_vector_binary w →
  recover_binary_zmod' w = v →
  nat_to_bits_le d v.val = some (vector_zmod_to_bit w) := by
  intros
  rw [←recover_binary_nat_to_bits_le]
  subst_vars
  rw [recover_binary_zmod_bit]
  . apply Eq.symm
    apply binary_zmod_same_as_nat
    assumption
  . assumption

theorem zmod_to_bit_coe {n : Nat} [Fact (n > 1)] {w : Vector Bit d} :
  vector_zmod_to_bit (Vector.map (Bit.toZMod (n := n)) w) = w := by
  induction w using Vector.inductionOn with
  | h_nil => rfl
  | h_cons ih =>
    simp [vector_zmod_to_bit] at ih
    simp [vector_zmod_to_bit, ih]
    congr
    unfold Bit.toZMod
    split <;> {
      have : n > 1 := (inferInstance : Fact (n > 1)).elim
      induction n with
      | zero =>
        apply absurd this
        simp
      | succ n =>
        induction n with
        | zero =>
          apply absurd this
          simp
        | succ =>
          rfl
    }

theorem vector_binary_of_bit_to_zmod {n : Nat} [Fact (n > 1)] {w : Vector Bit d }:
  is_vector_binary (w.map (Bit.toZMod (n := n))) := by
  induction w using Vector.inductionOn with
  | h_nil => trivial
  | h_cons ih =>
    simp [is_vector_binary_cons]
    apply And.intro
    . unfold Bit.toZMod
      split <;> {
        have : n > 1 := (inferInstance : Fact (n > 1)).elim
        induction n with
        | zero =>
          apply absurd this
          simp
        | succ n =>
          induction n with
          | zero =>
            apply absurd this
            simp
          | succ =>
            simp [is_bit]
      }
    . apply ih

theorem recover_binary_of_to_bits {n : Nat} [Fact (n > 1)] {w : Vector Bit d} {v : ZMod n}:
  nat_to_bits_le d v.val = some w →
  recover_binary_zmod' (w.map Bit.toZMod) = v := by
  rw [←recover_binary_nat_to_bits_le, recover_binary_zmod_bit, zmod_to_bit_coe]
  intro h
  rw [←binary_nat_zmod_equiv]
  rw [h]
  simp [ZMod.val_cast_of_lt]
  apply vector_binary_of_bit_to_zmod

theorem nat_to_bits_le_some_of_lt : n < 2 ^ d → ∃p, nat_to_bits_le d n = some p := by
  induction d generalizing n with
  | zero => intro h; simp at h; rw [h]; exists Vector.nil
  | succ d ih =>
    intro h
    have := ih (n := n / 2) (by
        have : 2 ^ d = (2 ^ d.succ) / 2 := by
          simp [Nat.pow_succ]
        rw [this]
        apply Nat.div_lt_div_of_lt_of_dvd
        simp [Nat.pow_succ]
        assumption
      )
    rcases this with ⟨_, h⟩
    apply Exists.intro
    unfold nat_to_bits_le
    simp [h, Bind.bind]
    rfl

def fin_to_bits_le {d : Nat} (n : Fin (2 ^ d)): Vector Bit d := match h: nat_to_bits_le d n.val with
| some r => r
| none => False.elim (by
    have := nat_to_bits_le_some_of_lt n.prop
    cases this
    simp [*] at h
  )

lemma fin_to_bits_recover_binary {D n : Nat } [Fact (n > 1)] (Index : (ZMod n)) (ix_small : Index.val < 2^D) :
  recover_binary_zmod' (Vector.map Bit.toZMod (fin_to_bits_le { val := ZMod.val Index, isLt := ix_small })) = Index := by
  rw [recover_binary_of_to_bits]
  simp [fin_to_bits_le]
  split
  . assumption
  . contradiction

lemma fin_to_bits_le_is_some {depth : Nat} {idx : Nat} (h : idx < 2 ^ depth) :
  nat_to_bits_le depth idx = some (fin_to_bits_le idx) := by
  simp [fin_to_bits_le]
  split
  . rename_i hnats
    rw [Nat.mod_eq_of_lt] at hnats
    . simp [hnats]
    . simp [h]
  . contradiction

theorem fin_to_bits_le_to_recover_binary_zmod' {n d : Nat} [Fact (n > 1)] {v : ZMod n} {w : Vector (ZMod n) d} {h : v.val < 2^d }:
  n > 2^d →
  is_vector_binary w →
  recover_binary_zmod' w = v →
  fin_to_bits_le ⟨v.val, by simp[h]⟩ = vector_zmod_to_bit w := by
  intros
  have : some (fin_to_bits_le ⟨v.val, by simp[h]⟩) = some (vector_zmod_to_bit w) := by
    rw [<-recover_binary_zmod'_to_bits_le]
    rotate_left
    linarith
    assumption
    assumption
    simp [fin_to_bits_le]
    split
    rename_i h
    simp [h]
    contradiction
  simp at this
  rw [this]

lemma vector_bit_to_zmod_last {d n : Nat} [Fact (n > 1)] {xs : Vector Bit (d+1)} :
  (zmod_to_bit (Vector.last (Vector.map (fun i => @Bit.toZMod n i) xs))) = Vector.last xs := by
  cases xs using Vector.casesOn
  simp
  rename_i x xs
  rw [<-vector_zmod_to_bit_last]
  simp
  have hx : nat_to_bit (ZMod.val (@Bit.toZMod n x)) = x := by
    simp [Bit.toZMod, is_bit, nat_to_bit]
    cases x
    . simp
    . simp [ZMod.val_one]
  have hxs : vector_zmod_to_bit (Vector.map (fun i => @Bit.toZMod n i) xs) = xs := by
    simp [vector_bit_to_zmod_to_bit]
  rw [hx, hxs]

@[elab_as_elim]
def bitCases' {n : Nat} {C : Subtype (α := ZMod n.succ.succ) is_bit → Sort _} (v : Subtype (α := ZMod n.succ.succ) is_bit)
  (zero : C bZero)
  (one : C bOne): C v := by
  rcases v with ⟨v, h⟩
  rcases v with ⟨v, _⟩
  cases v with
  | zero => exact zero
  | succ v => cases v with
    | zero => exact one
    | succ v =>
      apply False.elim
      rcases h with h | h <;> {
        injection h with h
        simp at h
      }

theorem isBitCases (b : Subtype (α := ZMod n) is_bit): b = bZero ∨ b = bOne := by
  cases b with | mk _ prop =>
  cases prop <;> {subst_vars ; tauto }


def bitCases : { v : ZMod (Nat.succ (Nat.succ n)) // is_bit v} → Bit
  | ⟨0, _⟩ => Bit.zero
  | ⟨1, _⟩ => Bit.one
  | ⟨⟨Nat.succ (Nat.succ i), _⟩, h⟩ => False.elim (by
      cases h <;> {
        rename_i h
        injection h with h;
        rw [Nat.mod_eq_of_lt] at h
        . injection h; try (rename_i h; injection h)
        . simp
      }
    )

@[simp] lemma ne_1_0 {n:Nat}: ¬(1 : ZMod (n.succ.succ)) = (0 : ZMod (n.succ.succ)) := by
  intro h;
  conv at h => lhs; whnf
  conv at h => rhs; whnf
  injection h with h
  injection h

@[simp] lemma ne_0_1 {n:Nat}: ¬(0 : ZMod (n.succ.succ)) = (1 : ZMod (n.succ.succ)) := by
  intro h;
  conv at h => lhs; whnf
  conv at h => rhs; whnf
  injection h with h
  injection h


@[simp]
lemma bitCases_eq_0 : bitCases b = Bit.zero ↔ b = bZero := by
  cases b with | mk val prop =>
  cases prop <;> {
    subst_vars
    conv => lhs; lhs; whnf
    simp
  }

@[simp]
lemma bitCases_eq_1 : bitCases b = Bit.one ↔ b = bOne := by
  cases b with | mk val prop =>
  cases prop <;> {
    subst_vars
    conv => lhs; lhs; whnf
    simp
  }

@[simp]
lemma bitCases_bZero {n:Nat}: bitCases (@bZero (n + 2)) = Bit.zero := by rfl

@[simp]
lemma bitCases_bOne {n:Nat}: bitCases (@bOne (n+2)) = Bit.one := by rfl

theorem is_vector_binary_iff_allIxes_is_bit {n : Nat} {v : Vector (ZMod n) d}: Vector.allIxes is_bit v ↔ is_vector_binary v := by
  induction v using Vector.inductionOn with
  | h_nil => simp [is_vector_binary]
  | h_cons ih => conv => lhs; simp [ih]

theorem fin_to_bits_le_recover_binary_nat {v : Vector Bit d}:
  fin_to_bits_le ⟨recover_binary_nat v, binary_nat_lt _⟩ = v := by
  unfold fin_to_bits_le
  split
  . rename_i h
    rw [←recover_binary_nat_to_bits_le] at h
    simp [binary_nat_unique] at h
    tauto
  . contradiction

theorem SubVector_map_cast_lower {v : SubVector α n prop} {f : α → β }:
  (v.val.map f) = v.lower.map fun (x : Subtype prop) => f x.val := by
  rw [←Vector.ofFn_get v.val]
  simp only [SubVector.lower, GetElem.getElem, Vector.map_ofFn]

@[simp]
theorem recover_binary_nat_fin_to_bits_le {v : Fin (2^d)}:
  recover_binary_nat (fin_to_bits_le v) = v.val := by
  unfold fin_to_bits_le
  split
  . rename_i h
    rw [←recover_binary_nat_to_bits_le] at h
    assumption
  . contradiction

@[simp]
theorem SubVector_lower_lift : SubVector.lift (SubVector.lower v) = v := by
  unfold SubVector.lift
  unfold SubVector.lower
  apply Subtype.eq
  simp [GetElem.getElem]

@[simp]
theorem SubVector_lift_lower : SubVector.lower (SubVector.lift v) = v := by
  unfold SubVector.lift
  unfold SubVector.lower
  apply Subtype.eq
  simp [GetElem.getElem]
