import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Bitvec.Defs

import ProvenZk.Ext.List
import ProvenZk.Ext.Vector

inductive Bit : Type where
  | zero : Bit
  | one : Bit
  deriving Repr, BEq

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

theorem is_vector_binary_dropLast {d n : Nat} {gate_0 : Vector (ZMod n) d} : is_vector_binary gate_0 → is_vector_binary (Vector.dropLast gate_0) := by
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

def recover_binary_zmod' {d n} (rep : Vector (ZMod n) d) : ZMod n := match d with
  | 0 => 0
  | Nat.succ _ => rep.head + 2 * recover_binary_zmod' rep.tail

@[simp]
theorem recover_binary_nat_zero {n : Nat} : recover_binary_nat (Vector.replicate n Bit.zero) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [recover_binary_nat, ih]

theorem recover_binary_zmod_bit {d n} [Fact (n > 1)]  {w : Vector (ZMod n) d}: is_vector_binary w → recover_binary_zmod' w = recover_binary_zmod (vector_zmod_to_bit w) := by
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

theorem binary_nat_unique {d} (rep1 rep2 : Vector Bit d): recover_binary_nat rep1 = recover_binary_nat rep2 -> rep1 = rep2 := by
  intro h
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
  exact binary_nat_unique _ _ same_vals

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

theorem zmod_to_bit_coe {n : Nat} [Fact (n > 1)] {w : Vector Bit d} : vector_zmod_to_bit (Vector.map (Bit.toZMod (n := n)) w) = w := by
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
          simp
          rfl
    }

theorem vector_binary_of_bit_to_zmod {n : Nat} [Fact (n > 1)] {w : Vector Bit d }: is_vector_binary (w.map (Bit.toZMod (n := n))) := by
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