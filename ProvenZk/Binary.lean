import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Bitvec.Defs
import ProvenZk.Ext.List

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

theorem double_succ_ne_zero (n : Nat) : Nat.succ (Nat.succ n) ≠ 0 := by
  simp

theorem double_succ_ne_one (n : Nat) : Nat.succ (Nat.succ n) ≠ 1 := by
  simp

/-!
nat_to_bit_condition uses an hypothesis to convert from Nat to Bit.
The advantage is that the match statement doesn't require a result
for x >= 2 because bits can be only 0 or 1.
-/
def nat_to_bit_condition (x : Nat) {h : x = 0 ∨ x = 1} : Bit := match p : x with
  | 0 => Bit.zero
  | 1 => Bit.one
  | Nat.succ (Nat.succ _) => False.elim (by
    cases h with
    | inl =>
      rename_i h
      rename_i input
      apply double_succ_ne_zero input
      exact h
    | inr =>
      rename_i h
      rename_i input
      apply double_succ_ne_one input
      exact h
  )

def nat_to_bit (x : Nat) : Bit := match x with
  | 0 => Bit.zero
  | 1 => Bit.one
  | Nat.succ (Nat.succ _) => panic "Bit can only be 0 or 1"

/-!
nat_to_bit_option encapsulates Bit inside Option.
The advantage is that for x >= 2, Option is None because
Bits can only be 0 or 1
-/
def nat_to_bit_option (x : Nat) : Option Bit := match x with
  | 0 => Option.some Bit.zero
  | 1 => Option.some Bit.one
  | Nat.succ (Nat.succ _) => Option.none

def zmod_to_bit {n} (x : ZMod n) : Bit := match ZMod.val x with
  | 0 => Bit.zero
  | 1 => Bit.one
  | Nat.succ (Nat.succ _) => panic "Bit can only be 0 or 1"

def zmod_to_bit_option {n} (x : ZMod n) : Option Bit := match ZMod.val x with
  | 0 => Option.some Bit.zero
  | 1 => Option.some Bit.one
  | Nat.succ (Nat.succ _) => Option.none

@[reducible]
def is_bit (a : ZMod N): Prop := a = 0 ∨ a = 1

def is_vector_binary {d n} (x : Vector (ZMod n) d) : Prop :=
  (List.foldr (fun a r => is_bit a ∧ r) True (Vector.toList x))

/-!
is_vector_binary_reverse proves that the operation is_vector_binary is
associative
-/
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

def vector_zmod_to_bit {n d : Nat} (a : Vector (ZMod n) d) : Vector Bit d :=
  Vector.map nat_to_bit (Vector.map ZMod.val a)

def recover_binary_nat {d} (rep : Vector Bit d): Nat := match d with
  | 0 => 0
  | Nat.succ _ => rep.head.toNat + 2 * recover_binary_nat rep.tail

def recover_binary_zmod {d n} (rep : Vector Bit d) : ZMod n := match d with
  | 0 => 0
  | Nat.succ _ => rep.head.toZMod + 2 * recover_binary_zmod rep.tail

-- (ZMod n) is used in place of Bit because circuits are written with ZMod n type
def recover_binary_zmod' {d n} (rep : Vector (ZMod n) d) : ZMod n := match d with
  | 0 => 0
  | Nat.succ _ => rep.head + 2 * recover_binary_zmod' rep.tail

def is_binary_of {n d} (inp : ZMod n) (rep : Vector Bit d): Prop := inp = recover_binary_zmod rep

/-!
nat_n_bits takes two Nat: a and difits. It converts a to a (Vector Bit) with LSB at index 0.
Then takes the digits from the Vector and converts the result to Nat
-/
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

/-- Uniquiness property of binary numbers -/
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

/-- Uniquiness property of binary numbers -/
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