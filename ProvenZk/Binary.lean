import Mathlib

inductive Bit : Type where
  | zero : Bit
  | one : Bit

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

end Bit

def recover_binary_nat {d} (rep : Vector Bit d): Nat := match d with
  | 0 => 0
  | Nat.succ _ => rep.head.toNat + 2 * recover_binary_nat rep.tail

def recover_binary_zmod {n d} (rep : Vector Bit d) : ZMod n := match d with
  | 0 => 0
  | Nat.succ _ => rep.head.toZMod + 2 * recover_binary_zmod rep.tail

def is_binary_of {n d} (inp : ZMod n) (rep : Vector Bit d): Prop := inp = recover_binary_zmod rep

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
    -- cases rep; rename_i rh rt
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