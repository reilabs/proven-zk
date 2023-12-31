import Init.Prelude
import Mathlib.Data.ZMod.Defs
import Mathlib.Init.Data.Nat.Bitwise

import ProvenZk.Binary
import ProvenZk.Gates

namespace GatesEquivalence
variable {N : Nat}
variable [Fact (Nat.Prime N)]

theorem zmod_symm {n} {a b : ZMod n} : a = b ↔ b = a := by
  tauto

theorem mul_inv_cancel_aux_copy (a : ZMod N) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  obtain ⟨k, rfl⟩ := ZMod.nat_cast_zmod_surjective a
  apply ZMod.coe_mul_inv_eq_one
  apply Nat.Coprime.symm
  rwa [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod N)]

theorem inv_self_eq_one (a : ZMod N) : a ≠ 0 → (a⁻¹) * a = 1 := by
  intro h
  simp [mul_comm]
  apply mul_inv_cancel_aux_copy
  tauto

theorem eq_mul_sides (a b out: ZMod N) : b ≠ 0 → ((out = a * b⁻¹) ↔ (out*b = a*(b⁻¹)*b)) := by
    intro
    apply Iff.intro
    . intro h
      rw [h]
    . intro h
      simp at h
      cases h
      . tauto
      . contradiction

lemma split_vector_eq_cons {x : α} {xs : Vector α d} {y : Vector α d.succ} :
  x ::ᵥ xs = y ↔ x = y.head ∧ xs = y.tail := by
  apply Iff.intro
  . intro h
    rw [<-h]
    simp
  . intro h
    casesm* (_ ∧ _)
    rename_i hx hxs
    rw [hx, hxs]
    simp

def nat_to_binary_self {d : Nat} :
  recover_binary_nat (nat_to_bits_le_full_n d x) = x % 2^d := by
  induction d generalizing x with
  | zero =>
    simp [recover_binary_nat, nat_to_bits_le_full_n, Nat.mod_one]
  | succ d' ih =>
    simp [recover_binary_nat, nat_to_bits_le_full_n]
    have : recover_binary_nat (nat_to_bits_le_full_n d' (x / 2)) = (x/2) % 2^d' := by
      if d' >= 1 then
        rw [ih (x := x/2)]
      else
        rename_i h
        simp at h
        subst_vars
        simp [nat_to_bits_le_full_n, recover_binary_nat, Nat.mod_one]
    rw [this]
    rw [<-Nat.div2_val]
    simp [bit_mod_two]
    split
    . rename_i h
      simp only [Bit.toNat]
      rw [Nat.mod_pow_succ]
      rw [<-Nat.div2_val]
      rw [h]
      simp_arith
    . rename_i h
      simp only [Bit.toNat]
      rw [Nat.mod_pow_succ]
      rw [<-Nat.div2_val]
      rw [h]
      simp_arith
    . rename_i h
      apply False.elim (by
        have := Nat.mod_lt x (y := 2)
        rw [h] at this
        simp at this
        contradiction
      )

lemma one_plus_one : x+1+1 = x+2 := by simp_arith

lemma nat_succ_div_two : n.succ.succ / 2 = Nat.succ (n/2) := by
  simp_arith

lemma log2_mul {n} : 2 * 2 ^ Nat.log 2 n > n := by
  rw [<-pow_succ]
  rw [add_comm]
  rw [<-Nat.succ_eq_one_add]
  simp
  apply Nat.lt_pow_succ_log_self
  simp

lemma binary_lt_two_pow_length {n : Nat} : 2^(binary_length n) > n := by
  induction n with
  | zero => simp
  | succ n' _ =>
    conv => rhs; rw [Nat.succ_eq_one_add]
    rw [binary_length]
    conv => lhs; arg 2; arg 1; rw [Nat.succ_eq_one_add]
    rw [Nat.succ_eq_one_add, add_comm, pow_succ]
    apply log2_mul

@[simp]
lemma is_bool_equivalence {a : ZMod N} :
  GatesDef.is_bool a ↔ a = 0 ∨ a = 1 := by
  unfold GatesDef.is_bool
  simp
  have : 1-a = 0 ↔ 1-a+a = a := by
    apply Iff.intro
    . intro h
      rw [h]
      simp
    . intro h
      rw [add_left_eq_self] at h
      simp [h]
  rw [this]
  conv => lhs; arg 1; simp; rw [zmod_symm]
  tauto

@[simp]
lemma div_equivalence {a b out : ZMod N} :
  GatesDef.div a b out ↔ b ≠ 0 ∧ out = a * (1 / b) := by
  unfold GatesDef.div
  rw [and_congr_right_iff]
  intro h
  rw [one_div, eq_mul_sides]
  rw [mul_assoc, inv_self_eq_one, mul_one]
  . tauto
  . tauto

@[simp]
lemma div_unchecked_equivalence {a b out : ZMod N} :
  GatesDef.div_unchecked a b out ↔ ((b ≠ 0 ∧ out = a * (1 / b)) ∨ (a = 0 ∧ b = 0 ∧ out = 0)) := by
  unfold GatesDef.div_unchecked
  rw [<-GatesDef.div]
  rw [<-div_equivalence]

@[simp]
lemma inv_equivalence {a out : ZMod N} :
  GatesDef.inv a out ↔ a ≠ 0 ∧ out = 1 / a := by
  unfold GatesDef.inv
  rw [one_div, and_congr_right_iff]
  intro h
  conv => rhs; rw [<-mul_one (a := a⁻¹)]; rw [mul_comm]
  rw [eq_mul_sides]
  rw [mul_assoc, inv_self_eq_one, mul_one]
  . tauto
  . tauto

@[simp]
lemma xor_equivalence {a b out : ZMod N} :
  GatesDef.xor a b out ↔
  (a = 0 ∧ b = 0 ∧ out = 0) ∨
  (a = 0 ∧ b = 1 ∧ out = 1) ∨
  (a = 1 ∧ b = 0 ∧ out = 1) ∨
  (a = 1 ∧ b = 1 ∧ out = 0) := by
  unfold GatesDef.xor
  apply Iff.intro
  . intro h
    simp at h
    casesm* (_ ∧ _)
    rename_i ha hb _
    cases ha <;> cases hb <;> {
      subst_vars
      simp
    }
  . intro h
    casesm* (_ ∨ _)
    repeat (
      casesm* (_ ∧ _)
      subst_vars
      simp [GatesDef.is_bool]
    )

@[simp]
lemma or_equivalence {a b out : ZMod N} :
  GatesDef.or a b out ↔
  (a = 0 ∧ b = 0 ∧ out = 0) ∨
  (a = 0 ∧ b = 1 ∧ out = 1) ∨
  (a = 1 ∧ b = 0 ∧ out = 1) ∨
  (a = 1 ∧ b = 1 ∧ out = 1) := by
  unfold GatesDef.or
  apply Iff.intro
  . intro h
    simp at h
    casesm* (_ ∧ _)
    rename_i ha hb _
    cases ha <;> cases hb <;> {
      subst_vars
      simp
    }
  . intro h
    casesm* (_ ∨ _)
    repeat (
      casesm* (_ ∧ _)
      subst_vars
      simp [GatesDef.is_bool]
    )

@[simp]
lemma and_equivalence {a b out : ZMod N} :
  GatesDef.and a b out ↔
  (a = 0 ∧ b = 0 ∧ out = 0) ∨
  (a = 0 ∧ b = 1 ∧ out = 0) ∨
  (a = 1 ∧ b = 0 ∧ out = 0) ∨
  (a = 1 ∧ b = 1 ∧ out = 1) := by
  unfold GatesDef.and
  rw [is_bool_equivalence]
  rw [is_bool_equivalence]
  apply Iff.intro
  . intro h
    simp at h
    casesm* (_ ∧ _)
    rename_i ha hb _
    cases ha <;> cases hb <;> {
      subst_vars
      simp
    }
  . intro h
    casesm* (_ ∨ _)
    repeat (
      casesm* (_ ∧ _)
      subst_vars
      simp
    )

@[simp]
lemma select_equivalence {b i1 i2 out : ZMod N} :
  GatesDef.select b i1 i2 out ↔ (b = 0 ∨ b = 1) ∧ if b = 1 then out = i1 else out = i2 := by
  unfold GatesDef.select
  rw [is_bool_equivalence]
  apply Iff.intro
  . intro h
    casesm* (_ ∧ _)
    rename_i hb _
    cases hb
    repeat (
      subst_vars
      simp
    )
  . intro h
    casesm* (_ ∧ _)
    rename_i hb hout
    cases hb
    repeat (
      subst_vars
      simp
      simp at hout
      tauto
    )

@[simp]
lemma select_equivalence' {b i1 i2 out : ZMod N} :
  GatesDef.select b i1 i2 out ↔ (b = 1 ∧ out = i1) ∨ (b = 0 ∧ out = i2) := by
  unfold GatesDef.select
  rw [is_bool_equivalence]
  apply Iff.intro
  . intro h
    casesm* (_ ∧ _)
    rename_i hb _
    cases hb
    repeat (
      subst_vars
      simp
    )
  . intro h
    casesm* (_ ∨ _)
    repeat (
      casesm* (_ ∧ _)
      subst_vars
      simp
    )

@[simp]
lemma lookup_equivalence {b0 b1 i0 i1 i2 i3 out : ZMod N} :
  GatesDef.lookup b0 b1 i0 i1 i2 i3 out ↔
  (b0 = 0 ∧ b1 = 0 ∧ out = i0) ∨
  (b0 = 1 ∧ b1 = 0 ∧ out = i1) ∨
  (b0 = 0 ∧ b1 = 1 ∧ out = i2) ∨
  (b0 = 1 ∧ b1 = 1 ∧ out = i3) := by
  unfold GatesDef.lookup
  rw [is_bool_equivalence]
  rw [is_bool_equivalence]
  apply Iff.intro
  . intro h
    casesm* (_ ∧ _)
    rename_i hb0 hb1 _
    cases hb0 <;> cases hb1 <;> {
      subst_vars
      simp [add_assoc]
    }
  . intro h
    casesm* (_ ∨ _)
    repeat (
      casesm* (_ ∧ _)
      subst_vars
      simp [add_assoc]
    )

--#eval (3:ZMod 9) = (12:ZMod 9)

@[simp]
lemma cmp_equivalence {a b out : ZMod N} :
  GatesDef.cmp_9 a b out ↔ if a = b then out = 0 else (if a.val < b.val then out = -1 else out = 1) := by
  unfold GatesDef.cmp_9
  apply Iff.intro
  . intro h
    casesm* (_ ∧ _)
    split
    . casesm* (_ ∨ _)
      . tauto
      . casesm* (_ ∧ _)
        rename_i heq hlt _
        have : a.val = b.val := by
          apply congrArg (h := heq)
        apply False.elim (by
          linarith
        )
      . casesm* (_ ∧ _)
        rename_i heq hlt _
        have : a.val = b.val := by
          apply congrArg (h := heq)
        apply False.elim (by
          linarith
        )
    . split
      . casesm* (_ ∨ _)
        . casesm* (_ ∧ _)
          rename_i hlt heq _
          have : a.val = b.val := by
            apply congrArg (h := heq)
          apply False.elim (by
            linarith
          )
        . tauto
        . casesm* (_ ∧ _)
          apply False.elim (by
            linarith
          )
      . casesm* (_ ∨ _)
        . apply False.elim (by
            tauto
          )
        . apply False.elim (by
            tauto
          )
        . tauto
  . intro h
    have : 2^(binary_length N) > N := by
      apply binary_lt_two_pow_length
    simp only [nat_to_binary_self]
    simp only [<-ZMod.val_nat_cast]
    refine ⟨?_, ?_, ?_⟩
    . rw [ZMod.val_nat_cast_of_lt]
      have : a.val < N := by
        simp [ZMod.val_lt]
      linarith
    . rw [ZMod.val_nat_cast_of_lt]
      have : b.val < N := by
        simp [ZMod.val_lt]
      linarith
    . if a = b then
        subst_vars
        simp at h
        simp
        tauto
      else
        if ZMod.val a < ZMod.val b then
          rename_i hne hle
          simp [hle, hne] at h
          simp [*]
        else
          rename_i hne hnle
          simp [hne, hnle] at h
          simp [*]
          simp at hnle
          if hval : ZMod.val a = ZMod.val b then
            have : a = b := by
              rw [<-ZMod.nat_cast_zmod_val (a := a)]
              rw [<-ZMod.nat_cast_zmod_val (a := b)]
              rw [hval]
            apply False.elim (by
              contradiction
            )
          else
            apply lt_of_le_of_ne
            . tauto
            . tauto

@[simp]
lemma is_zero_equivalence {a out: ZMod N} :
  GatesDef.is_zero a out ↔ if a = 0 then out = 1 else out = 0 := by
  unfold GatesDef.is_zero
  rw [one_div, mul_comm]
  apply Iff.intro
  . intro h
    casesm* (_ ∨ _)
    . casesm* (_ ∧ _)
      subst_vars
      rename_i h
      . simp [h]
    . casesm* (_ ∧ _)
      subst_vars
      simp
  . intro h
    if a = 0 then
      subst_vars
      simp at h
      tauto
    else
      rename_i ha
      simp [ha] at h
      simp [ha]
      tauto

@[simp]
lemma is_zero_equivalence' {a out: ZMod N} :
  GatesDef.is_zero a out ↔ (a = 0 ∧ out = 1) ∨ (a ≠ 0 ∧ out = 0) := by
  unfold GatesDef.is_zero
  rw [one_div, mul_comm]
  apply Iff.intro
  . intro h
    casesm* (_ ∨ _)
    . casesm* (_ ∧ _)
      subst_vars
      rw [inv_self_eq_one, sub_self]
      . tauto
      . tauto
    . casesm* (_ ∧ _)
      subst_vars
      simp
  . intro h
    casesm* (_ ∨ _)
    . casesm* (_ ∧ _)
      subst_vars
      simp
    . casesm* (_ ∧ _)
      subst_vars
      rw [inv_self_eq_one, sub_self]
      . tauto
      . tauto

@[simp]
lemma le_equivalence {a b : ZMod N} :
  GatesDef.le_9 a b ↔ a.val <= b.val := by
  unfold GatesDef.le_9
  apply Iff.intro
  . intro h
    tauto
  . intro h
    have : 2^(binary_length N) > N := by
      apply binary_lt_two_pow_length
    simp only [nat_to_binary_self]
    simp only [<-ZMod.val_nat_cast]
    refine ⟨?_, ?_, ?_⟩
    . rw [ZMod.val_nat_cast_of_lt]
      have : a.val < N := by
        simp [ZMod.val_lt]
      linarith
    . rw [ZMod.val_nat_cast_of_lt]
      have : b.val < N := by
        simp [ZMod.val_lt]
      linarith
    . tauto

-- Should `hd : 2^d < N` be a hypothesis?
@[simp]
lemma to_binary_equivalence {a : ZMod N} {d : Nat} {out : Vector (ZMod N) d} (hd : 2^d < N) :
  GatesDef.to_binary a d out ↔ vector_bit_to_zmod (nat_to_bits_le_full_n d a.val) = out := by
  apply Iff.intro
  . intro h
    unfold GatesDef.to_binary at h
    casesm* (_ ∧ _)
    rename_i h hbin
    rw [recover_binary_zmod_bit] at h
    rw [binary_nat_zmod_equiv_mod_p] at h
    rw [<-ZMod.val_nat_cast] at h
    rw [ZMod.val_nat_cast_of_lt] at h
    . induction d generalizing a with
      | zero => simp
      | succ d' _ =>
        rw [<-nat_to_binary_self] at h
        . simp [binary_nat_unique] at h
          rw [bit_to_zmod_equiv]
          rw [h]
          simp [hbin]
    . rw [<-@binary_zmod_same_as_nat (n := N) (d := d) (rep := vector_zmod_to_bit out)]
      . apply ZMod.val_lt
      . simp [hd]
    . simp [hbin]
  . unfold GatesDef.to_binary
    intro h
    have hbin : is_vector_binary out := by
      rw [<-h]
      rw [vector_bit_to_zmod]
      simp [vector_binary_of_bit_to_zmod]
    rw [recover_binary_zmod_bit]
    rw [binary_nat_zmod_equiv_mod_p]
    rw [<-ZMod.val_nat_cast]
    rw [ZMod.val_nat_cast_of_lt]
    refine ⟨?_, ?_⟩
    . induction d generalizing a with
      | zero =>
        simp [Nat.mod_one]
        simp [vector_zmod_to_bit, recover_binary_nat]
      | succ d' _ =>
        rw [<-nat_to_binary_self]
        . simp [binary_nat_unique]
          apply Eq.symm
          rw [<-bit_to_zmod_equiv]
          . rw [h]
          . simp [hbin]
    . simp [hbin]
    . rw [<-@binary_zmod_same_as_nat (n := N) (d := d) (rep := vector_zmod_to_bit out)]
      . apply ZMod.val_lt
      . simp [hd]
    . simp [hbin]

-- Should `hd : 2^d < N` be a hypothesis?
@[simp]
lemma from_binary_equivalence {d} {a : Vector (ZMod N) d} {out : ZMod N} (hd : 2^d < N)  :
  GatesDef.from_binary a out ↔ vector_bit_to_zmod (nat_to_bits_le_full_n d out.val) = a := by
  unfold GatesDef.from_binary
  rw [<-GatesDef.to_binary]
  apply to_binary_equivalence (hd := hd)

end GatesEquivalence
