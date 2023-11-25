import Mathlib.Data.ZMod.Defs
import Mathlib.Init.Data.Nat.Bitwise

import ProvenZk.Binary

namespace Gates
variable {N : Nat}
variable [Fact (Nat.Prime N)]
def is_bool (a : ZMod N): Prop := (1-a)*a = 0 --a = 0 ∨ a = 1
def add (a b : ZMod N): ZMod N := a + b
def mul_acc (a b c : ZMod N): ZMod N := a + (b * c)
def neg (a : ZMod N): ZMod N := a * (-1)
def sub (a b : ZMod N): ZMod N := a - b
def mul (a b : ZMod N): ZMod N := a * b
def div_unchecked (a b out : ZMod N): Prop := (b ≠ 0 ∧ out*b = a) ∨ (a = 0 ∧ b = 0 ∧ out = 0) --(b ≠ 0 ∧ out = a * (1 / b)) ∨ (a = 0 ∧ b = 0 ∧ out = 0)
def div (a b out : ZMod N): Prop := b ≠ 0 ∧ out*b = a --b ≠ 0 ∧ out = a * (1 / b)
def inv (a out : ZMod N): Prop := a ≠ 0 ∧ out*a = 1 --a ≠ 0 ∧ out = 1 / a
def xor (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a+b-a*b-a*b
def or (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a+b-a*b
def and (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a*b
def select (b i1 i2 out : ZMod N): Prop := is_bool b ∧ out = i2 - b*(i2-i1) --((b = 1 ∧ out = i1) ∨ (b = 0 ∧ out = i2))
def lookup (b0 b1 i0 i1 i2 i3 out : ZMod N): Prop := is_bool b0 ∧ is_bool b1 ∧
  out = (i2 - i0) * b1 + i0 + (((i3 - i2 - i1 + i0) * b1 + i1 - i0) * b0)
/-(
  (b0 = 0 ∧ b1 = 0 ∧ out = i0) ∨
  (b0 = 1 ∧ b1 = 0 ∧ out = i1) ∨
  (b0 = 0 ∧ b1 = 1 ∧ out = i2) ∨
  (b0 = 1 ∧ b1 = 1 ∧ out = i3)
)-/
def cmp (a b : ZMod N) (out : ZMod N): Prop := (a = b ∧ out = 0) ∨
  (ZMod.val a < ZMod.val b ∧ out = -1) ∨
  (ZMod.val a > ZMod.val b ∧ out = 1)
/-
let size := binary_length N
fin_to_bits_le (a, size)
fin_to_bits_le (b, size)
-/
def is_zero (a out: ZMod N): Prop := (a ≠ 0 ∧ out = 1-(a*(1/a))) ∨ (a = 0 ∧ out = 1)  -- (a = 0 ∧ out = 1) ∨ (a != 0 ∧ out = 0)
def eq (a b : ZMod N): Prop := a = b
def ne (a b : ZMod N): Prop := a ≠ b
def le (a b : ZMod N): Prop := ZMod.val a <= ZMod.val b
def to_binary (a : ZMod N) (n : Nat) (out : Vector (ZMod N) n): Prop := (recover_binary_zmod' out : ZMod N) = a ∧ is_vector_binary out
def from_binary {d} (a : Vector (ZMod N) d) (out : ZMod N): Prop := (recover_binary_zmod' a : ZMod N) = out
end Gates


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

theorem inv_self_eq_one (a : ZMod N) : a ≠ 0 → (a⁻¹) * a = 1 := by
  intro h
  simp [mul_comm]
  apply mul_inv_cancel_aux_copy
  tauto

@[simp]
lemma is_bool_equivalence {a : ZMod N} :
  Gates.is_bool a ↔ a = 0 ∨ a = 1 := by
  unfold Gates.is_bool
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
  Gates.div a b out ↔ b ≠ 0 ∧ out = a * (1 / b) := by
  unfold Gates.div
  rw [and_congr_right_iff]
  intro h
  rw [one_div, eq_mul_sides]
  rw [mul_assoc, inv_self_eq_one, mul_one]
  . tauto
  . tauto

@[simp]
lemma div_unchecked_equivalence {a b out : ZMod N} :
  Gates.div_unchecked a b out ↔ ((b ≠ 0 ∧ out = a * (1 / b)) ∨ (a = 0 ∧ b = 0 ∧ out = 0)) := by
  unfold Gates.div_unchecked
  rw [<-Gates.div]
  rw [<-div_equivalence]

@[simp]
lemma inv_equivalence {a out : ZMod N} :
  Gates.inv a out ↔ a ≠ 0 ∧ out = 1 / a := by
  unfold Gates.inv
  rw [one_div, and_congr_right_iff]
  intro h
  conv => rhs; rw [<-mul_one (a := a⁻¹)]; rw [mul_comm]
  rw [eq_mul_sides]
  rw [mul_assoc, inv_self_eq_one, mul_one]
  . tauto
  . tauto

@[simp]
lemma xor_equivalence {a b out : ZMod N} :
  Gates.xor a b out ↔
  (a = 0 ∧ b = 0 ∧ out = 0) ∨
  (a = 0 ∧ b = 1 ∧ out = 1) ∨
  (a = 1 ∧ b = 0 ∧ out = 1) ∨
  (a = 1 ∧ b = 1 ∧ out = 0) := by
  unfold Gates.xor
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
      simp [Gates.is_bool]
    )

@[simp]
lemma or_equivalence {a b out : ZMod N} :
  Gates.or a b out ↔
  (a = 0 ∧ b = 0 ∧ out = 0) ∨
  (a = 0 ∧ b = 1 ∧ out = 1) ∨
  (a = 1 ∧ b = 0 ∧ out = 1) ∨
  (a = 1 ∧ b = 1 ∧ out = 1) := by
  unfold Gates.or
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
      simp [Gates.is_bool]
    )

@[simp]
lemma and_equivalence {a b out : ZMod N} :
  Gates.and a b out ↔
  (a = 0 ∧ b = 0 ∧ out = 0) ∨
  (a = 0 ∧ b = 1 ∧ out = 0) ∨
  (a = 1 ∧ b = 0 ∧ out = 0) ∨
  (a = 1 ∧ b = 1 ∧ out = 1) := by
  unfold Gates.and
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
  Gates.select b i1 i2 out ↔ (b = 0 ∨ b = 1) ∧ if b = 1 then out = i1 else out = i2 := by
  unfold Gates.select
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
  Gates.select b i1 i2 out ↔ (b = 1 ∧ out = i1) ∨ (b = 0 ∧ out = i2) := by
  unfold Gates.select
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
  Gates.lookup b0 b1 i0 i1 i2 i3 out ↔
  (b0 = 0 ∧ b1 = 0 ∧ out = i0) ∨
  (b0 = 1 ∧ b1 = 0 ∧ out = i1) ∨
  (b0 = 0 ∧ b1 = 1 ∧ out = i2) ∨
  (b0 = 1 ∧ b1 = 1 ∧ out = i3) := by
  unfold Gates.lookup
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

@[simp]
lemma cmp_equivalence : sorry := by sorry -- TODO

@[simp]
lemma is_zero_equivalence {a out: ZMod N} :
  Gates.is_zero a out ↔ if a = 0 then out = 1 else out = 0 := by
  unfold Gates.is_zero
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
  Gates.is_zero a out ↔ (a = 0 ∧ out = 1) ∨ (a ≠ 0 ∧ out = 0) := by
  unfold Gates.is_zero
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
lemma le_equivalence : sorry := by sorry -- TODO

@[simp]
lemma to_binary_equivalence : sorry := by sorry -- TODO

@[simp]
lemma from_binary_equivalence : sorry := by sorry -- TODO

end GatesEquivalence

/-
Goal : calling Gates.cmp and Lean automatically switching between different implementations
of the gate depending on gnark versions.
The gnark version is determined by the extractor.
Use typeclasses
-/
namespace Ex
variable {N : Nat}
variable [Fact (Nat.Prime N)]

class Cmp (a : Type) where
  cmp : a → a → a → Prop

instance : Cmp (ZMod N) where
  cmp := Gates.cmp

end Ex
