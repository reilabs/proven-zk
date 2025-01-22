import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Vector.Mem
import Mathlib.Data.Vector.MapLemmas
import Mathlib.Data.Nat.Log

import ProvenZk.Ext.List
import ProvenZk.Ext.Vector

open BigOperators

@[reducible]
def is_bit (a : ZMod N): Prop := a = 0 ∨ a = 1

@[simp]
theorem is_bit_zero : is_bit (0 : ZMod n) := by tauto

@[simp]
theorem is_bit_one : is_bit (1 : ZMod n) := by tauto

def Bool.toZMod {N} (b : Bool) : ZMod N := b.toNat

def Bool.ofZMod {N} (b : ZMod N) : Bool := Bool.ofNat b.val

@[simp]
lemma Bool.toZMod_zero {N} : Bool.toZMod false = (0  : ZMod N) := by
  simp [Bool.toZMod, Bool.toNat]

@[simp]
lemma Bool.toZMod_one {N} : Bool.toZMod true = (1  : ZMod N) := by
  simp [Bool.toZMod, Bool.toNat]

@[simp]
lemma Bool.toZMod_is_bit {N} : is_bit (toZMod (N:=N) b) := by
  cases b <;> simp [is_bit, toZMod, toNat]


@[simp]
theorem Bool.toZMod_eq_one_iff_eq_true {n:ℕ} [Fact (n > 1)] : (Bool.toZMod a : ZMod n) = 1 ↔ a = true := by
  cases a <;> simp

@[simp]
theorem Bool.toZMod_eq_one_iff_eq_false {n:ℕ} [Fact (n > 1)] : (Bool.toZMod a : ZMod n) = 0 ↔ a = false := by
  cases a <;> simp

@[simp]
lemma Bool.ofZMod_toZMod_eq_self {b} [Fact (N > 1)]: Bool.ofZMod (Bool.toZMod (N:=N) b) = b := by
  cases b <;> simp [toZMod, ofZMod, ofNat, toNat]

@[simp]
lemma Bool.toZMod_ofZMod_eq_self_of_is_bit {N} [Fact (N > 1)] {i : ZMod N} (h : is_bit i):
  Bool.toZMod (Bool.ofZMod i) = i := by
  cases h <;> {simp [*, ofZMod, toZMod, ofNat, toNat]}

def is_vector_binary {d n} (x : List.Vector (ZMod n) d) : Prop := ∀ a ∈ x, is_bit a

@[simp]
lemma is_vector_binary_reverse {depth} (ix : List.Vector (ZMod n) depth):
  is_vector_binary ix.reverse ↔ is_vector_binary ix := by
  simp [is_vector_binary, List.Vector.toList_reverse]

theorem is_vector_binary_cons {a : ZMod n} {vec : List.Vector (ZMod n) d}:
  is_vector_binary (a ::ᵥ vec) ↔ is_bit a ∧ is_vector_binary vec := by
  simp [is_vector_binary]

lemma is_vector_binary_snoc {N : ℕ} {vs : List.Vector (ZMod N) n} {v}: is_vector_binary (vs.snoc v) ↔ is_vector_binary vs ∧ is_bit v := by
  simp [is_vector_binary]
  apply Iff.intro
  . intro h
    exact ⟨(fun a ha => h a (Or.inl ha)), h v (Or.inr rfl)⟩
  . intro h
    rcases h with ⟨hl, hr⟩
    intro a ha
    cases ha
    . apply hl; assumption
    . subst_vars; assumption

@[simp]
lemma is_vector_binary_map_toZMod {N n : ℕ} {v : List.Vector Bool n}: is_vector_binary (List.Vector.map (Bool.toZMod (N := N)) v) := by
  simp [is_vector_binary]
  tauto

lemma is_vector_binary_iff_exists_bool_vec {N n : ℕ} {v : List.Vector (ZMod N) n}:
  is_vector_binary v ↔ ∃x : List.Vector Bool n, v = x.map Bool.toZMod := by
  induction n with
  | zero =>
    cases v using List.Vector.casesOn
    simp [is_vector_binary]
    exists List.Vector.nil
  | succ n ih =>
    cases v using List.Vector.casesOn with | cons hd tl =>
    simp only [is_vector_binary_cons, ih]
    apply Iff.intro
    . intro ⟨bhd, ⟨tl, btl⟩⟩
      cases bhd with
      | inl hz =>
        exists (false ::ᵥ tl)
        simp [*]
      | inr ho =>
        exists true ::ᵥ tl
        simp [*]
    . intro ⟨x, hx⟩
      cases x using List.Vector.casesOn with | cons hd' tl' =>
      simp at hx
      injection hx with hx
      injection hx with hx htl
      simp [hx]
      exists tl'
      apply List.Vector.eq
      simp [List.Vector.toList, htl]
      rfl

def recover_binary_zmod' {d n} (rep : List.Vector (ZMod n) d) : ZMod n := match d with
  | 0 => 0
  | Nat.succ _ => rep.head + 2 * recover_binary_zmod' rep.tail

def binary_length (n : Nat) : Nat := (Nat.log 2 n).succ

namespace Fin

def msb {d:ℕ} (v : Fin (2^d.succ)): Bool := v.val ≥ 2^d

@[simp]
theorem msb_false_of_lt {d:ℕ} {v : Fin (2^d.succ)} (h : v.val < 2^d): msb v = false := by
  simpa [msb]

@[simp]
theorem msb_true_of_ge {d:ℕ} {v : Fin (2^d.succ)} (h : v.val ≥ 2^d): msb v = true := by
  simpa [msb]

def lsbs {d:ℕ} (v : Fin (2^d.succ)): Fin (2^d) := ⟨v.val - (msb v).toNat * 2^d, prop⟩ where
  prop := by
    cases Nat.lt_or_ge v.val (2^d) with
    | inl lt =>
      simp [lt, Bool.toNat]
    | inr ge =>
      apply Nat.sub_lt_left_of_lt_add
      . simp [msb, ge, Bool.toNat]
      . have : 2^d + 2^d = 2^d.succ := by simp_arith [pow_succ, Nat.mul_comm]
        simp [msb, ge, Bool.toNat, v.prop, this]

private lemma snoc_step_helper {d : ℕ} {b : Bool} {v : Fin (2^d)}:
  b.toNat + 2 * v.val < 2^d.succ := by
  have : b.toNat ≤ 1 := by cases b <;> simp
  simp_arith
  calc
    b.toNat + 2 * v.val + 1 ≤ 2 * v.val + 2 := by cases b <;> { simp_arith }
    _ = 2 * (v.val + 1) := by simp_arith
    _ ≤ 2 * 2^d := by
      have := Fin.prop v
      simp_arith [-Fin.is_lt] at this
      simp_arith [this]
      linarith
    _ = 2^(d+1) := by simp [pow_succ, Nat.mul_comm]

private lemma cons_step_helper {d : ℕ} {b : Bool} {v : Fin (2^d)}:
  b.toNat * 2^d + v.val < 2^d.succ := by
  have : 2 ^ d.succ = 2^d + 2^d := by simp_arith [pow_succ, Nat.mul_comm]
  apply Nat.add_lt_add_of_le_of_lt
  . cases b <;> simp
  . apply Fin.is_lt

theorem msbs_lsbs_decomposition {d} {v : Fin (2^d.succ)}:
  v = ⟨(msb v).toNat * 2^d + (lsbs v).val, cons_step_helper⟩  := by
    cases Decidable.em (v.val ≥ 2^d) <;> simp [msb, lsbs, *, Bool.toNat]

theorem msb_lsbs_decomposition_unique {d}  {v : Fin (2^d.succ)} {msb' : Bool} {lsbs' : Fin (2^d)} {h}:
  v = ⟨(msb'.toNat * 2^d) + lsbs'.val, h⟩ ↔ msb' = msb v ∧ lsbs' = lsbs v := by
  apply Iff.intro
  . rintro ⟨_⟩
    apply And.intro
    . cases msb' <;> {
        simp [msb, Bool.toNat]
      }
    . cases msb' <;> {
      have : ¬ 2^d ≤ lsbs'.val := not_le_of_lt (Fin.is_lt lsbs')
      simp [lsbs, Bool.toNat, msb, this]
    }
  . rintro ⟨⟨_⟩, ⟨_⟩⟩
    apply Fin.eq_of_val_eq
    cases Decidable.em (2^d ≤ v.val) <;> simp [msb, lsbs, *, Bool.toNat]

@[simp]
theorem lsbs_of_msb_lsbs_decomposition {d} {msb' : Bool} {lsbs' : Fin (2^d)} {h}:
  lsbs ⟨(msb'.toNat * 2^d) + lsbs'.val, h⟩ = lsbs' := by
  apply eq_comm.mp
  refine (msb_lsbs_decomposition_unique.mp (Eq.refl _)).2

@[simp]
theorem msb_of_msb_lsbs_decomposition {d} {msb' : Bool} {lsbs' : Fin (2^d)} {h}:
  msb (⟨(msb'.toNat * 2^d) + lsbs'.val, h⟩: Fin (2^d.succ)) = msb' := by
  apply eq_comm.mp
  refine (msb_lsbs_decomposition_unique.mp (Eq.refl _)).1

def toBitsBE {d : ℕ} (v : Fin (2^d)): List.Vector Bool d := match d with
  | 0 => List.Vector.nil
  | Nat.succ _ => msb v ::ᵥ (lsbs v).toBitsBE

def toBitsLE {d : ℕ} (v : Fin (2^d)): List.Vector Bool d := v.toBitsBE.reverse

@[simp]
theorem lsbs_eq_val_of_lt {d:ℕ} {v : Fin (2^d.succ)} (h : v.val < 2^d): lsbs v = ⟨v, h⟩ := by
  simp [lsbs, *, Bool.toNat]

def ofBitsBE {d : ℕ} (v : List.Vector Bool d): Fin (2^d) := match d with
  | 0 => ⟨0, by decide⟩
  | d + 1 =>
    let proof := by
      have : 2^d.succ = 2^d + 2^d := by simp_arith [pow_succ, Nat.mul_comm]
      rw [this]
      apply Nat.add_lt_add_of_le_of_lt
      . cases v.head <;> simp
      . apply Fin.prop
    ⟨(v.head.toNat * 2^d + (ofBitsBE v.tail).val), proof⟩

theorem ofBitsBE_snoc {d : ℕ} {v : Bool} {vs : List.Vector Bool d}:
  ofBitsBE (vs.snoc v) = ⟨v.toNat + 2 * (ofBitsBE vs).val, snoc_step_helper⟩ := by
  induction d with
  | zero =>
    cases vs using List.Vector.casesOn
    simp [ofBitsBE]
  | succ d ih =>
    unfold ofBitsBE
    simp_arith [List.Vector.tail_snoc, List.Vector.head_snoc, ih, Nat.pow_succ]
    cases vs.head <;> simp_arith [Bool.toNat]

def ofBitsLE {d : ℕ} (v : List.Vector Bool d): Fin (2^d) := ofBitsBE v.reverse

@[simp]
lemma lsbs_ofBitsBE_eq_ofBitsBE_tail {d : ℕ} {v : List.Vector Bool d.succ}:
  lsbs (ofBitsBE v) = ofBitsBE v.tail := by
  induction d with
  | zero =>
    cases v using List.Vector.casesOn
    rename_i hd _
    cases hd <;> rfl
  | succ d ih =>
    cases v using List.Vector.casesOn with | cons hd tl =>
    rw [ofBitsBE]
    simp [ih]

@[simp]
lemma msb_ofBitsBE_eq_head {d : ℕ} {v : List.Vector Bool d.succ}:
  msb (ofBitsBE v) = v.head := by
  cases v using List.Vector.casesOn with | cons hd tl =>
  rw [ofBitsBE]
  simp

@[simp]
lemma toBitsBE_ofBitsBE_eq_self {d : ℕ} {v : List.Vector Bool d}:
  toBitsBE (ofBitsBE v) = v := by
  induction d with
  | zero => cases v using List.Vector.casesOn; rfl
  | succ d ih => simp [toBitsBE, ih]

@[simp]
lemma toBitsLE_ofBitsLE_eq_self {d : ℕ} {v : List.Vector Bool d}:
  toBitsLE (ofBitsLE v) = v := by
  simp [toBitsLE, ofBitsLE]

@[simp]
lemma ofBitsBE_toBitsBE_eq_self {d : ℕ} {v : Fin (2^d)}:
  ofBitsBE (toBitsBE v) = v := by
  induction d with
  | zero =>
    cases v with | mk _ p =>
    simp at p
    cases p
    rfl
  | succ d ih =>
    rw [msbs_lsbs_decomposition (v := v)]
    simp [toBitsBE, ofBitsBE, ih]

@[simp]
lemma ofBitsLE_toBitsLE_eq_self {d : ℕ} {v : Fin (2^d)}:
  ofBitsLE (toBitsLE v) = v := by
  simp [toBitsLE, ofBitsLE]

@[simp]
lemma toBitsBE_injective : toBitsBE a = toBitsBE b ↔ a = b := by
  apply Iff.intro
  . intro h
    have := congrArg ofBitsBE h
    simp at this
    assumption
  . intro; simp [*]

@[simp]
lemma toBitsLE_injective : toBitsLE a = toBitsLE b ↔ a = b := by
  simp [toBitsLE]

end Fin

theorem recover_binary_zmod'_map_toZMod_eq_Fin_ofBitsLE {N l : ℕ} {v : List.Vector Bool l}:
  recover_binary_zmod' (List.Vector.map (Bool.toZMod (N := N)) v) = (Fin.ofBitsLE v).val := by
  induction l with
  | zero => simp [recover_binary_zmod']
  | succ l ih =>
    cases v using List.Vector.casesOn with | cons hd tl =>
    simp [recover_binary_zmod', Fin.ofBitsLE, Fin.ofBitsBE_snoc, ih]
    rfl
