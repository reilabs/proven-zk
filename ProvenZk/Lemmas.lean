import ProvenZk.Gates
import ProvenZk.Binary

import Mathlib.Data.Vector.MapLemmas
import Mathlib

variable {N : Nat}
variable [Fact (Nat.Prime N)]

instance : Fact (N > 1) := ⟨Nat.Prime.one_lt Fact.out⟩

theorem ZMod.eq_of_veq {a b : ZMod N} (h : a.val = b.val) : a = b := by
  have : N ≠ 0 := by apply Nat.Prime.ne_zero Fact.out
  have : ∃n, N = Nat.succ n := by exists N.pred; simp [Nat.succ_pred this]
  rcases this with ⟨_, ⟨_⟩⟩
  simp [val] at h
  exact Fin.eq_of_veq h


theorem ZMod.val_fin {n : ℕ} {i : ZMod (Nat.succ n)} : i.val = Fin.val i := by
  simp [ZMod.val]

@[simp]
theorem exists_eq_left₂ {pred : α → β → Prop}:
  (∃a b, (a = c ∧ b = d) ∧ pred a b) ↔ pred c d := by
  simp [and_assoc]

@[simp]
theorem is_bool_is_bit (a : ZMod n) [Fact (Nat.Prime n)]: Gates.is_bool a = is_bit a := by rfl

@[simp]
theorem Gates.eq_def : Gates.eq a b ↔ a = b := by simp [Gates.eq]

@[simp]
theorem Gates.sub_def {N} {a b : ZMod N} : Gates.sub a b = a - b := by simp [Gates.sub]

@[simp]
theorem Gates.is_zero_def {N} {a out : ZMod N} : Gates.is_zero a out ↔ out = Bool.toZMod (a = 0) := by
  simp [Gates.is_zero]
  apply Iff.intro
  . rintro (_ | _) <;> simp [*]
  . rintro ⟨_⟩
    simp [Bool.toZMod, Bool.toNat]
    tauto

@[simp]
theorem Gates.select_zero {a b r : ZMod N}: Gates.select 0 a b r = (r = b) := by
  simp [Gates.select]

@[simp]
theorem Gates.select_one {a b r : ZMod N}: Gates.select 1 a b r = (r = a) := by
  simp [Gates.select]

@[simp]
theorem Gates.or_zero { a r : ZMod N}: Gates.or a 0 r = (is_bit a ∧ r = a) := by
  simp [Gates.or]

@[simp]
theorem Gates.zero_or { a r : ZMod N}: Gates.or 0 a r = (is_bit a ∧ r = a) := by
  simp [Gates.or]

@[simp]
theorem Gates.one_or { a r : ZMod N}: Gates.or 1 a r = (is_bit a ∧ r = 1) := by
  simp [Gates.or]

@[simp]
theorem Gates.or_one { a r : ZMod N}: Gates.or a 1 r = (is_bit a ∧ r = 1) := by
  simp [Gates.or]

@[simp]
theorem Gates.is_bit_one_sub {a : ZMod N}: is_bit (Gates.sub 1 a) ↔ is_bit a := by
  simp [Gates.sub, is_bit, sub_eq_zero]
  tauto

@[simp]
theorem Gates.xor_bool {N} [Fact (N>1)] {a b : Bool} {c : ZMod N} : Gates.xor a.toZMod b.toZMod c ↔ c = (a != b).toZMod := by
  unfold xor
  cases a <;> cases b <;> {
    simp [is_bool, Bool.toZMod, Bool.toNat, bne]
    try ring_nf
  }

@[simp]
theorem Gates.and_bool {N} [Fact (N>1)] {a b : Bool} {c : ZMod N} : Gates.and a.toZMod b.toZMod c ↔ c = (a && b).toZMod := by
  unfold and
  cases a <;> cases b <;> {
    simp [is_bool, Bool.toZMod, Bool.toNat]
  }

@[simp]
theorem Gates.or_bool {N} [Fact (N>1)] {a b : Bool} {c : ZMod N} : Gates.or a.toZMod b.toZMod c ↔ c = (a || b).toZMod := by
  unfold or
  cases a <;> cases b <;> {
    simp [is_bool, Bool.toZMod, Bool.toNat]
  }

@[simp]
theorem Gates.not_bool {N} [Fact (N>1)] {a : Bool} : (1 : ZMod N) - a.toZMod = (!a).toZMod := by
  cases a <;> simp [sub]

@[simp]
lemma Gates.select_bool {N} [Fact (N > 1)] {c : Bool} {t f r : ZMod N}: Gates.select (c.toZMod (N:=N)) t f r ↔ r = if c then t else f := by
  cases c <;> simp [select, is_bool]

@[simp]
lemma Gates.eq_1_toZMod {N} [Fact (N>1)] {b : Bool}: Gates.eq (b.toZMod (N:=N)) 1 ↔ b := by
  cases b <;> simp [eq, is_bool]

@[simp]
lemma Gates.ite_0_toZMod {N} [Fact (N>1)] {b f: Bool}: (if b then (0:ZMod N) else f.toZMod (N:=N)) = (if b then false else f).toZMod := by
  cases b <;> simp

theorem Gates.to_binary_rangecheck {a : ZMod N} {n out} (h: to_binary a n out): a.val < 2^n := by
  rcases h with ⟨hrec, hbin⟩
  replace hbin := is_vector_binary_iff_exists_bool_vec.mp hbin
  rcases hbin with ⟨x, ⟨_⟩⟩
  rw [recover_binary_zmod'_map_toZMod_eq_Fin_ofBitsLE] at hrec
  cases Nat.lt_or_ge (2^n) N with
  | inl hp =>
    cases hrec
    have : (Fin.ofBitsLE x).val < N := Nat.lt_trans (Fin.is_lt _) hp
    rw [ZMod.val_nat_cast, Nat.mod_eq_of_lt this]
    exact Fin.is_lt _
  | inr hp =>
    apply Nat.lt_of_lt_of_le
    . apply ZMod.val_lt
    . simp [*]

lemma Gates.to_binary_iff_eq_Fin_ofBitsLE {l : ℕ} {a : ZMod N} {v : Vector (ZMod N) l}:
  Gates.to_binary a l v ↔ ∃v', v = v'.map Bool.toZMod ∧ a = (Fin.ofBitsLE v').val := by
  unfold to_binary
  rw [is_vector_binary_iff_exists_bool_vec]
  apply Iff.intro
  . rintro ⟨⟨_⟩, ⟨x, ⟨_⟩⟩⟩
    exists x
    cases x using Vector.casesOn
    . simp [recover_binary_zmod']
    . rename_i xhd xtl
      simp [recover_binary_zmod', recover_binary_zmod'_map_toZMod_eq_Fin_ofBitsLE, Fin.ofBitsLE, Fin.ofBitsBE_snoc]
      rfl
  . rintro ⟨v', ⟨_⟩, ⟨_⟩⟩
    simp [recover_binary_zmod'_map_toZMod_eq_Fin_ofBitsLE]

@[simp]
lemma map_toZMod_ofZMod_eq_self_of_is_vector_binary {n : ℕ} {v : Vector (ZMod N) n} (h : is_vector_binary v) :
  v.map (fun x => Bool.toZMod (Bool.ofZMod x)) = v := by
  induction n with
  | zero => simp [Vector.map]
  | succ n ih =>
    cases v using Vector.casesOn
    simp only [is_vector_binary_cons] at h
    simp [*]

lemma Gates.to_binary_iff_eq_fin_to_bits_le_of_pow_length_lt {l : ℕ} {a : ZMod N} {v : Vector (ZMod N) l} (pow_lt : 2 ^ l < N):
  Gates.to_binary a l v ↔ ∃(ha : a.val < 2^l), v = (Fin.toBitsLE ⟨a.val, ha⟩).map Bool.toZMod := by
  apply Iff.intro
  . intro to_bin
    have := Gates.to_binary_rangecheck to_bin
    exists this
    rw [Gates.to_binary_iff_eq_Fin_ofBitsLE] at to_bin
    rcases to_bin with ⟨v, ⟨_⟩, ⟨_⟩⟩
    have : Fin.mk (ZMod.val ((Fin.ofBitsLE v) : ZMod N)) this = Fin.ofBitsLE v := by
      apply Fin.eq_of_veq
      simp
      rw [ZMod.val_cast_of_lt]
      apply Nat.lt_trans (Fin.is_lt _) pow_lt
    rw [this]
    simp [Fin.toBitsLE, Fin.ofBitsLE]
  . intro ⟨ha, hv⟩
    rw [Gates.to_binary_iff_eq_Fin_ofBitsLE]
    simp [*]

lemma Gates.from_binary_iff_eq_ofBitsLE_mod_order {l : ℕ} {a : Vector Bool l} {out : ZMod N}:
  Gates.from_binary (a.map Bool.toZMod) out ↔ out = (Fin.ofBitsLE a).val := by
  simp [from_binary, recover_binary_zmod'_map_toZMod_eq_Fin_ofBitsLE, eq_comm]
