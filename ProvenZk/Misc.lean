import ProvenZk.Gates
import ProvenZk.GatesEquivalence
import ProvenZk.Binary

open  GatesEquivalence

variable {N : Nat}
variable [Fact (Nat.Prime N)]

theorem or_rw (a b out : (ZMod N)) : GatesDef.or a b out ↔
  (GatesDef.is_bool a ∧ GatesDef.is_bool b ∧
  ( (out = 1 ∧ (a = 1 ∨ b = 1) ∨
    (out = 0 ∧ a = 0 ∧ b = 0)))) := by
  rw [or_equivalence]
  rw [is_bool_equivalence]
  rw [is_bool_equivalence]
  apply Iff.intro
  . intro h
    casesm* (_ ∨ _)
    repeat (
      casesm* (_ ∧ _)
      subst_vars
      simp
    )
  . intro h
    casesm* (_ ∧ _)
    rename_i ha hb hout
    cases ha <;> cases hb <;> {
      subst_vars
      simp at hout
      simp
      tauto
    }

lemma select_rw {b i1 i2 out : (ZMod N)} : (GatesDef.select b i1 i2 out) ↔ is_bit b ∧ match zmod_to_bit b with
  | Bit.zero => out = i2
  | Bit.one => out = i1 := by
  rw [select_equivalence]
  apply Iff.intro
  . intro h
    casesm* (_ ∧ _)
    rename_i hb hout
    cases hb
    repeat (
      subst_vars
      simp at hout
      simp [zmod_to_bit, ZMod.val_one]
      tauto
    )
  . intro h
    simp [is_bit] at h
    casesm* (_ ∧ _)
    rename_i hb hout
    cases hb
    repeat (
      subst_vars
      simp [zmod_to_bit, ZMod.val_one] at hout
      simp
      tauto
    )

@[simp]
theorem is_bool_is_bit (a : ZMod n) [Fact (Nat.Prime n)]: GatesDef.is_bool a = is_bit a := by
  rw [is_bool_equivalence]

@[simp]
theorem select_zero {a b r : ZMod N}: GatesDef.select 0 a b r = (r = b) := by
  simp [GatesDef.select]

@[simp]
theorem select_one {a b r : ZMod N}: GatesDef.select 1 a b r = (r = a) := by
  simp [GatesDef.select]

@[simp]
theorem or_zero { a r : ZMod N}: GatesDef.or a 0 r = (is_bit a ∧ r = a) := by
  simp [GatesDef.or]

@[simp]
theorem zero_or { a r : ZMod N}: GatesDef.or 0 a r = (is_bit a ∧ r = a) := by
  simp [GatesDef.or]

@[simp]
theorem one_or { a r : ZMod N}: GatesDef.or 1 a r = (is_bit a ∧ r = 1) := by
  simp [GatesDef.or]

@[simp]
theorem or_one { a r : ZMod N}: GatesDef.or a 1 r = (is_bit a ∧ r = 1) := by
  simp [GatesDef.or]

@[simp]
theorem is_bit_one_sub {a : ZMod N}: is_bit (GatesDef.sub 1 a) ↔ is_bit a := by
  simp [GatesDef.sub, is_bit, sub_eq_zero]
  tauto

lemma double_prop {a b c d : Prop} : (b ∧ a ∧ c ∧ a ∧ d) ↔ (b ∧ a ∧ c ∧ d) := by
  simp
  tauto

lemma and_iff (P Q R : Prop): (Q ↔ R) → (P ∧ Q ↔ P ∧ R) := by
  tauto

lemma ex_iff {P Q : α → Prop}: (∀x, P x ↔ Q x) → ((∃x, P x) ↔ ∃x, Q x) := by
  intro h;
  apply Iff.intro <;> {
    intro h1
    cases h1; rename_i witness prop
    exists witness
    try { rw [h witness]; assumption }
    try { rw [←h witness]; assumption }
  }
