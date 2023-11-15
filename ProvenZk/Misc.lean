import ProvenZk.Gates
import ProvenZk.Binary

variable {N : Nat}
variable [Fact (Nat.Prime N)]

theorem or_rw (a b out : (ZMod N)) : Gates.or a b out ↔
  (Gates.is_bool a ∧ Gates.is_bool b ∧
  ( (out = 1 ∧ (a = 1 ∨ b = 1) ∨
    (out = 0 ∧ a = 0 ∧ b = 0)))) := by
  unfold Gates.or
  unfold Gates.is_bool
  simp
  intro ha hb
  cases ha <;> cases hb <;> { subst_vars; simp }

lemma select_rw {b i1 i2 out : (ZMod N)} : (Gates.select b i1 i2 out) ↔ is_bit b ∧ match zmod_to_bit b with
  | Bit.zero => out = i2
  | Bit.one => out = i1 := by
  unfold Gates.select
  unfold Gates.is_bool
  apply Iff.intro <;> {
    intro h; rcases h with ⟨is_b, _⟩
    refine ⟨is_b, ?_⟩
    cases is_b
    case inl => {
      simp [*, zmod_to_bit] at *
      assumption
    }
    case inr => {
      simp [*, zmod_to_bit] at *
      have : Nat.Prime N := (inferInstance : Fact (Nat.Prime N)).elim
      have : N > 1 := by
        apply Nat.Prime.one_lt
        assumption
      cases N
      case zero => simp [ZMod.val] at *
      case succ n _ _ _ _=> {
        cases n
        case zero => simp [ZMod.val] at *
        case succ => {
          simp [ZMod.val] at *
          assumption
        }
      }
    }
  }

@[simp]
theorem is_bool_is_bit (a : ZMod n) [Fact (Nat.Prime n)]: Gates.is_bool a = is_bit a := by rfl

@[simp]
theorem select_zero {a b r : ZMod N}: Gates.select 0 a b r = (r = b) := by
  simp [Gates.select]

@[simp]
theorem select_one {a b r : ZMod N}: Gates.select 1 a b r = (r = a) := by
  simp [Gates.select]

@[simp]
theorem or_zero { a r : ZMod N}: Gates.or a 0 r = (is_bit a ∧ r = a) := by
  simp [Gates.or]

@[simp]
theorem zero_or { a r : ZMod N}: Gates.or 0 a r = (is_bit a ∧ r = a) := by
  simp [Gates.or]

@[simp]
theorem one_or { a r : ZMod N}: Gates.or 1 a r = (is_bit a ∧ r = 1) := by
  simp [Gates.or]

@[simp]
theorem or_one { a r : ZMod N}: Gates.or a 1 r = (is_bit a ∧ r = 1) := by
  simp [Gates.or]

@[simp]
theorem is_bit_one_sub {a : ZMod N}: is_bit (Gates.sub 1 a) ↔ is_bit a := by
  simp [Gates.sub, is_bit, sub_eq_zero]
  tauto

lemma double_prop {a b c d : Prop} : (b ∧ a ∧ c ∧ a ∧ d) ↔ (b ∧ a ∧ c ∧ d) := by
  simp
  tauto
