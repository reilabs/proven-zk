import ProvenZk.Gates

theorem or_rw [Fact (Nat.Prime N)] (a b out : (ZMod N)) : Gates.or a b out ↔
  (Gates.is_bool a ∧ Gates.is_bool b ∧
  ( (out = 1 ∧ (a = 1 ∨ b = 1) ∨
    (out = 0 ∧ a = 0 ∧ b = 0)))) := by
  unfold Gates.or
  unfold Gates.is_bool
  simp
  intro ha hb
  cases ha <;> cases hb <;> { subst_vars; simp }

lemma select_rw [Fact (Nat.Prime N)] {b i1 i2 out : (ZMod N)} : (Gates.select b i1 i2 out) ↔ is_bit b ∧ match zmod_to_bit b with
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

lemma double_prop {a b c d : Prop} : (b ∧ a ∧ c ∧ a ∧ d) ↔ (b ∧ a ∧ c ∧ d) := by
  simp
  tauto
