import Std.Data.Fin.Basic
import Std.Classes.Cast
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Linarith.Frontend

namespace Fin

theorem castSucc_succ_eq_succ_castSucc : Fin.castSucc (Fin.succ i) = Fin.succ (Fin.castSucc i) := by
  rfl

theorem last_succ_eq_succ_last : Fin.last (Nat.succ n) = Fin.succ (Fin.last n) := by
  rfl

theorem last_def : Fin.mk (n := Nat.succ n) n (by simp) = Fin.last n := by
  rfl

theorem castSucc_def {i : Fin n} :
  Fin.mk (n := Nat.succ n) (i.val) (by cases i; linarith) = i.castSucc := by
  rfl

theorem cast_last {n : Nat} : ↑n = Fin.last n := by
  conv => lhs; whnf
  conv => rhs; whnf
  simp

end Fin
