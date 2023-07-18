import Mathlib

namespace Vector

theorem toList_tail {α n} (v: Vector α (Nat.succ n)) : v.tail.toList = v.toList.tail := by
  rw [←cons_head_tail v]
  rw [toList_cons]
  simp

@[simp]
theorem toList_snoc {α n} (v: Vector α n) (x: α) : (snoc v x).toList = v.toList ++ [x] := by
  cases v
  unfold snoc
  simp

@[simp]
theorem snoc_nil_cons {α} (x: α): snoc nil x = x ::ᵥ nil := by
  apply Vector.eq
  simp [snoc, append, head]

theorem tail_snoc {T n} (v: Vector T (Nat.succ n)) (x: T): tail (snoc v x) = snoc (tail v) x := by
  cases v; rename_i v _;
  apply Vector.eq
  simp [toList_snoc, toList_tail]
  cases v
  . contradiction
  . simp

theorem head_snoc {T n} (v: Vector T (Nat.succ n)) (x: T): head (snoc v x) = head v := by
  cases v; rename_i val _;
  cases val
  . contradiction
  . simp [snoc, head, append]

theorem reverse_cons_snoc {T n} (v: Vector T n) (x: T): reverse (cons x v) = snoc (reverse v) x := by
  apply Vector.eq
  simp [toList_snoc, toList_reverse]

@[simp]
def element_wise_eq {T n} (v1 v2: Vector T n): Prop := match n with
  | Nat.zero => True
  | Nat.succ _ => v1.head = v2.head ∧ element_wise_eq v1.tail v2.tail

theorem elems_eq {T n} {v1 v2: Vector T n}: v1 = v2 -> element_wise_eq v1 v2 := by
  induction n with
  | zero => simp
  | succ =>
    intro h
    simp [element_wise_eq, *]

syntax (priority := high) "vec![" term,* "]" : term
macro_rules
  | `(vec![]) => `(nil)
  | `(vec![$x]) => `(cons $x nil)
  | `(vec![$x, $xs:term,*]) => `(cons $x (vec![$xs,*]))

instance : GetElem (Vector a l) (Nat) a (fun _ i => i < l) where
  getElem xs i h := xs.get ⟨i, h⟩

end Vector
