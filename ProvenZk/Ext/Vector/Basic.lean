import Mathlib
import ProvenZk.Ext.Range
import ProvenZk.Ext.List

namespace Vector

def mapIdx (v : Vector α n) (f : Nat -> α -> β): Vector β n := ⟨v.toList.mapIdx f, by simp⟩

@[simp]
theorem toList_mapIdx {v : Vector α n} {f : ℕ -> α -> β}:
  (v.mapIdx f).toList = v.toList.mapIdx f := by
  simp [mapIdx]

@[simp]
theorem mapIdx_cons {α β n} (f : ℕ -> α -> β) (x : α) (v : Vector α n):
  (cons x v).mapIdx f = cons (f 0 x) (v.mapIdx (fun i x => f (i + 1) x)) := by
  apply Vector.eq
  simp [mapIdx, toList_cons]

@[simp]
theorem mapIdx_nil {α β} (f : ℕ -> α -> β):
  (nil : Vector α 0).mapIdx f = nil := by
  apply Vector.eq
  simp

theorem mapIdx_compose {α β γ : Type} {n} (f : ℕ → α → β) (g : ℕ → β → γ) (v : Vector α n):
  mapIdx (mapIdx v f) g = mapIdx v (fun i x => g i (f i x)) := by
  apply Vector.eq
  simp [List.mapIdx_compose]

@[simp]
theorem set_cons_0 {α n} (v : Vector α n) (x y: α):
  (cons y v).set 0 x = cons x v := by
  apply Vector.eq
  simp
  rfl

@[simp]
theorem toList_tail {α n} (v: Vector α (Nat.succ n)) : v.tail.toList = v.toList.tail := by
  rw [←cons_head_tail v]
  rw [toList_cons]
  simp

@[simp]
theorem toList_snoc {α n} (v: Vector α n) (x: α) : (snoc v x).toList = v.toList ++ [x] := by
  cases v
  unfold snoc
  simp

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


-- @[simp]
-- def element_wise_eq {T n} (v1 v2: Vector T n): Prop := match n with
--   | Nat.zero => True
--   | Nat.succ _ => v1.head = v2.head ∧ element_wise_eq v1.tail v2.tail

-- theorem elems_eq {T n} {v1 v2: Vector T n}: v1 = v2 -> element_wise_eq v1 v2 := by
--   induction n with
--   | zero => simp
--   | succ =>
--     intro h
--     simp [element_wise_eq, *]


syntax (priority := high) "vec![" term,* "]" : term
macro_rules
  | `(vec![]) => `(nil)
  | `(vec![$x]) => `(cons $x nil)
  | `(vec![$x, $xs:term,*]) => `(cons $x (vec![$xs,*]))

instance : GetElem (Vector a l) (Nat) a (fun _ i => i < l) where
  getElem xs i h := xs.toList.get ⟨i, by rw [Vector.toList_length]; exact h⟩

def to_column (v : Vector α n) : Matrix (Fin n) Unit α := Matrix.of (fun i _ => v.get i)

end Vector
