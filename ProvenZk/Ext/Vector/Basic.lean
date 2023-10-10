import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.Defs

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

def mapIdx' (v : Vector α n) (f : Fin n -> α -> β): Vector β n := match n with
  | Nat.zero => nil
  | Nat.succ _ =>
    let h := f 0 v.head
    let t := v.tail.mapIdx' (fun i x => f (Fin.succ i) x)
    cons h t

theorem mapIdx'_mapIdx (v : Vector α n) (f : Nat -> α -> β):
  v.mapIdx' (fun i x => f i x) = v.mapIdx f := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [←Vector.cons_head_tail v]
    rw [mapIdx_cons]
    unfold mapIdx'
    simp
    congr
    rw [←ih]
    rfl

theorem mapIdx_mod (v: Vector α n) (f: ℕ -> α -> β): v.mapIdx f = v.mapIdx (fun i x => f (i % n) x) := by
  rw [←mapIdx'_mapIdx, ←mapIdx'_mapIdx]
  congr
  funext i _
  congr
  cases i
  simp
  apply Eq.symm
  apply Nat.mod_eq_of_lt
  assumption

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

theorem map_reverse {α β n} (f : α -> β) (v : Vector α n) : (reverse v).map f = reverse (v.map f) := by
  apply Vector.eq
  simp [toList_reverse, List.map_reverse]

syntax (priority := high) "vec![" term,* "]" : term
macro_rules
  | `(vec![]) => `(nil)
  | `(vec![$x]) => `(cons $x nil)
  | `(vec![$x, $xs:term,*]) => `(cons $x (vec![$xs,*]))

def to_column (v : Vector α n) : Matrix (Fin n) Unit α := Matrix.of (fun i _ => v.get i)

theorem vector_eq_cons : (x ::ᵥ xs) = (y ::ᵥ ys) ↔ x = y ∧ xs = ys := by
  simp [Vector.eq_cons_iff]

theorem vector_reverse_eq {x y : Vector α n} : (x.reverse = y) ↔ (x = y.reverse) := by
  apply Iff.intro
  case mp => {
    intro
    subst_vars
    simp
  }
  case mpr => {
    intro
    subst_vars
    simp
  }

@[simp]
theorem vector_replicate_succ : Vector.replicate (Nat.succ n) a = a ::ᵥ Vector.replicate n a := by
  rfl

theorem vector_replicate_succ_snoc : Vector.replicate (Nat.succ n) a = (Vector.replicate n a).snoc a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => rhs; simp [←ih]

@[simp]
theorem vector_replicate_reverse : Vector.reverse (Vector.replicate n a) = Vector.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ih, ←vector_replicate_succ_snoc]

@[simp]
theorem vector_map_replicate : Vector.map f (Vector.replicate n a) = Vector.replicate n (f a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ih]

end Vector
