import Mathlib
import ProvenZk.Ext.Range

namespace Vector

def snoc {α n} (v: Vector α n) (x: α) : Vector α n.succ := v.append (x ::ᵥ nil)

def get! [Inhabited α] (l : List α) (i : Nat) : α := if h : i < l.length then l.get ⟨i, h⟩ else default

def listSetLoopX [Inhabited α] (l : List α) (m : ℕ) (f : ℕ -> α -> α): List α := Id.run do
  let mut l := l
  for i in [0:m] do
    l := l.set i (f i (l.get! i))
  l


def listSetLoop [Inhabited α] (l : List α) (f : ℕ -> α -> α): List α := listSetLoopX l l.length f

def setLoop [Inhabited α] (v : Vector α n) (f : ℕ -> α -> α): Vector α n := match n with
  | Nat.zero => v
  | Nat.succ _ => Id.run do
    let mut v := v
    for i in [0:n] do
      v := v.set i (f i (v.get i))
    v



-- theorem length_listSetLoop [Inhabited α] {l : List α}

lemma listMapIdx_appendOne [Inhabited α] (l1 : List α) (elem : α) (f : ℕ -> α -> α):
  (List.mapIdx f l1) ++ [f l1.length elem] = List.mapIdx f (l1 ++ [elem]) := by
  simp [List.mapIdx_append]

lemma set_at_len [Inhabited α] (l1 l2 : List α) (it new : α):
  (l1 ++ it :: l2).set l1.length new = l1 ++ new :: l2 := by
  induction l1 with
  | nil => simp [List.set]
  | cons => simp [*]

lemma get_at_len [Inhabited α] (l1 l2 : List α) (it  : α):
  (l1 ++ it :: l2).get! l1.length = it := by
  induction l1 with
  | nil => simp
  | cons => simp [*]

lemma listMapIdx_setLoopApp [Inhabited α] (l1 l2 : List α) (f : ℕ -> α -> α):
 (List.mapIdx f l1) ++ l2 = listSetLoopX (l1 ++ l2) l1.length f := by
  induction l1 using List.reverseRecOn generalizing l2 with
  | H0 => simp [listSetLoopX, Id.run, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  | H1 xs x ih =>
    simp [listSetLoopX, forIn]
    let g (i : ℕ) (l : List α) := List.set l i (f i (List.get! l i))
    have : (fun i a => ForInStep.yield (List.set a i (f i (List.get! a i)))) = (fun i r => ForInStep.yield (g i r)) := by rfl
    rw [this]
    conv => rhs; enter [1,1,2]; rw [←Nat.zero_add (_ + _)]
    rw [Std.Range.forIn_stopSucc]
    simp
    clear g this
    simp [listSetLoopX, forIn] at ih
    rw [←ih, ←listMapIdx_appendOne, ←List.length_mapIdx (l := xs) (f := f), set_at_len, get_at_len]
    simp

lemma listMapIdx_setLoopX [Inhabited α] {l : List α} {f : ℕ -> α -> α }:
  List.mapIdx f l = listSetLoopX l l.length f := by
  have : List.mapIdx f l = List.mapIdx f l ++ [] := by simp
  conv => lhs ; rw [this]
  have : l = l ++ [] := by simp
  conv => rhs ; arg 1; rw [this]
  apply listMapIdx_setLoopApp

theorem listMapIdx_setLoop [Inhabited α] {l : List α} {f : ℕ -> α -> α }:
  List.mapIdx f l = listSetLoop l f := by
  rw [listMapIdx_setLoopX, listSetLoop]



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

theorem reverse_snoc_cons {T n} (v: Vector T n) (x: T): reverse (snoc v x) = cons x (reverse v) := by
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

theorem reverse_singleton {T} (v : Vector T 1) : reverse v = v := by
  cases v; rename_i l p
  apply Vector.eq
  rw [toList_reverse]
  unfold toList
  simp
  cases l
  . contradiction
  . rename_i h t
    cases t
    . simp
    . simp at p


syntax (priority := high) "vec![" term,* "]" : term
macro_rules
  | `(vec![]) => `(nil)
  | `(vec![$x]) => `(cons $x nil)
  | `(vec![$x, $xs:term,*]) => `(cons $x (vec![$xs,*]))

instance : GetElem (Vector a l) (Nat) a (fun _ i => i < l) where
  getElem xs i h := xs.toList.get ⟨i, by rw [Vector.toList_length]; exact h⟩

theorem head_eq (v1 v2 : Vector α (Nat.succ n)) (h : v1 = v2) : v1[0] = v2[0] := by
  rw [h]

end Vector
