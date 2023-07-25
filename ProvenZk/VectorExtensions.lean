import Mathlib
import ProvenZk.Ext.Range
import ProvenZk.Ext.List

namespace Vector

def snoc {α n} (v: Vector α n) (x: α) : Vector α n.succ := v.append (x ::ᵥ nil)

def listSetLoopX (l : List α) (m : ℕ) (f : ℕ -> α -> α): List α := Id.run do
  let mut l := l
  for i in [0:m] do
    l := match h:l.length with
    | Nat.zero => l
    | Nat.succ _ => l.set i (f i (l.get (Fin.ofNat' i (by linarith))))
  l

def listSetLoop (l : List α) (f : ℕ -> α -> α): List α := listSetLoopX l l.length f

def mapIdx (v : Vector α n) (f : Nat -> α -> β): Vector β n := ⟨v.toList.mapIdx f, by simp⟩

def to_column (v : Vector α n) : Matrix (Fin n) Unit α := Matrix.of (fun i _ => v.get i)

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

@[simp]
theorem set_cons_0 {α n} (v : Vector α n) (x y: α):
  (cons y v).set 0 x = cons x v := by
  apply Vector.eq
  simp
  rfl

theorem mapIdx_compose {α β γ : Type} {n} (f : ℕ → α → β) (g : ℕ → β → γ) (v : Vector α n):
  mapIdx (mapIdx v f) g = mapIdx v (fun i x => g i (f i x)) := by
  apply Vector.eq
  simp [List.mapIdx_compose]

def setLoop (v : Vector α n) (f : ℕ -> α -> α): Vector α n := match n with
  | Nat.zero => v
  | Nat.succ _ => Id.run do
    let mut v := v
    for i in [0:n] do
      v := v.set i (f i (v.get i))
    v

theorem setLoop_def {n : ℕ} (v : Vector α n.succ) (f : ℕ -> α -> α):
  Std.Range.forIn (m := Id) [0:n.succ] v (fun i r => ForInStep.yield (r.set i (f i (r.get i)))) = v.setLoop f := by
  sorry

@[simp]
lemma toList_setLoop {α n} {v : Vector α n} {f : ℕ -> α -> α}:
  (v.setLoop f).toList = listSetLoop v.toList f := by
  simp [setLoop, listSetLoop, listSetLoopX]
  cases n
  {
    simp [Id.run, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  }
  {
    rename_i n
    simp
    apply Std.Range.forIn_homo
    simp
    intro i v
    split
    { rename_i h; rw [toList_length] at h; contradiction }
    {
      rename_i h; rw [toList_length] at h; simp at h;
      intro mem; simp [Membership.mem] at mem;
      rw [get_eq_get]
      apply congrArg₂
      {
        apply Nat.mod_eq_of_lt
        assumption
      }
      {
        apply congrArg₂
        { rfl }
        {
          apply congr
          { rfl }
          simp [Fin.ofNat']
          rfl
        }
      }
    }
  }

lemma listMapIdx_appendOne (l1 : List α) (elem : α) (f : ℕ -> α -> α):
  (List.mapIdx f l1) ++ [f l1.length elem] = List.mapIdx f (l1 ++ [elem]) := by
  simp [List.mapIdx_append]

lemma set_at_len (l1 l2 : List α) (it new : α):
  (l1 ++ it :: l2).set l1.length new = l1 ++ new :: l2 := by
  induction l1 with
  | nil => simp [List.set]
  | cons => simp [*]

lemma get_at_len (l1 l2 : List α) (it : α):
  (l1 ++ it :: l2).get (Fin.ofNat' l1.length (by simp)) = it := by
  simp [Fin.ofNat']
  have : ∀ {l1 l2: List α}, List.length l1 % (List.length l1 + Nat.succ (List.length l2)) = List.length l1 := by
    intros
    apply Nat.mod_eq_of_lt
    simp
  simp [this]
  induction l1 with
  | nil => simp
  | cons x xs ih =>
    unfold List.get
    simp
    apply ih


lemma listMapIdx_setLoopApp (l1 l2 : List α) (f : ℕ -> α -> α):
 (List.mapIdx f l1) ++ l2 = listSetLoopX (l1 ++ l2) l1.length f := by
  induction l1 using List.reverseRecOn generalizing l2 with
  | H0 => simp [listSetLoopX, Id.run, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  | H1 xs x ih =>
    simp [listSetLoopX, forIn, Id.run]
    let g (i : ℕ) (l : List α) := match h:l.length with
    | Nat.zero => l
    | Nat.succ _ => l.set i (f i (l.get (Fin.ofNat' i (by linarith))))
    have : (fun i l => ForInStep.yield (match h:l.length with
    | Nat.zero => l
    | Nat.succ _ => l.set i (f i (l.get (Fin.ofNat' i (by linarith)))))) = (fun i r => ForInStep.yield (g i r)) := by rfl
    rw [this]
    conv => rhs; enter [1, 2]; rw [←Nat.zero_add (_ + _)]
    rw [Std.Range.forIn_stopSucc]
    simp
    clear g this
    simp [listSetLoopX, forIn, Id.run] at ih
    rw [←ih, ←listMapIdx_appendOne]
    have : List.length (List.mapIdx f xs ++ x :: l2) = Nat.succ (xs.length + l2.length):= by
      simp; rw [Nat.add_succ]
    split
    { rename_i h; rw [this] at h; simp at h }
    {
      rw [←List.length_mapIdx (l := xs) (f := f), set_at_len, get_at_len]
      simp
    }

lemma listMapIdx_setLoopX {l : List α} {f : ℕ -> α -> α }:
  List.mapIdx f l = listSetLoopX l l.length f := by
  have : List.mapIdx f l = List.mapIdx f l ++ [] := by simp
  conv => lhs ; rw [this]
  have : l = l ++ [] := by simp
  conv => rhs ; arg 1; rw [this]
  apply listMapIdx_setLoopApp

theorem listMapIdx_setLoop {l : List α} {f : ℕ -> α -> α }:
  List.mapIdx f l = listSetLoop l f := by
  rw [listMapIdx_setLoopX, listSetLoop]

theorem setLoop_mapIdx {v : Vector α n} {f : ℕ -> α -> α }:
  v.setLoop f = v.mapIdx f := by
  apply Vector.eq
  simp [listMapIdx_setLoop]

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
