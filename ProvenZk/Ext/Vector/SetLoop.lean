import ProvenZk.Ext.Vector.Basic

namespace Vector

private lemma set_at_len (l1 l2 : List α) (it new : α):
  (l1 ++ it :: l2).set l1.length new = l1 ++ new :: l2 := by
  induction l1 with
  | nil => simp [List.set]
  | cons => simp [*]

private lemma get_at_len (l1 l2 : List α) (it : α):
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

private def listSetLoopUpto (l : List α) (m : ℕ) (f : ℕ -> α -> α): List α := Id.run do
  let mut l := l
  for i in [0:m] do
    l := match h:l.length with
    | Nat.zero => l
    | Nat.succ _ => l.set i (f i (l.get (Fin.ofNat' i (by linarith))))
  l

private def listSetLoop (l : List α) (f : ℕ -> α -> α): List α := listSetLoopUpto l l.length f

def setLoop (v : Vector α n) (f : ℕ -> α -> α): Vector α n := match n with
  | Nat.zero => v
  | Nat.succ _ => Id.run do
    let mut v := v
    for i in [0:n] do
      v := v.set i (f i (v.get i))
    v

theorem setLoop_def {n : ℕ} (v : Vector α n.succ) (f : ℕ -> α -> α):
  Std.Range.forIn (m := Id) [0:n.succ] v (fun i r => ForInStep.yield (r.set i (f i (r.get i)))) = v.setLoop f := by
  simp [setLoop, Id.run, forIn]

private lemma toList_setLoop {α n} {v : Vector α n} {f : ℕ -> α -> α}:
  (v.setLoop f).toList = listSetLoop v.toList f := by
  simp [setLoop, listSetLoop, listSetLoopUpto]
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

private lemma listMapIdx_appendOne (l1 : List α) (elem : α) (f : ℕ -> α -> α):
  (List.mapIdx f l1) ++ [f l1.length elem] = List.mapIdx f (l1 ++ [elem]) := by
  simp [List.mapIdx_append]


private lemma listMapIdx_setLoopApp (l1 l2 : List α) (f : ℕ -> α -> α):
 (List.mapIdx f l1) ++ l2 = listSetLoopUpto (l1 ++ l2) l1.length f := by
  induction l1 using List.reverseRecOn generalizing l2 with
  | H0 => simp [listSetLoopUpto, Id.run, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  | H1 xs x ih =>
    simp [listSetLoopUpto, forIn, Id.run]
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
    simp [listSetLoopUpto, forIn, Id.run] at ih
    rw [←ih, ←listMapIdx_appendOne]
    have : List.length (List.mapIdx f xs ++ x :: l2) = Nat.succ (xs.length + l2.length):= by
      simp; rw [Nat.add_succ]
    split
    { rename_i h; rw [this] at h; simp at h }
    {
      rw [←List.length_mapIdx (l := xs) (f := f), set_at_len, get_at_len]
      simp
    }

private lemma listMapIdx_setLoopUpto {l : List α} {f : ℕ -> α -> α }:
  List.mapIdx f l = listSetLoopUpto l l.length f := by
  have : List.mapIdx f l = List.mapIdx f l ++ [] := by simp
  conv => lhs ; rw [this]
  have : l = l ++ [] := by simp
  conv => rhs ; arg 1; rw [this]
  apply listMapIdx_setLoopApp

private lemma listMapIdx_setLoop {l : List α} {f : ℕ -> α -> α }:
  List.mapIdx f l = listSetLoop l f := by
  rw [listMapIdx_setLoopUpto, listSetLoop]

theorem setLoop_mapIdx {v : Vector α n} {f : ℕ -> α -> α }:
  v.setLoop f = v.mapIdx f := by
  apply Vector.eq
  simp [listMapIdx_setLoop, toList_setLoop]

end Vector
