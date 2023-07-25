import Init.Data.Range
import Mathlib

namespace Std
namespace Range

private lemma fuel_doesnt_matter [Monad m] {start d : Nat} {init : α} {f : Nat -> α -> m (ForInStep α)} (fuel1 fuel2 : Nat):
  (fuel1 >= d) →
  (fuel2 >= d) →
  Std.Range.forIn.loop f fuel1 start (start + d) 1 init =
  Std.Range.forIn.loop f fuel2 start (start + d) 1 init := by
  induction d generalizing start init fuel1 fuel2 with
  | zero =>
    unfold forIn.loop
    simp
  | succ _ ih =>
    intro h1 h2
    unfold forIn.loop
    simp
    split
    { contradiction }
    split
    { contradiction }
    unfold Bind.bind
    apply congrArg
    funext
    split
    { rfl }
    have : ∀ d, start + Nat.succ d = start + 1 + d := by simp_arith
    conv => lhs; arg 4; rw [this]
    conv => rhs; arg 4; rw [this]
    apply ih
    all_goals linarith

theorem forIn_stopSucc {start d : Nat} {init : α} {f : Nat -> α -> α } :
  Range.forIn (m := Id) [start:(start + d.succ)] init (fun i a => ForInStep.yield (f i a)) =
  f (start + d) (Range.forIn (m := Id) [start:(start + d)] init (fun i a => ForInStep.yield (f i a))) := by
  induction d generalizing start init with
  | zero =>
    unfold Range.forIn
    unfold Range.forIn.loop
    unfold Range.forIn.loop
    simp [Id.run]
  | succ d ih =>
    simp [Range.forIn] at ih
    have start_shifts : start + d.succ.succ = (start + 1) + d.succ := calc
      start + d.succ.succ = (start + d.succ).succ := by rw [Nat.add_succ]
      _ = start.succ + d.succ := by rw [←Nat.succ_add]
      _ = (start + 1) + d.succ := by rw [Nat.succ_add]

    have old_fuel_correct : start + Nat.succ d ≥ Nat.succ d := by simp
    have new_fuel_correct : start + 1 + Nat.succ d ≥ Nat.succ d := by simp
    unfold Range.forIn
    unfold Range.forIn.loop
    simp
    conv =>
      lhs
      rw [start_shifts]
      rw [fuel_doesnt_matter (start + d.succ) (start + 1 + d.succ) old_fuel_correct new_fuel_correct]
      rw [ih]
    apply congrArg₂
    { simp_arith }
    rw [fuel_doesnt_matter (start+1+d) (start+d)]
    have : start + 1 + d = start + Nat.succ d := by simp_arith
    rw [this]

    all_goals linarith

theorem forIn_startSucc {start d : Nat} {init : α} {f : ℕ -> α -> α } :
  Range.forIn (m := Id) [start:(start + d.succ)] init (fun i a => ForInStep.yield (f i a)) =
  Range.forIn (m := Id) [start.succ:(start + d.succ)] (f start init) (fun i a => ForInStep.yield (f i a)) := by
  simp [Range.forIn]
  conv =>
    lhs
    unfold forIn.loop
    simp
    arg 4; rw [Nat.add_succ, ←Nat.succ_add, ←Nat.add_one]
  rw [fuel_doesnt_matter (start + d) (start + d.succ)]
  {
    repeat apply congr
    all_goals (try rfl)
    simp_arith
  }
  all_goals linarith

theorem forIn_ixShift [Monad m] {start stop shift : Nat} {init : α} {f : ℕ -> α -> m (ForInStep α) } :
  Range.forIn [start:stop] init (fun i a => f (i + shift) a) = Range.forIn [start+shift:stop+shift] init f := by
  cases h:decide (stop ≤ start) with
  | true =>
    simp at h
    unfold Range.forIn
    unfold Range.forIn.loop
    simp [h]
  | false =>
    simp at h
    let d := stop - start
    have : stop = start + d := by
      simp
      rw [←Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
      linarith
    rw [this]
    rw [this] at h
    clear this h
    induction d generalizing start stop init with
    | zero =>
      unfold Range.forIn
      unfold Range.forIn.loop
      simp
    | succ d1 ih =>
      unfold Range.forIn
      unfold Range.forIn.loop
      simp
      split
      { rename_i h; simp_arith at h }
      rename_i fuel feq
      conv at feq =>
        rw [Nat.add_succ, Nat.succ_add]
        simp
      rw [←feq]
      unfold Bind.bind
      apply congrArg
      funext x
      split
      { rfl }
      simp [Std.Range.forIn] at ih
      conv =>
        lhs
        arg 4; rw [Nat.add_succ, ←Nat.succ_add, ←Nat.add_one]
      rw [fuel_doesnt_matter (start + d1) (start + 1 + d1)]
      rw [ih]
      have : start + 1 + d1 + shift = start + 1 + shift + d1 := by simp_arith
      rw [this]
      rw [fuel_doesnt_matter (start + 1 + shift + d1) (start + d1 + shift)]
      apply congr
      apply congr
      apply congr
      apply congr
      rfl
      all_goals simp_arith

theorem forIn_startSucc_shift {start d : Nat} {init : α} {f : ℕ -> α -> α } :
  Range.forIn (m := Id) [start:(start + d.succ)] init (fun i a => ForInStep.yield (f i a)) =
  Range.forIn (m := Id) [start:(start + d)] (f start init) (fun i a => ForInStep.yield (f (i + 1) a)) := by
  rw [forIn_startSucc]
  conv =>
    lhs
    arg 1
    conv =>
      arg 1
      rw [←Nat.add_one]
    conv =>
      arg 2
      rw [←Nat.add_one, ←Nat.add_assoc]
  rw [←forIn_ixShift]

theorem forIn_homo {start stop : Nat} {init : α} {f1 : Nat -> α -> α} {f2 : Nat -> β -> β} {g : α -> β} :
  (forall i a, i ∈ [start:stop] -> g (f1 i a) = f2 i (g a)) ->
  g (Range.forIn (m := Id) [start:stop] init (fun i a => ForInStep.yield (f1 i a))) =
  (Range.forIn (m := Id) [start:stop] (g init) (fun i a => ForInStep.yield (f2 i a))) := by
  cases h:decide (stop ≤ start) with
  | true =>
    simp at h
    unfold Range.forIn
    unfold Range.forIn.loop
    simp [h, Id.run]
  | false =>
    simp at h
    let d := stop - start
    have : stop = start + d := by
      simp
      rw [←Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
      linarith
    rw [this]
    induction d with
    | zero =>
      unfold Range.forIn
      unfold Range.forIn.loop
      simp [Id.run]
    | succ d ih =>
      intro h
      rw [forIn_stopSucc, forIn_stopSucc]
      rw [h]
      apply congrArg
      rw [ih]
      {
        intro i a imemd
        apply h
        simp [Membership.mem]
        simp [Membership.mem] at imemd
        cases imemd
        apply And.intro
        { assumption }
        { linarith }
      }
      {
        simp [Membership.mem]
      }

theorem counter_elide_fst {f : Nat -> (MProd Nat α) -> α} {init : MProd Nat α} {k start stop}:
  Std.Range.forIn (m := Id) [start:stop] init (fun i r => ForInStep.yield { fst := r.1 + k, snd := f i r }) =
  MProd.mk (init.fst + (stop - start) * k) (Std.Range.forIn (m := Id) [start:stop] init.2 (fun i r => ForInStep.yield (f i ⟨init.1 + (i - start) * k, r⟩))) := by
  cases h : decide (stop ≤ start) with
  | true =>
    simp at h
    unfold Range.forIn
    unfold Range.forIn.loop
    simp [h]
    rfl
  | false =>
    simp at h
    let d := stop - start
    have : stop = start + d := by
      simp
      rw [←Nat.add_sub_assoc, Nat.add_comm, Nat.add_sub_cancel]
      linarith
    rw [this]
    have : start + d - start = d := by simp_arith
    rw [this]
    induction d with
    | zero =>
      unfold Range.forIn
      unfold Range.forIn.loop
      simp
      rfl
    | succ d ih =>
      simp [forIn_stopSucc]
      simp [ih]
      apply congrArg₂
      {
        rw [←Nat.add_one]
        rw [Nat.right_distrib]
        simp_arith
      }
      {
        simp_arith
      }


end Range
end Std