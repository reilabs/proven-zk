import ProvenZk.PoseidonExtract
import ProvenZk.Poseidon
import ProvenZk.VectorExtensions
-- import Mathlib

variable [Fact (Nat.Prime Order)]

lemma fin_mod { n } (x : Fin n) : x.val = x.val % n := by
  have : _ := x.isLt
  simp [Nat.mod_eq_of_lt this]


-- def foo :=   [0:10].forIn
lemma sbox_uncps (A : F) (k : F -> Prop): sbox A k = k (A ^ 5) := by
  unfold sbox
  conv => lhs; simp [Gates.mul]
  apply congrArg
  rw [mul_assoc]
  conv => rhs; whnf
  conv => lhs; whnf
  congr
  simp_arith
  apply fin_mod _


lemma mds_uncps (S : Vector F 3) (k : Vector F 3 -> Prop): mds_3 S k = k (Poseidon.mds_matmul S) := by
  sorry

lemma full_round_uncps (S C: Vector F 3) (k : Vector F 3 -> Prop): fullRound_3_3 S C k = k (Poseidon.full_round S C) := by
  conv => lhs; simp [fullRound_3_3, Gates.add, sbox_uncps, mds_uncps]

lemma half_round_uncps (S C: Vector F 3) (k : Vector F 3 -> Prop): halfRound_3_3 S C k = k (Poseidon.partial_round S C) := by
  conv => lhs; simp [halfRound_3_3, Gates.add, sbox_uncps, mds_uncps]

lemma iff_to_eq {α} {a b: α} {k : α -> Prop }: a = b -> (k a ↔ k b) := by intro eq; rw [eq]


-- lemma full_rounds_1_uncps {S: Vector F 3} {k: Vector F 3 -> Prop}:
--   full_rounds_cps' S 0 4 k = k (Poseidon.full_rounds_step_3 ⟨0, S⟩ 4).2 := by
--   simp [full_rounds_cps', full_round_uncps, round_constants', Poseidon.round_constants_field, getElem!]
--   apply iff_to_eq
--   unfold Poseidon.full_rounds_step_3
--   simp
--   split; rename_i h; rw [←h]; clear h
--   simp [forIn, Std.Range.forIn, Std.Range.forIn.loop, Poseidon.round_constants_field]
--   simp [getElem!]

-- lemma full_rounds_2_uncps {S : Vector F 3} {k : Vector F 3 -> Prop}:
--   full_rounds_cps' S 183 4 k = k (Poseidon.full_rounds_step_3 ⟨183, S⟩ 4).2 := by
--   simp [full_rounds_cps', full_round_uncps, round_constants', Poseidon.round_constants_field, getElem!]
--   apply iff_to_eq
--   unfold Poseidon.full_rounds_step_3
--   simp
--   split; rename_i h; rw [←h]; clear h
--   simp [forIn, Std.Range.forIn, Std.Range.forIn.loop, Poseidon.round_constants_field]
--   simp [getElem!]

lemma full_rounds_cps'_tear (state: Vector F 3) (init_const: Nat) (round_count: Nat) (k : Vector F 3 -> Prop):
    full_rounds_cps' (state: Vector F 3) (init_const) (round_count.succ) k =
    full_rounds_cps' (Poseidon.full_round state (round_constants' init_const)) init_const.succ.succ.succ round_count k := by
  simp [full_rounds_cps']
  rw [full_round_uncps]

lemma half_rounds_cps'_tear (state: Vector F 3) (init_const: Nat) (round_count: Nat) (k : Vector F 3 -> Prop):
    half_rounds_cps' (state: Vector F 3) (init_const) (round_count.succ) k =
    half_rounds_cps' (Poseidon.partial_round state (round_constants' init_const)) init_const.succ.succ.succ round_count k := by
  simp [half_rounds_cps']
  rw [half_round_uncps]

lemma loop_invariant [Monad m] {stop start fuel: Nat} {s : α} {f : Nat -> α -> m (ForInStep α)}:
  (∀i1 i2 a, f i1 a = f i2 a) ->
  Std.Range.forIn.loop f fuel start.succ stop.succ 1 s = Std.Range.forIn.loop f fuel start stop 1 s := by
  intro h
  induction fuel generalizing start stop s with
  | zero =>
    simp [Std.Range.forIn.loop]
  | succ fuel ih =>
    simp [Std.Range.forIn.loop]
    split
    {
      have : stop ≤ start := by
        rw [←Nat.succ_le_succ_iff]
        assumption
      simp [this]
    }
    {
      have : ¬ stop ≤ start := by
        rw [←Nat.succ_le_succ_iff]
        assumption
      simp [this]
      have : f start s = f start.succ s := by
        apply h
      simp [this]
      unfold bind
      apply congrArg
      funext
      split
      {rfl}
      {rw [ih]}
    }

lemma full_round_step_3_tear {inp : MProd Nat (Vector F 3)} {count}:
  Poseidon.full_rounds_step_3 inp count.succ =
  Poseidon.full_rounds_step_3 ⟨inp.1.succ.succ.succ, Poseidon.full_round inp.2 (round_constants' inp.1)⟩ count := by
  conv =>
    lhs
    simp [Poseidon.full_rounds_step_3, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  conv =>
    rhs
    simp [Poseidon.full_rounds_step_3, forIn, Std.Range.forIn, Std.Range.forIn.loop, round_constants']
  split; rename_i h; rw [←h]; clear h
  split; rename_i h; rw [←h]; clear h
  simp [loop_invariant]

lemma full_round_const_count {inp : MProd Nat (Vector F 3)} {count}:
  (Poseidon.full_rounds_step_3 inp count).1 = inp.1 + count * 3 := by
  induction count generalizing inp with
  | zero =>
    simp [Poseidon.full_rounds_step_3, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  | succ count ih =>
    rw [full_round_step_3_tear, ih]
    simp
    linarith

lemma partial_round_step_3_tear {inp : MProd Nat (Vector F 3)} {count}:
  Poseidon.partial_rounds_step_3 inp count.succ =
  Poseidon.partial_rounds_step_3 ⟨inp.1.succ.succ.succ, Poseidon.partial_round inp.2 (round_constants' inp.1)⟩ count := by
  conv =>
    lhs
    simp [Poseidon.partial_rounds_step_3, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  conv =>
    rhs
    simp [Poseidon.partial_rounds_step_3, forIn, Std.Range.forIn, Std.Range.forIn.loop, round_constants']
  split; rename_i h; rw [←h]; clear h
  split; rename_i h; rw [←h]; clear h
  simp [loop_invariant]

lemma partial_round_const_count {inp : MProd Nat (Vector F 3)} {count}:
  (Poseidon.partial_rounds_step_3 inp count).1 = inp.1 + count * 3 := by
  induction count generalizing inp with
  | zero =>
    simp [Poseidon.partial_rounds_step_3, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  | succ count ih =>
    rw [partial_round_step_3_tear, ih]
    simp
    linarith

lemma partial_rounds_uncps {S : Vector F 3} {start count : Nat} {k : Vector F 3 -> Prop}:
  half_rounds_cps' S start count k = k (Poseidon.partial_rounds_step_3 ⟨start, S⟩ count).2 := by
  induction count generalizing start S with
  | zero =>
    simp [half_rounds_cps', Poseidon.partial_rounds_step_3, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  | succ count ih =>
    rw [partial_round_step_3_tear]
    rw [half_rounds_cps'_tear]
    apply ih

lemma full_rounds_uncps {S : Vector F 3} {start count : Nat} {k : Vector F 3 -> Prop}:
  full_rounds_cps' S start count k = k (Poseidon.full_rounds_step_3 ⟨start, S⟩ count).2 := by
  induction count generalizing start S with
  | zero =>
    simp [full_rounds_cps', Poseidon.full_rounds_step_3, forIn, Std.Range.forIn, Std.Range.forIn.loop]
  | succ count ih =>
    rw [full_round_step_3_tear]
    rw [full_rounds_cps'_tear]
    apply ih

def step_2 (input_words : Vector F 3): Vector F 3 := Id.run do
  let R_f := Poseidon.R_F / 2
  let mut round_constants_counter := 0
  let mut state_words := input_words
  match Poseidon.full_rounds_step_3 (MProd.mk round_constants_counter state_words) R_f with
  | ⟨rc, sw⟩ => do
    round_constants_counter := 12
    state_words := sw

  match Poseidon.partial_rounds_step_3 (MProd.mk round_constants_counter state_words) Poseidon.R_P with
  | ⟨rc, sw⟩ => do
    round_constants_counter := 183
    state_words := sw

  match Poseidon.full_rounds_step_3 (MProd.mk round_constants_counter state_words) R_f with
  | ⟨rc, sw⟩ => do
    round_constants_counter := 195
    state_words := sw

  state_words

lemma step_2_go {input_words : Vector F 3}: Poseidon.step_1 input_words = step_2 input_words := by
  unfold Poseidon.step_1
  simp
  simp [Poseidon.full_rounds_step_2_go, Poseidon.partial_rounds_step_2_go]
  simp [Poseidon.full_rounds_step_3_go, Poseidon.partial_rounds_step_3_go]
  simp [Id.run]
  split; rename_i h; rw [←h]; clear h
  split; rename_i h; rw [←h]; clear h
  (
    split
    rename_i rc sw h
    have : sw = (MProd.mk rc sw).2 := by rfl
    rw [this, ←h]
    clear this rc sw h
  )
  have : ∀ (a : Id (MProd Nat (Vector F 3))), a = MProd.mk a.1 a.2 := by
    intro a
    cases a
    rfl
  unfold step_2
  simp [Id.run]
  (
    split
    rename_i rc sw h
    have : sw = (MProd.mk rc sw).2 := by rfl
    rw [this, ←h]
    clear this rc sw h
  )
  (
    split
    rename_i rc sw h
    have : sw = (MProd.mk rc sw).2 := by rfl
    rw [this, ←h]
    clear this rc sw h
  )
  (
    split
    rename_i rc sw h
    have : sw = (MProd.mk rc sw).2 := by rfl
    rw [this, ←h]
    clear this rc sw h
  )
  apply congrArg
  apply congr
  {
    apply congrArg
    rw [this (Poseidon.partial_rounds_step_3 _ _), partial_round_const_count]
    apply congr
    {
      apply congrArg
      rw [full_round_const_count]
      simp
    }
    {
      apply congrArg
      apply congr
      {
        apply congrArg
        rw [this (Poseidon.full_rounds_step_3 _ _), full_round_const_count]
        rfl
      }
      { rfl }
    }
  }
  { rfl }

lemma congrArg2 { a b } {c d} {f : α -> β -> γ }: a = b -> c = d -> f a c = f b d := by
  intros
  congr

lemma vec_zero_eq (v1 v2 : Vector F 3): v1 = v2 -> v1[0] = v2[0] := by
  intro h
  rw [h]

lemma poseidon_uncps (A B : F) (k : F -> Prop): Poseidon A B k = k (Poseidon.perm vec![0, A, B])[0] := by
  rw [looped_Poseidon'_go, looped_Poseidon', full_rounds_uncps, partial_rounds_uncps, full_rounds_uncps]
  apply congrArg
  simp [Poseidon.step1_go, step_2_go, step_2]
  simp [Id.run]
  apply vec_zero_eq
  (
    split
    rename_i rc sw h
    have : sw = (MProd.mk rc sw).2 := by rfl
    rw [this, ←h]
    clear this rc sw h
  )
  (
    split
    rename_i rc sw h
    have : sw = (MProd.mk rc sw).2 := by rfl
    rw [this, ←h]
    clear this rc sw h
  )
  (
    split
    rename_i rc sw h
    have : sw = (MProd.mk rc sw).2 := by rfl
    rw [this, ←h]
    clear this rc sw h
  )
  congr