import ProvenZk.PoseidonExtract
import ProvenZk.Poseidon
import ProvenZk.VectorExtensions
import ProvenZk.Ext.Range
-- import Mathlib

variable [Fact (Nat.Prime Order)]

lemma fin_mod { n } {x : Fin n} : x.val = x.val % n := by
  have : _ := x.isLt
  simp [Nat.mod_eq_of_lt this]

lemma iff_to_eq {α} {a b: α} {k : α -> Prop }: a = b -> (k a ↔ k b) := by intro eq; rw [eq]

lemma sbox_uncps (A : F) (k : F -> Prop): sbox A k = k (A ^ 5) := by
  unfold sbox
  simp [Gates.mul]
  apply iff_to_eq
  repeat (rw [pow_succ])
  rw [pow_zero, mul_one, mul_assoc]

lemma mds_uncps (S : Vector F 3) (k : Vector F 3 -> Prop): mds_3 S k = k (Poseidon.mds_matmul S) := by
  simp [mds_3, Gates.add, Gates.mul]
  apply iff_to_eq
  simp [Poseidon.mds_matmul, Vector.to_column, Matrix.to_vector, Vector.ofFn, Matrix.of, Matrix.mul, Matrix.dotProduct]
  simp [Finset.univ, Fintype.elems, mul_comm, add_assoc, Poseidon.MDS_matrix_field, Poseidon.MDS_matrix]
  simp [Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction]
  conv => rhs; enter [2,2]; simp [mul_comm]
  congr <;> { rw [←S.cons_head_tail]; rfl}

lemma full_round_uncps (S C: Vector F 3) (k : Vector F 3 -> Prop): fullRound_3_3 S C k = k (Poseidon.full_round S C) := by
  conv => lhs; simp [fullRound_3_3, Gates.add, sbox_uncps, mds_uncps]

lemma half_round_uncps (S C: Vector F 3) (k : Vector F 3 -> Prop): halfRound_3_3 S C k = k (Poseidon.partial_round S C) := by
  conv => lhs; simp [halfRound_3_3, Gates.add, sbox_uncps, mds_uncps]

lemma partial_rounds_uncps {S : Vector F 3} {start count : Nat} {k : Vector F 3 -> Prop}:
  half_rounds_cps S start count k = k (Poseidon.partial_rounds S start count) := by
  induction count generalizing start S with
  | zero =>
    simp [half_rounds_cps, Poseidon.partial_rounds, forIn, Std.Range.forIn, Std.Range.forIn.loop, Id.run]
  | succ count ih =>
    unfold half_rounds_cps
    rw [half_round_uncps, ih]
    unfold Poseidon.partial_rounds
    simp [Id.run, forIn]
    apply iff_to_eq
    simp [Std.Range.counter_elide_2]
    rw [←zero_add (Nat.succ count), Std.Range.forIn_startSucc]
    simp_arith
    conv => rhs; arg 1; rw [←Nat.add_one, ←Nat.add_one]
    rw [←Std.Range.forIn_ixShift]
    congr
    funext i a
    have : (i + 1) * 3 = i * 3 + 3 := by simp_arith
    rw [this]
    rw [←Nat.add_assoc]
    have : i * 3 = 3 * i := by simp_arith
    rw [this]
    simp_arith


lemma full_rounds_uncps {S : Vector F 3} {start count : Nat} {k : Vector F 3 -> Prop}:
  full_rounds_cps S start count k = k (Poseidon.full_rounds S start count) := by
  induction count generalizing start S with
  | zero =>
    simp [full_rounds_cps, Poseidon.full_rounds, forIn, Std.Range.forIn, Std.Range.forIn.loop, Id.run]
  | succ count ih =>
    unfold full_rounds_cps
    rw [full_round_uncps, ih]
    unfold Poseidon.full_rounds
    simp [Id.run, forIn]
    apply iff_to_eq
    simp [Std.Range.counter_elide_2]
    rw [←zero_add (Nat.succ count), Std.Range.forIn_startSucc]
    simp_arith
    conv => rhs; arg 1; rw [←Nat.add_one, ←Nat.add_one]
    rw [←Std.Range.forIn_ixShift]
    congr
    funext i a
    have : (i + 1) * 3 = i * 3 + 3 := by simp_arith
    rw [this]
    rw [←Nat.add_assoc]
    have : i * 3 = 3 * i := by simp_arith
    rw [this]
    simp_arith

lemma poseidon_uncps (A B : F) (k : F -> Prop): Poseidon A B k = k (Poseidon.perm vec![0, A, B])[0] := by
  simp [
    looped_Poseidon_go,
    looped_Poseidon,
    full_rounds_uncps,
    partial_rounds_uncps,
    full_rounds_uncps,
    Poseidon.step_2_go,
    Poseidon.step_2
  ]
  rfl