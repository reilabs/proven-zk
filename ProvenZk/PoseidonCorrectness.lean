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

def mds_matmul (S : Vector F 3) : Vector F 3 :=
  let smat := Matrix.column_from_vector S
  let rmat := Poseidon.MDS_matrix_field.mul smat
  vec![rmat 0 0, rmat 1 0, rmat 2 0]

lemma vec_eq (a b : α) (t s : Vector α n) : a = b -> t = s -> a ::ᵥ t = b ::ᵥ s := by
  intros
  congr

lemma mds_uncps (S : Vector F 3) (k : Vector F 3 -> Prop): mds_3 S k = k (mds_matmul S) := by
  conv => lhs; simp [mds_3, Gates.add, Gates.mul]
  congr
  simp [mds_matmul, Matrix.mul_apply]
  repeat (any_goals (apply vec_eq))
  . simp [Finset.univ, Fintype.elems, mul_comm, add_assoc, Matrix.column_from_vector]
  . simp [Finset.univ, Fintype.elems, mul_comm, add_assoc, Matrix.column_from_vector]
  . simp [Finset.univ, Fintype.elems]
    conv => lhs; simp [mul_comm, add_assoc]
  . rfl

def full_round (S C: Vector F 3) : Vector F 3 :=
  mds_matmul vec![(S[0] + C[0]) ^ 5, (S[1] + C[1]) ^ 5, (S[2] + C[2]) ^ 5]

def full_round_with_const (i: Nat) (S : Vector F 3) : Vector F 3 :=
  let c := vec![Poseidon.round_constants_field[3 * i]!, Poseidon.round_constants_field[3 * i + 1]!, Poseidon.round_constants_field[3 * i + 2]!]
  full_round S c

lemma full_round_uncps (S C: Vector F 3) (k : Vector F 3 -> Prop): fullRound_3_3 S C k = k (full_round S C) := by
  conv => lhs; simp [fullRound_3_3, Gates.add, sbox_uncps, mds_uncps]

def half_round (S C: Vector F 3) : Vector F 3 :=
  mds_matmul vec![(S[0] + C[0]) ^ 5, S[1] + C[1], S[2] + C[2]]

def half_round_with_const(i: Nat) (S : Vector F 3) : Vector F 3 :=
  let c := vec![Poseidon.round_constants_field[3 * i]!, Poseidon.round_constants_field[3 * i + 1]!, Poseidon.round_constants_field[3 * i + 2]!]
  half_round S c

lemma half_round_uncps (S C: Vector F 3) (k : Vector F 3 -> Prop): halfRound_3_3 S C k = k (half_round S C) := by
  conv => lhs; simp [halfRound_3_3, Gates.add, sbox_uncps, mds_uncps]


def generic_loop (S : α) (start stop: Nat) (f : Nat -> α -> α) : α := Id.run do
  let mut state := S
  for i in [start:stop] do
    state := f i state
  state

def generic_recur (S : α) (start stop : Nat) (f : Nat -> α -> α) : α := go stop start stop S where
  go fuel start stop s := if stop ≤ start then s else match fuel with
    | Nat.zero => s
    | Nat.succ fuel => go fuel (start + 1) stop (f start s)

-- fuel₀ = stop, start₀ = start
-- fuel₁ = stop - 1, start₁ = start + 1
-- fuel₂ = stop - 2, start₂ = start + 2
-- fuelₙ + startₙ = start + stop

lemma generic_recur_empty (S: α) (start: Nat) (f : Nat -> α -> α):
  generic_recur S start start f = S := by
  unfold generic_recur
  unfold generic_recur.go
  simp


lemma generic_recur_cons (S : α) (start d : Nat) (f : Nat -> α -> α):
  generic_recur S start (start + d.succ) f = generic_recur  (f start S) (start + 1) (start + d.succ) f := by
  have : ∀ (S : α) (start fuel1 fuel2 d : Nat) (f : Nat -> α -> α),
    (fuel1 >= d.succ) ->
    (fuel2 >= d.succ) ->
    generic_recur.go f fuel1 start (start + d.succ) S = generic_recur.go f fuel2 (start + 1) (start + d.succ) (f start S) := by
    intro S start fuel1 fuel2 d f h1 h2
    induction d generalizing fuel1 fuel2 start S f with
    | zero =>
      unfold generic_recur.go
      simp
      split
      . contradiction
      . unfold generic_recur.go; simp
    | succ d ih =>
      unfold generic_recur.go
      simp
      cases fuel1
      {contradiction}
      cases fuel2
      {contradiction}
      simp
      split
      {contradiction}
      simp
      conv => lhs; arg 4; rw [Nat.add_succ, ←Nat.succ_add, Nat.add_one, ←Nat.add_one]
      rw [ih]
      conv => rhs; arg 4; rw [Nat.add_succ, ←Nat.succ_add, Nat.add_one, ←Nat.add_one]
      all_goals linarith

  unfold generic_recur
  conv => lhs; arg 2; rw [Nat.add_succ]
  rw [this] <;> simp_arith

lemma generic_recur_snoc (S: α) (start d: Nat) (f: Nat -> α -> α):
  generic_recur S start (start + d.succ) f = f (start + d) (generic_recur S start (start + d) f) := by
  have go_snoc : ∀ fuel start d s,
    fuel > d ->
    generic_recur.go f fuel start (start + d.succ) s = f (start + d) (generic_recur.go f (fuel - 1) start (start + d) s) := by
    intro fuel start d s
    induction d generalizing fuel start s with
    | zero =>
      intro h
      unfold generic_recur.go
      simp
      split
      . contradiction
      . simp
        unfold generic_recur.go
        simp
    | succ d ih =>
      intro h
      conv => lhs ; unfold generic_recur.go ; simp
      cases fuel
      . contradiction
      . rename_i fuelᵢ
        simp
        conv =>
          lhs
          arg 4
          rw [Nat.add_succ, ←Nat.succ_add, Nat.add_one]
          arg 1
          rw [←Nat.add_one]
        rw [ih]
        . conv => lhs; arg 1; rw [Nat.add_assoc]; rw [Nat.one_add]
          apply congrArg
          conv =>
            rhs
            unfold generic_recur.go
            simp
          cases fuelᵢ
          . contradiction
          . simp
            conv => lhs; arg 4; rw [Nat.add_assoc]; rw [Nat.one_add]
        . linarith

  unfold generic_recur
  apply go_snoc
  linarith



def generic_recur_non_tail (S : α) (start stop : Nat) (f : Nat -> α -> α): α := go stop start stop S where
  go fuel start stop s := if stop ≤ start then s else match fuel with
    | Nat.zero => s
    | Nat.succ fuel => f (stop - 1)  (go fuel start (stop - 1) s)

lemma generic_recur_tail_non_tail (S: α) (start d : Nat) (f : Nat -> α -> α) :
  generic_recur S start (start + d) f = generic_recur_non_tail S start (start + d) f := by
  have : ∀ fuel start stop s, generic_recur.go f fuel start stop s = generic_recur_non_tail.go f fuel start stop s := by
    intro fuel start stop s
    induction fuel generalizing start stop s with
    | zero => rfl
    | succ fuel ih =>
      unfold generic_recur.go
      split
      . sorry
      . sorry
      -- unfold generic_recur_non_tail.go
      -- split_ifs
      -- . rfl
      -- . simp
      --   rw [ih]
  induction d with
  | zero =>
    simp [generic_recur, generic_recur_non_tail]
    unfold generic_recur.go
    unfold generic_recur_non_tail.go
    simp
  | succ d ih =>
    simp [generic_recur, generic_recur_non_tail]
    unfold generic_recur.go
    unfold generic_recur_non_tail.go
    simp
    sorry


theorem generic_loop_or_recur (S : α) (start stop: Nat) (f : Nat -> α -> α) : generic_loop S start stop f = generic_recur S start stop f := by
  have inside : ∀ s (fuel start stop : Nat),
    generic_recur.go f fuel start stop s =
    Id.run (Std.Range.forIn.loop (fun i x => pure (ForInStep.yield (f i x))) fuel start stop 1 s) := by
      intros s fuel start stop
      simp [Id.run]
      induction fuel generalizing start s with
      | zero =>
        simp [generic_recur.go, Std.Range.forIn.loop]
      | succ fuel ih =>
        simp [generic_recur.go, Std.Range.forIn.loop]
        split_ifs
        . rfl
        . apply ih
  simp [generic_loop, generic_recur, Id.run, forIn, Std.Range.forIn, inside]

def full_rounds_loop (S : Vector F 3) (start stop : Nat) : Vector F 3 := Id.run do
  let mut state := S
  for i in [start:stop] do
    state := full_round_with_const i state
  state

def round_constants' (i : Nat) : Vector F 3 := vec![Poseidon.round_constants_field[3 * i]!, Poseidon.round_constants_field[3 * i + 1]!, Poseidon.round_constants_field[3 * i + 2]!]

def full_rounds_no_loop (S : Vector F 3) (start stop : Nat) : Vector F 3 := generic_recur S start stop fun i S =>
  full_round S vec![Poseidon.round_constants_field[3 * i]!, Poseidon.round_constants_field[3 * i + 1]!, Poseidon.round_constants_field[3 * i + 2]!]

lemma full_rounds_loop_generic S start stop : full_rounds_loop S start stop = generic_loop S start stop full_round_with_const := by
  simp [full_rounds_loop, generic_loop, full_round_with_const]

lemma full_rounds_no_loop_generic S start stop : full_rounds_no_loop S start stop = generic_recur S start stop full_round_with_const := by
  simp [full_rounds_no_loop, generic_recur, full_round_with_const]

lemma full_rounds_loop_recur {S : Vector F 3} {start count : Nat} : full_rounds_loop S start count = full_rounds_no_loop S start count := by
  rw [full_rounds_loop_generic, full_rounds_no_loop_generic, generic_loop_or_recur]

def half_rounds_loop (S : Vector F 3) (start stop : Nat) : Vector F 3 := Id.run do
  let mut state := S
  for i in [start:stop] do
    state := half_round_with_const i state
  state

def half_rounds_no_loop (S : Vector F 3) (start stop : Nat) : Vector F 3 := generic_recur S start stop fun i S =>
  half_round S vec![Poseidon.round_constants_field[3 * i]!, Poseidon.round_constants_field[3 * i + 1]!, Poseidon.round_constants_field[3 * i + 2]!]

lemma half_rounds_loop_generic S start stop : half_rounds_loop S start stop = generic_loop S start stop half_round_with_const := by
  simp [half_rounds_loop, generic_loop, half_round_with_const]

lemma half_rounds_no_loop_generic S start stop : half_rounds_no_loop S start stop = generic_recur S start stop half_round_with_const := by
  simp [half_rounds_no_loop, generic_recur, half_round_with_const]

lemma half_rounds_loop_recur (S : Vector F 3) (start count : Nat) : half_rounds_loop S start count = half_rounds_no_loop S start count := by
  rw [half_rounds_loop_generic, half_rounds_no_loop_generic, generic_loop_or_recur]

def poseidon_looped_fnd (S : Vector F 3): Vector F 3 := Id.run do
  let mut state := S
  state := full_rounds_loop state 0 4
  state := half_rounds_loop state 4 61
  state := full_rounds_loop state 61 65
  state

def poseidon_non_looped (S : Vector F 3): Vector F 3 := Id.run do
  let mut state := S
  state := full_rounds_no_loop state 0 4
  state := half_rounds_no_loop state 4 61
  state := full_rounds_no_loop state 61 65
  state

def poseidon_looped (S : Vector F 3): Vector F 3 := Id.run do
  let mut state := S
  for i in [0:4] do
    let c := vec![Poseidon.round_constants_field[3 * i]!, Poseidon.round_constants_field[3 * i + 1]!, Poseidon.round_constants_field[3 * i + 2]!]
    state := full_round state c
  for i in [4:61] do
    let c := vec![Poseidon.round_constants_field[3 * i]!, Poseidon.round_constants_field[3 * i + 1]!, Poseidon.round_constants_field[3 * i + 2]!]
    state := half_round state c
  for i in [61:65] do
    let c := vec![Poseidon.round_constants_field[3 * i]!, Poseidon.round_constants_field[3 * i + 1]!, Poseidon.round_constants_field[3 * i + 2]!]
    state := full_round state c
  state

theorem unIdRun (x : Id α) : Id.run x = x := by
  simp [Id.run]

theorem poseidon_looped_unfndd S : poseidon_looped_fnd S = poseidon_looped S := by
  simp [
    poseidon_looped_fnd,
    poseidon_looped,
    full_rounds_loop,
    half_rounds_loop,
    full_round_with_const,
    half_round_with_const,
    unIdRun
  ]

lemma poseidon_looped_non_looped (S : Vector F 3): poseidon_looped S = poseidon_non_looped S := by
  rw [←poseidon_looped_unfndd, poseidon_looped_fnd]
  simp [unIdRun]
  rw [full_rounds_loop_recur, half_rounds_loop_recur, full_rounds_loop_recur]
  sorry
  -- rw


-- set_option maxRecDepth 1024
-- set_option maxHeartbeats 0

lemma vecEqs (v₁ v₂ : Vector α 3) : v₁ = v₂ -> v₁[0] = v₂[0] := by intros; congr

lemma congrArg2 {a b : α} { c d : β } {f : α -> β -> γ } : a = b -> c = d -> f a c = f b d :=
  by intros; congr

-- set_option maxRecDepth 1024

def zipfold (f : α -> β -> α) (init : α) (params : Vector β len) := match len with
  | Nat.zero => init
  | Nat.succ _ => zipfold f (f init params.head) params.tail

def poseidon_constants_rounds (start d : Nat) : Vector (Vector F 3) d := match d with
  | Nat.zero => Vector.nil
  | Nat.succ d => (poseidon_constants_rounds start d).snoc (round_constants' (start + d))

-- theorem full_rounds_no_loop_zipfold (start d : Nat) : full_rounds_no_loop ()

lemma zipfold_1 (f : α -> β -> α) (init : α) (param : β) : f init param = zipfold f init vec![param] := by
  simp [zipfold]

lemma zipfold_next (f : α -> β -> α) (init: α) (param : β) (params : Vector β len) : zipfold f (f init param) params = zipfold f init (param ::ᵥ params) := by
  simp [zipfold]

lemma zipfold_snoc (f : α -> β -> α) (init: α) (param : β) (params : Vector β len) : zipfold f init (params.snoc param) = f (zipfold f init params) param := by
  induction len generalizing init with
  | zero =>
    simp [zipfold, Vector.eq_nil]
  | succ len ih =>
    conv =>
      lhs
      unfold zipfold
      rw [Vector.tail_snoc, Vector.head_snoc, ih]


def full_rounds_zipfold (start len : Nat) (inp : Vector F 3): Vector F 3 :=
  zipfold full_round inp (poseidon_constants_rounds start len)

lemma full_rounds_recur_zipfold {start len : Nat} {inp : Vector F 3}:
  full_rounds_zipfold start len inp = full_rounds_no_loop inp start (start + len) := by
  induction len generalizing inp with
  | zero =>
    simp [full_rounds_zipfold, full_rounds_no_loop, generic_recur_empty, poseidon_constants_rounds, zipfold]
  | succ len ih =>
    simp [full_rounds_zipfold, full_rounds_no_loop] at ih
    simp [full_rounds_zipfold, poseidon_constants_rounds, zipfold_snoc, round_constants']
    simp [full_rounds_no_loop, generic_recur_snoc]
    congr
    apply ih

-- set_option maxRecDepth 4096
-- set_option maxHeartbeats 0

lemma half_rounds_recur_zipfold {start len : Nat} {inp : Vector F 3}:
  zipfold half_round inp (poseidon_constants_rounds start len) = half_rounds_no_loop inp start (start + len) := by
  induction len generalizing inp with
  | zero =>
    simp [half_rounds_no_loop, generic_recur_empty, poseidon_constants_rounds, zipfold]
  | succ len ih =>
    simp [half_rounds_no_loop] at ih
    simp [poseidon_constants_rounds, zipfold_snoc, round_constants']
    simp [half_rounds_no_loop, generic_recur_snoc]
    congr
    apply ih

lemma iff_reverse (v1 v2 : Vector α len): v1 = v2 ↔ v1.reverse = v2.reverse := by sorry

lemma vec_get_list {v : Vector α len} {i : Nat} { _ : i < len } : v[i] = v.toList.get ⟨i, by rw [Vector.toList_length]; assumption⟩  := by
  simp [getElem!, getElem, List.get]

lemma iff_to_eq (a b : α) (k : α -> Prop): a = b -> (k a ↔ k b) := by intro hp; rw [hp]

set_option maxHeartbeats 0
set_option maxRecDepth 1024

                      -- (forIn { start := 0, stop := 3, step := 1 } state_words fun i r =>
                      --   ForInStep.yield (Vector.set r (↑i) (r[i]! ^ 5)))))

lemma lemma1 {state_words : Vector F 3}:
  (forIn (m := Id) [0:3] state_words fun (i:Nat) r => ForInStep.yield (Vector.set r i (r[i]! ^ 5)))
  = vec![state_words[0]! ^ 5, state_words[1]! ^ 5, state_words[2]! ^ 5] := by
  sorry

lemma looped_poseidon_correct {inp : Vector F 3}: poseidon_looped inp = Poseidon.perm inp := by
  simp [Poseidon.perm, Poseidon.R_F, Poseidon.t]
  simp [Id.run]
  split


--   rw [unIdRun]
--   split


-- THIS ALSO WORKS

-- lemma poseidon_uncps (A B : F) (k : F -> Prop): Poseidon A B k = k (poseidon_looped vec![0, A, B])[0] := by
--   simp [Poseidon, full_round_uncps, half_round_uncps]
--   apply iff_to_eq
--   apply Vector.head_eq
--   simp [poseidon_looped_non_looped, poseidon_non_looped, unIdRun]
--   repeat (apply congrArg2)
--   all_goals rfl





-- THIS WORKS

-- lemma poseidon_uncps (A B : F) (k : F -> Prop): Poseidon A B k = k (poseidon_looped vec![0, A, B])[0] := by
--   simp [Poseidon, full_round_uncps, half_round_uncps]
--   apply iff_to_eq
--   apply Vector.head_eq
--   rw [zipfold_1 full_round _ _]
--   repeat (rw [zipfold_next full_round _ _])
--   rw [zipfold_1 half_round]
--   repeat (rw [zipfold_next half_round])
--   rw [zipfold_1 full_round]
--   repeat (rw [zipfold_next full_round])
--   rw [poseidon_looped_non_looped]
--   simp [poseidon_non_looped, unIdRun]
--   have : 65 = 61 + 4 := by rfl
--   rw [this, ←full_rounds_recur_zipfold]
--   rw [full_rounds_zipfold]
--   apply congr
--   apply congr
--   { rfl }
--   have : 61 = 4 + 57 := by rfl
--   rw [this, ←half_rounds_recur_zipfold]
--   apply congr
--   apply congr
--   { rfl }
--   have : 4 = 0 + 4 := by rfl
--   rw [this]
--   rw [←full_rounds_recur_zipfold]
--   rw [full_rounds_zipfold]
--   apply congr
--   {rfl}
--   {
--     rfl
--   }
--   {
--     simp [poseidon_constants_rounds]
--     rw [iff_reverse]
--     repeat (rw [Vector.reverse_snoc_cons])
--     rw [Vector.reverse_singleton]
--     apply Vector.eq
--     rw [Vector.toList_reverse]
--     simp
--     repeat (apply And.intro; swap)
--     all_goals rfl
--   }
--   {
--     rfl
--   }



--- END WORKS


  -- apply vecEqs
  -- simp [
  --   poseidon_looped_non_looped,
  --   poseidon_non_looped,
  --   unIdRun
  -- ]
  -- simp [full_rounds_no_loop]
  -- have : 65 = 61 + 4 := by rfl
  -- simp [this, generic_recur_snoc, generic_recur_empty]
  -- apply congrArg2; rotate_left; unfold Poseidon.round_constants_field; simp_arith;


  -- have : 4 = 0 + 4 := by rfl
  -- conv in generic_recur _ 0 4 _ => simp [this]
  -- -- simp [this]
  -- have : 65 = 61 + 4 := by rfl

  -- simp [generic_recur_snoc, generic_recur_empty]






    -- simp [poseidon_looped_non_looped, poseidon_non_looped, unIdRun, full_rounds_no_loop, half_rounds_no_loop]



--   simp_arith
--   rfl

  -- conv =>
  --   lhs
  --   arg 2

  -- congr

  -- apply congrArg
  -- simp [sbox, Gates.mul]
  -- conv in (_ ^ _) => whnf
  -- rfl


-- lemma looped_correct (A B : F) (k : F -> Prop): looped_Poseidon A B k ↔ k (Poseidon.perm #[0, A, B])[0]! := by
--   unfold looped_Poseidon
--   unfold Poseidon.perm
--   simp [Id.run, forIn, Std.Range.forIn, Poseidon.R_F]
--   unfold Std.Range.forIn.loop

--   sorry