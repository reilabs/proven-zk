import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.Defs

import ProvenZk.Ext.Fin
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

theorem vector_reverse_inj {a b : Vector α d} : Vector.reverse a = Vector.reverse b ↔ a = b := by
  apply Iff.intro
  . intro h
    induction d with
    | zero =>
      cases a using Vector.casesOn
      cases b using Vector.casesOn
      rfl
    | succ d ih =>
      cases a using Vector.revCasesOn
      cases b using Vector.revCasesOn
      simp [Vector.eq_cons_iff] at h
      cases h;
      subst_vars
      congr
      apply ih
      assumption
  . intro h; congr

theorem vector_map_inj {a b : Vector α d} {f_inj : ∀ a b, f a = f b → a = b}: a.map f = b.map f ↔ a = b := by
  apply Iff.intro
  . intro h
    induction d with
    | zero =>
      cases a using Vector.casesOn
      cases b using Vector.casesOn
      rfl
    | succ d ih =>
      cases a using Vector.casesOn
      cases b using Vector.casesOn
      simp [Vector.eq_cons_iff] at h
      rcases h with ⟨h, t⟩
      have := f_inj _ _ h
      have := ih t
      congr
  . intro h; congr

def dropLast { n : Nat } (v : Vector α n) : Vector α (n-1) := ⟨List.dropLast v.toList, by simp⟩

lemma toList_dropLast { n : Nat } (v : Vector α n) : v.dropLast.toList = v.toList.dropLast := by
  rfl

lemma vector_list_vector {d} {x₁ x₂ : α} {xs : Vector α d} : (x₁ ::ᵥ x₂ ::ᵥ xs).dropLast = x₁ ::ᵥ (x₂ ::ᵥ xs).dropLast := by
  rfl

@[simp]
theorem vector_get_zero {vs : Vector i n} : (v ::ᵥ vs)[0] = v := by rfl

@[simp]
theorem vector_get_succ_fin {vs : Vector i n} {i : Fin n} : (v ::ᵥ vs)[i.succ] = vs[i] := by rfl

@[simp]
theorem vector_get_succ_nat {vs : Vector i n} {i : Nat} {h : i.succ < n.succ } : (v ::ᵥ vs)[i.succ]'h = vs[i]'(by linarith) := by rfl

@[simp]
theorem vector_get_snoc_last { vs : Vector α n }:
  (vs.snoc v).get (Fin.last n) = v := by
  induction n with
  | zero =>
    cases vs using Vector.casesOn; rfl
  | succ n ih =>
    cases vs using Vector.casesOn
    rw [Fin.last_succ_eq_succ_last, Vector.snoc_cons, Vector.get_cons_succ, ih]

@[simp]
lemma snoc_get_castSucc {vs : Vector α n}: (vs.snoc v).get (Fin.castSucc i) = vs.get i := by
  cases n
  case zero => cases i using finZeroElim
  case succ n =>
  induction n with
  | zero =>
    cases i using Fin.cases with
    | H0 => cases vs using Vector.casesOn with | cons hd tl => simp
    | Hs i => cases i using finZeroElim
  | succ n ih =>
    cases vs using Vector.casesOn with | cons hd tl =>
    cases i using Fin.cases with
    | H0 => simp
    | Hs i => simp [Fin.castSucc_succ_eq_succ_castSucc, ih]

theorem vector_get_val_getElem {v : Vector α n} {i : Fin n}: v[i.val]'(i.prop) = v.get i := by
  rfl

theorem getElem_def {v : Vector α n} {i : Nat} {prop}: v[i]'prop = v.get ⟨i, prop⟩ := by
  rfl

@[simp]
lemma vector_get_snoc_fin_prev {vs : Vector α n} {v : α} {i : Fin n}:
  (vs.snoc v)[i.val]'(by (have := i.prop); linarith) = vs[i.val]'(i.prop) := by
  simp [vector_get_val_getElem, getElem_def, Fin.castSucc_def]

theorem ofFn_snoc' { fn : Fin (Nat.succ n) → α }:
  Vector.ofFn fn = Vector.snoc (Vector.ofFn (fun (x : Fin n) => fn (Fin.castSucc x))) (fn n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => lhs; rw [Vector.ofFn, ih]
    simp [Vector.ofFn]
    congr
    simp [Fin.succ]
    congr
    simp [Nat.mod_eq_of_lt]

def allIxes (f : α → Prop) : Vector α n → Prop := fun v => ∀(i : Fin n), f v[i]

@[simp]
theorem allIxes_cons : allIxes f (v ::ᵥ vs) ↔ f v ∧ allIxes f vs := by
  simp [allIxes, GetElem.getElem]
  apply Iff.intro
  . intro h
    exact ⟨h 0, fun i => h i.succ⟩
  . intro h i
    cases i using Fin.cases
    . simp [h.1]
    . simp [h.2]

@[simp]
theorem allIxes_nil : allIxes f Vector.nil := by
  simp [allIxes]

theorem getElem_allIxes {v : { v: Vector α n // allIxes prop v  }} {i : Nat} { i_small : i < n}:
  v.val[i]'i_small = ↑(Subtype.mk (v.val.get ⟨i, i_small⟩) (v.prop ⟨i, i_small⟩)) := by rfl

theorem getElem_allIxes₂ {v : { v: Vector (Vector α m) n // allIxes (allIxes prop) v  }} {i j: Nat} { i_small : i < n} { j_small : j < m}:
  (v.val[i]'i_small)[j]'j_small = ↑(Subtype.mk ((v.val.get ⟨i, i_small⟩).get ⟨j, j_small⟩) (v.prop ⟨i, i_small⟩ ⟨j, j_small⟩)) := by rfl

theorem allIxes_indexed {v : {v : Vector α n // allIxes prop v}} {i : Nat} {i_small : i < n}:
  prop (v.val[i]'i_small) := v.prop ⟨i, i_small⟩

theorem allIxes_indexed₂ {v : {v : Vector (Vector (Vector α a) b) c // allIxes (allIxes prop) v}}
  {i : Nat} {i_small : i < c}
  {j : Nat} {j_small : j < b}:
  prop ((v.val[i]'i_small)[j]'j_small) :=
  v.prop ⟨i, i_small⟩ ⟨j, j_small⟩

theorem allIxes_indexed₃ {v : {v : Vector (Vector (Vector α a) b) c // allIxes (allIxes (allIxes prop)) v}}
  {i : Nat} {i_small : i < c}
  {j : Nat} {j_small : j < b}
  {k : Nat} {k_small : k < a}:
  prop (((v.val[i]'i_small)[j]'j_small)[k]'k_small) :=
  v.prop ⟨i, i_small⟩ ⟨j, j_small⟩ ⟨k, k_small⟩

@[simp]
theorem map_ofFn {f : α → β} (g : Fin n → α) :
  Vector.map f (Vector.ofFn g) = Vector.ofFn (fun x => f (g x)) := by
  apply Vector.eq
  simp
  rfl

@[simp]
theorem map_id': Vector.map (fun x => x) v = v := by
  have : ∀α, (fun (x:α) => x) = id := by intro _; funext _; rfl
  rw [this, Vector.map_id]

end Vector
