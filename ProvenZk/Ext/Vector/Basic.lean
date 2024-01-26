import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Vector.Mem
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

theorem eq_cons : (x ::ᵥ xs) = (y ::ᵥ ys) ↔ x = y ∧ xs = ys := by
  simp [Vector.eq_cons_iff]

theorem reverse_eq {x y : Vector α n} : (x.reverse = y) ↔ (x = y.reverse) := by
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

theorem replicate_succ_snoc : Vector.replicate (Nat.succ n) a = (Vector.replicate n a).snoc a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => rhs; simp [←ih]

@[simp]
theorem replicate_reverse : Vector.reverse (Vector.replicate n a) = Vector.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ih, ←replicate_succ_snoc]

@[simp]
theorem map_replicate : Vector.map f (Vector.replicate n a) = Vector.replicate n (f a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [ih]

@[simp]
theorem reverse_inj {a b : Vector α d} : Vector.reverse a = Vector.reverse b ↔ a = b := by
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

@[simp]
theorem map_inj {a b : Vector α d} {f_inj : ∀ a b, f a = f b → a = b}: a.map f = b.map f ↔ a = b := by
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

@[simp]
theorem getElem_zero {vs : Vector i n} : (v ::ᵥ vs)[0] = v := by rfl

@[simp]
theorem get_succ_fin {vs : Vector i n} {i : Fin n} : (v ::ᵥ vs)[i.succ] = vs[i] := by rfl

@[simp]
theorem get_succ_nat {vs : Vector i n} {i : Nat} {h : i.succ < n.succ } : (v ::ᵥ vs)[i.succ]'h = vs[i]'(by linarith) := by rfl

@[simp]
theorem get_snoc_last { vs : Vector α n }:
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

theorem get_val_getElem {v : Vector α n} {i : Fin n}: v[i.val]'(i.prop) = v.get i := by
  rfl

theorem getElem_def {v : Vector α n} {i : Nat} {prop}: v[i]'prop = v.get ⟨i, prop⟩ := by
  rfl

@[simp]
lemma get_snoc_fin_prev {vs : Vector α n} {v : α} {i : Fin n}:
  (vs.snoc v)[i.val]'(by (have := i.prop); linarith) = vs[i.val]'(i.prop) := by
  simp [get_val_getElem, getElem_def, Fin.castSucc_def]

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

instance : Membership α (Vector α n) := ⟨fun x xs => x ∈ xs.toList⟩

@[simp]
theorem mem_def {xs : Vector α n} {x} : x ∈ xs ↔ x ∈ xs.toList := by rfl

-- def allElems (f : α → Prop) : Vector α n → Prop := fun v => ∀(a : α), a ∈ v → f a

-- @[simp]
-- theorem allElems_cons : Vector.allElems prop (v ::ᵥ vs) ↔ prop v ∧ allElems prop vs := by
--   simp [allElems]

-- @[simp]
-- theorem allElems_nil : Vector.allElems prop Vector.nil := by simp [allElems]

-- def allIxes (f : α → Prop) : Vector α n → Prop := fun v => ∀(i : Fin n), f v[i]

-- @[simp]
-- theorem allIxes_cons : allIxes f (v ::ᵥ vs) ↔ f v ∧ allIxes f vs := by
--   simp [allIxes, GetElem.getElem]
--   apply Iff.intro
--   . intro h
--     exact ⟨h 0, fun i => h i.succ⟩
--   . intro h i
--     cases i using Fin.cases
--     . simp [h.1]
--     . simp [h.2]

-- @[simp]
-- theorem allIxes_nil : allIxes f Vector.nil := by
--   simp [allIxes]

-- theorem getElem_allElems {v : { v: Vector α n // allElems prop v  }} {i : Nat} { i_small : i < n}:
--   v.val[i]'i_small = ↑(Subtype.mk (p := prop) (v.val.get ⟨i, i_small⟩) (by apply v.prop; simp)) := by rfl

-- theorem getElem_allElems₂ {v : { v: Vector (Vector α m) n // allElems (allElems prop) v  }} {i j: Nat} { i_small : i < n} { j_small : j < m}:
--   (v.val[i]'i_small)[j]'j_small = ↑(Subtype.mk (p := prop) ((v.val.get ⟨i, i_small⟩).get ⟨j, j_small⟩) (by apply v.prop; rotate_right; exact v.val.get ⟨i, i_small⟩; all_goals simp)) := by rfl

-- theorem allElems_indexed {v : {v : Vector α n // allElems prop v}} {i : Nat} {i_small : i < n}:
--   prop (v.val[i]'i_small) := by
--   apply v.prop
--   simp [getElem]

-- theorem allElems_indexed₂ {v : {v : Vector (Vector (Vector α a) b) c // allElems (allElems prop) v}}
--   {i : Nat} {i_small : i < c}
--   {j : Nat} {j_small : j < b}:
--   prop ((v.val[i]'i_small)[j]'j_small) := by
--   apply v.prop (v.val[i]'i_small) <;> simp [getElem]

-- theorem allElems_indexed₃ {v : {v : Vector (Vector (Vector α a) b) c // allElems (allElems (allElems prop)) v}}
--   {i : Nat} {i_small : i < c}
--   {j : Nat} {j_small : j < b}
--   {k : Nat} {k_small : k < a}:
--   prop (((v.val[i]'i_small)[j]'j_small)[k]'k_small) := by
--   apply v.prop
--   rotate_right
--   . exact (v.val[i]'i_small)[j]'j_small
--   rotate_right
--   . exact (v.val[i]'i_small)
--   all_goals simp [getElem]

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

def ofFnGet (v : Vector F d) : Vector F d := Vector.ofFn fun i => v[i.val]'i.prop
instance : HAppend (Vector α d₁) (Vector α d₂) (Vector α (d₁ + d₂)) := ⟨Vector.append⟩

@[simp]
theorem ofFnGet_id : ofFnGet v = v := by simp [ofFnGet, GetElem.getElem]

@[simp]
theorem hAppend_toList {v₁ : Vector α d₁} {v₂ : Vector α d₂}:
  (v₁ ++ v₂).toList = v₁.toList ++ v₂.toList := by rfl

theorem append_inj {v₁ w₁ : Vector α d₁} {v₂ w₂ : Vector α d₂}:
  v₁ ++ v₂ = w₁ ++ w₂ → v₁ = w₁ ∧ v₂ = w₂ := by
  intro h
  induction v₁, w₁ using Vector.inductionOn₂ with
  | nil =>
    apply And.intro rfl
    apply Vector.eq
    have := congrArg toList h
    simp at this
    assumption
  | cons ih =>
    have := congrArg toList h
    simp at this
    rcases this with ⟨h₁, h₂⟩
    rw [←hAppend_toList, ←hAppend_toList] at h₂
    have := Vector.eq _ _ h₂
    have := ih this
    cases this
    subst_vars
    apply And.intro <;> rfl

lemma eq_iff {n} {v w : Vector α n} : v = w ↔ v.toList = w.toList := by
  apply Iff.intro
  . intro h
    subst h
    rfl
  . intro h
    apply Vector.eq
    simp at h
    assumption

theorem append_inj_iff {v₁ w₁ : Vector α d₁} {v₂ w₂ : Vector α d₂}:
  v₁ ++ v₂ = w₁ ++ w₂ ↔ v₁ = w₁ ∧ v₂ = w₂ := by
  apply Iff.intro
  . exact append_inj
  . intro ⟨_, _⟩
    simp [*]

-- theorem allIxes_toList : Vector.allIxes prop v ↔ ∀ i, prop (v.toList.get i) := by
--   unfold Vector.allIxes
--   apply Iff.intro
--   . intro h i
--     rcases i with ⟨i, p⟩
--     simp at p
--     simp [GetElem.getElem, Vector.get] at h
--     have := h ⟨i, p⟩
--     conv at this => arg 1; whnf
--     exact this
--   . intro h i
--     simp [GetElem.getElem, Vector.get]
--     rcases i with ⟨i, p⟩
--     have := h ⟨i, by simpa⟩
--     conv at this => arg 1; whnf
--     exact this

-- theorem allElems_append {v₁ : Vector α n₁} {v₂ : Vector α n₂} : Vector.allElems prop (v₁ ++ v₂) ↔ Vector.allElems prop v₁ ∧ Vector.allElems prop v₂ := by
--   simp [allElems]
--   apply Iff.intro
--   . intro h
--     apply And.intro
--     . exact fun a hp => h a (Or.inl hp)
--     . exact fun a hp => h a (Or.inr hp)
--   . rintro ⟨_,_⟩ _ _ ; tauto

-- theorem SubVector_append {v₁ : Vector α d₁} {prop₁ : Vector.allIxes prop v₁ } {v₂ : Vector α d₂} {prop₂ : Vector.allIxes prop v₂}:
--   (Subtype.mk v₁ prop₁).val ++ (Subtype.mk v₂ prop₂).val =
--   (Subtype.mk (v₁ ++ v₂) (allIxes_append.mpr ⟨prop₁, prop₂⟩)).val := by eq_refl


-- theorem allIxes_iff_allElems : allIxes prop v ↔ ∀ a ∈ v, prop a := by
--   apply Iff.intro
--   . intro hp a ain
--     have := (Vector.mem_iff_get a v).mp ain
--     rcases this with ⟨i, h⟩
--     cases h
--     apply hp
--   . intro hp i
--     apply hp
--     apply Vector.get_mem

@[simp]
theorem getElem_map {i n : ℕ} {h : i < n} {v : Vector α n} : (Vector.map f v)[i]'h = f (v[i]'h) := by
  simp [getElem]

theorem map_singleton {a : α} {f : α → β} : Vector.map f (a ::ᵥ Vector.nil) = (f a ::ᵥ Vector.nil) := by
  rfl

@[simp]
lemma getElem_snoc_at_length {vs : Vector α n}: (vs.snoc v)[n]'(by simp_arith) = v := by
  induction n with
  | zero => cases vs using Vector.casesOn; rfl
  | succ n ih => cases vs using Vector.casesOn; simp [ih]

@[simp]
lemma getElem_snoc_before_length {vs : Vector α n} {i : ℕ} (hp : i < n): (vs.snoc v)[i]'(by linarith) = vs[i]'hp := by
  induction n generalizing i with
  | zero => cases vs using Vector.casesOn; contradiction
  | succ n ih =>
    cases vs using Vector.casesOn;
    cases i with
    | zero => simp
    | succ i => simp [ih (Nat.lt_of_succ_lt_succ hp)]


def permute (fn : Fin m → Fin n) (v : Vector α n): Vector α m :=
  Vector.ofFn (fun i => v[fn i])

theorem permute_inj {n : Nat} {fn : Fin m → Fin n} (perm_surj : Function.Surjective fn): Function.Injective (permute (α := α) fn) := by
  intro v₁ v₂ h
  ext i
  rcases perm_surj i with ⟨j, i_inv⟩
  have : (permute fn v₁).get j = (permute fn v₂).get j := by rw [h]
  simp [permute, GetElem.getElem] at this
  subst_vars
  assumption

theorem map_permute {p : Fin m → Fin n} {f : α → β} {v : Vector α n}:
  Vector.map f (permute p v) = permute p (v.map f) := by
  simp [permute]

end Vector
