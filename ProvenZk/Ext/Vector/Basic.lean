import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Vector.Mem
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.Defs

import ProvenZk.Ext.Fin
import ProvenZk.Ext.List

namespace List.Vector

@[simp]
theorem set_cons_0 {α n} (v : Vector α n) (x y: α):
  (cons y v).set 0 x = cons x v := by
  apply Vector.eq
  simp

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
  | `(vec![]) => ``(nil)
  | `(vec![$x]) => ``(cons $x nil)
  | `(vec![$x, $xs:term,*]) => ``(cons $x (vec![$xs,*]))

def to_column (v : Vector α n) : Matrix (Fin n) Unit α := Matrix.of (fun i _ => v.get i)

theorem eq_cons : (x ::ᵥ xs) = (y ::ᵥ ys) ↔ x = y ∧ xs = ys := by
  simp [Vector.eq_cons_iff]

theorem reverse_eq {x y : Vector α n} : (x.reverse = y) ↔ (x = y.reverse) := by
  apply Iff.intro
  case mp =>
    intro
    subst_vars
    simp
  case mpr =>
    intro
    subst_vars
    simp

theorem replicate_succ_snoc : Vector.replicate (Nat.succ n) a = (Vector.replicate n a).snoc a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Vector.replicate_succ, ih, ←Vector.snoc_cons]
    congr

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
    | zero => cases vs using Vector.casesOn with | cons hd tl => simp
    | succ i => cases i using finZeroElim
  | succ n ih =>
    cases vs using Vector.casesOn with | cons hd tl =>
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [Fin.castSucc_succ_eq_succ_castSucc, ih]

theorem get_val_getElem {v : Vector α n} {i : Fin n}: v[i.val]'(i.prop) = v.get i := by
  rfl

theorem getElem_def' {v : Vector α n} {i : Nat} {prop}: v[i]'prop = v.get ⟨i, prop⟩ := by
  rfl

@[simp]
lemma get_snoc_fin_prev {vs : Vector α n} {v : α} {i : Fin n}:
  (vs.snoc v)[i.val]'(by (have := i.prop); linarith) = vs[i.val]'(i.prop) := by
  simp [get_val_getElem, getElem_def', Fin.castSucc_def]

theorem ofFn_snoc' { fn : Fin (Nat.succ n) → α }:
  Vector.ofFn fn = Vector.snoc (Vector.ofFn (fun (x : Fin n) => fn (Fin.castSucc x))) (fn n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    conv => lhs; rw [Vector.ofFn, ih]
    simp [Vector.ofFn]
    congr

instance : Membership α (Vector α n) := ⟨fun xs x => x ∈ xs.toList⟩

@[simp]
theorem mem_def {xs : Vector α n} {x} : x ∈ xs ↔ x ∈ xs.toList := by rfl

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

theorem exists_succ_iff_exists_snoc {α d} {pred : Vector α (Nat.succ d) → Prop}:
  (∃v, pred v) ↔ ∃vs v, pred (Vector.snoc vs v) := by
  apply Iff.intro
  . rintro ⟨v, hp⟩
    cases v using Vector.revCasesOn
    apply Exists.intro
    apply Exists.intro
    assumption
  . rintro ⟨vs, v, hp⟩
    exists vs.snoc v

theorem exists_succ_iff_exists_cons {α d} {pred : Vector α (Nat.succ d) → Prop}:
  (∃v, pred v) ↔ ∃v vs, pred (v ::ᵥ vs) := by
  apply Iff.intro
  . rintro ⟨v, hp⟩
    cases v using Vector.casesOn
    apply Exists.intro
    apply Exists.intro
    assumption
  . rintro ⟨v, vs, hp⟩
    exists (v ::ᵥ vs)

@[simp]
theorem snoc_eq : Vector.snoc xs x = Vector.snoc ys y ↔ xs = ys ∧ x = y := by
  apply Iff.intro
  . intro h
    have := congrArg Vector.reverse h
    simp at this
    injection this with this
    injection this with h t
    simp [*]
    apply Vector.eq
    have := congrArg List.reverse t
    simp_all
  . intro ⟨_, _⟩
    simp [*]

end Vector
