import Mathlib.Data.Vector.MapLemmas

import ProvenZk.Ext.Vector
import ProvenZk.Hash
import ProvenZk.Binary

inductive MerkleTree (F: Type) (H : Hash F 2) : Nat -> Type
| leaf : F  -> MerkleTree F H 0
| bin : MerkleTree F H depth -> MerkleTree F H depth -> MerkleTree F H (depth+1)
deriving Repr

namespace MerkleTree

def left {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin l _ => l

def right {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin _ r => r

def treeFor {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) (dir : Bool) : MerkleTree F H depth := match dir with
| false => t.left
| true => t.right

def root {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) : F := match t with
| leaf f => f
| bin l r => H vec![root l, root r]

def itemAt {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Bool depth) : F := match depth with
  | Nat.zero => match t with
    | leaf f => f
  | Nat.succ _ => (t.treeFor p.head).itemAt p.tail

-- def itemAtNat {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) : Option F := do
--   t.itemAt <$> Dir.nat_to_dir_vec idx depth

def itemAtFin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)): F :=
  MerkleTree.itemAt Tree i.toBitsBE

instance : GetElem (MerkleTree α H d) Nat α (fun _ i => i < 2^d) where
  getElem tree ix inb := tree.itemAtFin ⟨ix, inb⟩

def proof {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Bool depth) : Vector F depth := match depth with
  | Nat.zero => Vector.nil
  | Nat.succ _ => Vector.cons (t.treeFor !p.head).root ((t.treeFor p.head).proof p.tail)

-- def proof_at_nat (t : MerkleTree F H depth) (idx: Nat): Option (Vector F depth) :=
--   t.proof <$> Dir.nat_to_dir_vec idx depth

-- def tree_proof_at_fin_dropLast {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^(d+1))): Vector F d :=
--   MerkleTree.proof Tree (Dir.fin_to_dir_vec i).dropLast.reverse

def proofAtFin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)): Vector F d :=
  MerkleTree.proof Tree i.toBitsBE

-- lemma proof_at_nat_to_fin {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
--   MerkleTree.proof_at_nat t idx = some (MerkleTree.proofAtFin t idx) := by
--   simp [MerkleTree.proof_at_nat, MerkleTree.proofAtFin]
--   simp [Dir.nat_to_dir_vec, Dir.fin_to_dir_vec]
--   simp [fin_to_bits_le_is_some h]

-- lemma proof_at_nat_to_fin_some {depth : Nat} {F: Type} {H: Hash F 2} {a : Vector F depth} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
--   MerkleTree.proof_at_nat t idx = some a ↔
--   MerkleTree.proofAtFin t idx = a := by
--   rw [proof_at_nat_to_fin (h := h)]
--   . simp

def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : Vector Bool depth) (proof : Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let recover' := recover H ix.tail proof.tail item
    match ix.head with
    | false => H vec![recover', pitem]
    | true => H vec![pitem, recover']

lemma recover_snoc {H : Hash α 2} {item : α} {ps : Vector Bool n} {p : Bool} {ss : Vector α n} {s : α}:
  recover H (ps.snoc p) (ss.snoc s) item = recover H ps ss (
    match p with
    | false => H vec![item, s]
    | true => H vec![s, item]
  ) := by
  induction ps, ss using Vector.inductionOn₂ generalizing item s with
  | nil => rfl
  | @cons n p s ps ss ih =>
    unfold recover
    cases p <;> simp [*]

theorem eq_recover_iff_eq_item {depth : Nat} {F: Type} {H : Hash F 2}
  {ix : Vector Bool depth} {proof : Vector F depth} {item₁ : F} {item₂ : F}
  [Fact (CollisionResistant H)]:
  recover H ix proof item₁ = recover H ix proof item₂ ↔ item₁ = item₂ := by
  apply Iff.intro
  case mp =>
    induction depth with
    | zero => simp [recover]
    | succ _ ih =>
      intro h
      unfold recover at h
      split at h <;> {
              simp at h
              have := congrArg Vector.head h
              have := congrArg (Vector.head ∘ Vector.tail) h
              apply ih
              assumption
      }
  case mpr =>
    intro h
    rw [h]

-- def recover_tail {depth : Nat} {F: Type} (H: Hash F 2) (ix : Vector Bool depth) (proof : Vector F depth) (item : F) : F := match depth with
--   | Nat.zero => item
--   | Nat.succ _ =>
--     let pitem := proof.head
--     let next := match ix.head with
--       | false => H vec![item, pitem]
--       | true => H vec![pitem, item]
--     recover_tail H ix.tail proof.tail next

-- lemma recover_tail_snoc
--   {depth F}
--   (H: Hash F 2)
--   (ix : Vector Bool depth)
--   (dir : Bool)
--   (proof : Vector F depth)
--   (pitem : F)
--   (item : F):
--   recover_tail H (ix.snoc dir) (proof.snoc pitem) item = match dir with
--     | false => H vec![recover_tail H ix proof item, pitem]
--     | true => H vec![pitem, recover_tail H ix proof item] := by
--   induction depth generalizing dir pitem item with
--   | zero => simp [Vector.eq_nil, recover_tail]
--   | succ _ ih =>
--       conv =>
--         lhs
--         rw [recover_tail, Vector.head_snoc, Vector.head_snoc, Vector.tail_snoc, Vector.tail_snoc, ih]

-- theorem recover_tail_reverse_equals_recover
--   {F depth}
--   (H : Hash F 2)
--   (ix : Vector Bool depth)
--   (proof : Vector F depth)
--   (item : F) :
--   recover_tail H ix.reverse proof.reverse item = recover H ix proof item := by
--   induction depth with
--   | zero => rfl
--   | succ _ ih =>
--     rw [←ix.cons_head_tail,
--         ←proof.cons_head_tail,
--         Vector.reverse_cons,
--         Vector.reverse_cons,
--         recover_tail_snoc]
--     unfold recover
--     split <;> simp [*]

-- theorem recover_tail_equals_recover_reverse
--   {F depth}
--   (H : Hash F 2)
--   (ix : Vector Bool depth)
--   (proof : Vector F depth)
--   (item : F) :
--   recover_tail H ix proof item = recover H ix.reverse proof.reverse item := by
--   have : ix = ix.reverse.reverse:= by simp
--   rw [this]
--   have : proof = proof.reverse.reverse := by simp
--   rw [this]
--   rw [recover_tail_reverse_equals_recover]
--   simp

theorem recover_proof_is_root
  {F depth}
  (H : Hash F 2)
  (ix : Vector Bool depth)
  (tree : MerkleTree F H depth):
  recover H ix (tree.proof ix) (tree.itemAt ix) = tree.root := by
  induction depth with
  | zero =>
    cases tree
    simp [recover, proof, itemAt, root]
  | succ _ ih =>
    cases tree; rename_i l r
    simp [recover]
    split <;> (
      unfold root
      congr <;> simp [*, proof, treeFor, left, right, itemAt, ih]
    )

def set { depth : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Bool depth) (item : F) : MerkleTree F H depth := match depth with
  | Nat.zero => leaf item
  | Nat.succ _ => match ix.head with
    | false => bin (set tree.left ix.tail item) tree.right
    | true => bin tree.left (set tree.right ix.tail item)

-- def set_at_nat(t : MerkleTree F H depth) (idx: Nat) (newVal: F): Option (MerkleTree F H depth) :=
--   (t.set · newVal) <$> Dir.nat_to_dir_vec idx depth

def setAtFin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)) (Item : F): MerkleTree F H d :=
  MerkleTree.set Tree i.toBitsBE Item

-- lemma set_at_nat_to_fin {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) (item : F) (h : idx < 2 ^ depth):
--   MerkleTree.set_at_nat t idx item = some (MerkleTree.setAtFin t idx item) := by
--   simp [MerkleTree.set_at_nat, MerkleTree.setAtFin]
--   simp [Dir.nat_to_dir_vec]
--   simp [Dir.fin_to_dir_vec]
--   simp [fin_to_bits_le_is_some h]

-- lemma set_at_nat_to_fin_some {depth : Nat} {F: Type} {H: Hash F 2} {a : MerkleTree F H depth} (t : MerkleTree F H depth) (idx : Nat) (item : F) (h : idx < 2 ^ depth):
--   MerkleTree.set_at_nat t idx item = some a ↔
--   MerkleTree.setAtFin t idx item = a := by
--   rw [set_at_nat_to_fin (h := h)]
--   . simp

-- lemma item_at_nat_to_fin {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
--   MerkleTree.itemAtNat t idx = some (MerkleTree.itemAtFin t idx) := by
--   simp [MerkleTree.itemAtNat, MerkleTree.itemAtFin]
--   simp [Dir.nat_to_dir_vec, Dir.fin_to_dir_vec]
--   simp [fin_to_bits_le_is_some h]

-- lemma item_at_nat_to_fin_some {depth : Nat} {F: Type} {H: Hash F 2} {a : F} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
--   MerkleTree.itemAtNat t idx = some a ↔
--   MerkleTree.itemAtFin t idx = a := by
--   rw [item_at_nat_to_fin (h := h)]
--   . simp

theorem itemAt_set_invariant_of_neq { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {ix₁ ix₂ : Vector Bool depth} {item₁ : F} {neq : ix₁ ≠ ix₂}:
  itemAt (set tree ix₁ item₁) ix₂ = itemAt tree ix₂ := by
  induction depth with
  | zero =>
    cases ix₁ using Vector.casesOn
    cases ix₂ using Vector.casesOn
    cases (neq rfl)
  | succ depth ih =>
    cases ix₁ using Vector.casesOn; rename_i ix₁_hd ix₁_tl
    cases ix₂ using Vector.casesOn; rename_i ix₂_hd ix₂_tl
    cases tree; rename_i tree_l tree_r
    simp [itemAt, set, treeFor, set, left, right]
    simp [Vector.eq_cons] at neq
    cases ix₁_hd <;> { cases ix₂_hd <;> { simp [ih, neq] } }

-- theorem item_at_nat_invariant {H : Hash α 2} {tree tree': MerkleTree α H depth} { neq : ix₁ ≠ ix₂ }:
--   set_at_nat tree ix₁ item₁ = some tree' →
--   itemAtNat tree' ix₂ = itemAtNat tree ix₂ := by
--   simp [set_at_nat, itemAtNat]
--   intros; subst_vars
--   cases h : Dir.nat_to_dir_vec ix₂ depth with
--   | none => rfl
--   | some ix =>
--     simp
--     rw [item_at_invariant]
--     intro hp
--     refine (neq ?_)
--     apply Dir.nat_to_dir_vec_unique <;> assumption

-- theorem item_at_fin_invariant {H : Hash α 2} {tree tree': MerkleTree α H depth} { neq : ix₁ ≠ ix₂ } {h₁ : ix₁ < 2 ^ depth} {h₂ : ix₂ < 2 ^ depth}:
--   MerkleTree.setAtFin tree ix₁ item₁ = tree' →
--   MerkleTree.itemAtFin tree' ix₂ = MerkleTree.itemAtFin tree ix₂ := by
--   rw [<-set_at_nat_to_fin_some (h := h₁)]
--   rw [<-item_at_nat_to_fin_some (h := h₂)]
--   rw [<-item_at_nat_to_fin (h := h₂)]
--   apply MerkleTree.item_at_nat_invariant (neq := neq)

theorem getElem_setAtFin_invariant_of_neq {tree : MerkleTree α H depth} {ix₁ : Nat} {hix₁ : ix₁ < 2 ^ depth} {ix₂ : Fin (2 ^ depth)} (hneq : ix₁ ≠ ix₂.val):
  (tree.setAtFin ix₂ item)[ix₁]'hix₁ = tree[ix₁]'hix₁ := by
  unfold setAtFin
  simp [setAtFin, getElem, itemAtFin]
  apply itemAt_set_invariant_of_neq
  simp [ne_comm, Fin.eq_iff_veq, *]

@[simp]
theorem read_after_insert_sound {depth : Nat} {F: Type} {H: Hash F 2} {tree : MerkleTree F H depth} {ix : Vector Bool depth} {new : F} :
  (tree.set ix new).itemAt ix = new := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases tree
    simp [set]
    split <;> simp [itemAt, treeFor, left, right, *]

-- lemma set_implies_item_at { depth : Nat } {F: Type} {H : Hash F 2} {t₁ t₂ : MerkleTree F H depth} {ix : Vector Bool depth} {item : F} :
--   set t₁ ix item = t₂ → itemAt t₂ ix = item := by
--   intro h
--   rw [<-h]
--   apply read_after_insert_sound

theorem proof_ceritfies_item
  {depth : Nat}
  {F: Type}
  {H: Hash F 2}
  [Fact (CollisionResistant H)]
  {ix : Vector Bool depth}
  {tree : MerkleTree F H depth}
  {proof : Vector F depth}
  {item : F}:
  recover H ix proof item = tree.root → tree.itemAt ix = item := by
  intro h
  induction depth with
  | zero =>
    cases tree
    simp [recover, root] at h
    simp [itemAt]
    rw [h]
  | succ depth ih =>
    cases tree
    simp [itemAt, treeFor, left, right]
    split <;> {
      simp [recover, root, *, Vector.eq_cons_iff] at h
      cases h
      apply ih (proof := proof.tail)
      assumption
    }

theorem proof_insert_invariant
  {depth : Nat}
  {F: Type}
  {H: Hash F 2}
  [Fact (CollisionResistant H)]
  (ix : Vector Bool depth)
  (tree : MerkleTree F H depth)
  (old new : F)
  (proof : Vector F depth)
  :
  recover H ix proof old = tree.root → recover H ix proof new = (tree.set ix new).root := by
  intro h
  induction depth with
  | zero => rfl
  | succ _ ih =>
    cases tree
    simp [set]
    split <;> {
      simp [root, recover, *, Vector.eq_cons_iff] at h
      simp [left, right, root, recover, *]
      congr
      apply ih
      simp [*]
    }

theorem recover_proof_reversible {H : Hash α 2} [Fact (CollisionResistant H)] {Tree : MerkleTree α H d} {Proof : Vector α d}:
  recover H Index Proof Item = Tree.root →
  Tree.proof Index = Proof := by
  induction d with
  | zero =>
    cases Proof using Vector.casesOn
    simp [proof]
  | succ d ih =>
    cases Proof using Vector.casesOn
    cases Index using Vector.casesOn
    cases Tree
    simp [root, recover, proof]
    intro h
    split at h <;> {
      have : CollisionResistant H := (inferInstance : Fact (CollisionResistant H)).out
      have := this h
      rw [Vector.eq_cons, Vector.eq_cons] at this
      casesm* (_ ∧ _)
      subst_vars
      simp [treeFor, left, right]
      congr
      apply ih
      assumption
    }

theorem recover_equivalence
  {F depth}
  (H : Hash F 2)
  [Fact (CollisionResistant H)]
  (tree : MerkleTree F H depth)
  (Path : Vector Bool depth)
  (Proof : Vector F depth)
  (Item : F) :
    (itemAt tree Path = Item ∧ proof tree Path = Proof) ↔
    recover H Path Proof Item = tree.root := by
  apply Iff.intro
  . intros
    casesm* (_ ∧ _)
    rename_i hitem_at hproof
    rw [<-hitem_at]
    rw [<-hproof]
    apply recover_proof_is_root
  . intros
    apply And.intro
    . apply proof_ceritfies_item (proof := Proof)
      assumption
    . apply recover_proof_reversible (Item := Item)
      assumption

theorem eq_root_eq_tree {H} [ph: Fact (CollisionResistant H)] {t₁ t₂ : MerkleTree α H d}:
  t₁.root = t₂.root ↔ t₁ = t₂ := by
  induction d with
  | zero => cases t₁; cases t₂; tauto
  | succ _ ih =>
    cases t₁
    cases t₂
    apply Iff.intro
    . intro h
      have h := Fact.elim ph h
      injection h with h
      injection h with _ h
      injection h
      congr <;> {rw [←ih]; assumption}
    . intro h
      injection h
      subst_vars
      rfl

@[simp]
theorem Bool.eq_true_of_neg_eq_false {b}: !b = false ↔ b = true := by
  cases b <;> simp

@[simp]
theorem Bool.eq_false_of_neg_eq_true {b}: !b = true ↔ b = false := by
  cases b <;> simp

lemma proof_of_set_is_proof
  {F d}
  (H : Hash F 2)
  [Fact (CollisionResistant H)]
  (Tree : MerkleTree F H d)
  (ix : Vector Bool d)
  (item : F):
  (MerkleTree.proof (MerkleTree.set Tree ix item) ix) = MerkleTree.proof Tree ix := by
  induction d with
  | zero =>
    simp [MerkleTree.set, MerkleTree.proof]
  | succ d ih =>
    cases Tree
    simp [MerkleTree.set, MerkleTree.proof, MerkleTree.treeFor]
    split <;> {
      simp [*, MerkleTree.set, MerkleTree.left, MerkleTree.right, Vector.eq_cons] at *
      simp [*]
    }

lemma proof_of_set_fin
  {F d}
  (H : Hash F 2)
  [Fact (CollisionResistant H)]
  (Tree : MerkleTree F H d)
  (ix : Fin (2^d))
  (item : F):
  (proofAtFin (setAtFin Tree ix item) ix) = proofAtFin Tree ix := by
  simp [proofAtFin, setAtFin]
  simp [proof_of_set_is_proof]

-- def multi_set { depth b : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (path : Vector (Vector Dir depth) b) (item : F) : MerkleTree F H depth :=
--   match b with
--   | Nat.zero => tree
--   | Nat.succ _ => multi_set (tree.set path.head item) path.tail item

lemma tree_set_comm  { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {p₁ p₂ : Vector Bool depth} {item : F}:
  MerkleTree.set (MerkleTree.set tree p₁ item) p₂ item = MerkleTree.set (MerkleTree.set tree p₂ item) p₁ item := by
  induction depth with
  | zero => rfl
  | succ d ih => cases tree with | bin l r =>
    cases p₁ using Vector.casesOn with | cons p₁h p₁t =>
    cases p₂ using Vector.casesOn with | cons p₂h p₂t =>
    cases p₁h <;> {
      cases p₂h <;> { simp [MerkleTree.set, MerkleTree.left, MerkleTree.right]; try rw [ih] }
    }

-- lemma multi_set_set { depth b : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {p : Vector Bool depth} {path : Vector (Vector Bool depth) b} {item : F}:
--   multi_set (MerkleTree.set tree p item) path item = MerkleTree.set (multi_set tree path item) p item := by
--   induction path using Vector.inductionOn generalizing tree p with
--   | h_nil => rfl
--   | h_cons ih => simp [multi_set, ih, tree_set_comm]

-- def multi_item_at { depth b : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (path : Vector (Vector Dir depth) b) (item : F) : Prop :=
--   match b with
--   | Nat.zero => true
--   | Nat.succ _ => tree.itemAt path.head = item ∧ multi_item_at tree path.tail item

-- theorem multi_set_is_item_at { depth b : Nat } {F: Type} {H : Hash F 2} {initialTree finalTree: MerkleTree F H depth} {path : Vector (Vector Dir depth) b} {item : F} :
--   (multi_set initialTree path item = finalTree →
--   multi_item_at finalTree path item) := by
--   induction path using Vector.inductionOn generalizing initialTree finalTree with
--   | h_nil =>
--     simp [multi_set, multi_item_at]
--   | @h_cons b' x xs ih =>
--     unfold multi_set
--     unfold multi_item_at
--     simp only [Vector.tail_cons, Vector.head_cons]
--     intro h
--     refine ⟨?_, ?_⟩
--     . rw [←h, multi_set_set, MerkleTree.read_after_insert_sound]
--     . apply ih h

-- theorem multi_set_is_item_at_all_item { depth b i : Nat } {range : i ∈ [0:b]} {F: Type} {H : Hash F 2}
--   {initialTree finalTree: MerkleTree F H depth} {path : Vector (Vector Dir depth) b} {item : F} :
--   multi_set initialTree path item = finalTree →
--   MerkleTree.itemAt finalTree (path[i]'(by rcases range; tauto)) = item := by
--   intro hp
--   induction path using Vector.inductionOn generalizing i initialTree finalTree with
--   | h_nil =>
--     rcases range with ⟨lo, hi⟩
--     have := Nat.ne_of_lt (Nat.lt_of_le_of_lt lo hi)
--     contradiction
--   | @h_cons b' x xs ih =>
--     rcases range with ⟨lo, hi⟩
--     cases lo with
--     | refl =>
--       have hitem_at : multi_item_at finalTree (x ::ᵥ xs) item := multi_set_is_item_at hp
--       unfold multi_item_at at hitem_at
--       tauto
--     | @step i h =>
--       exact ih (by assumption) (range := ⟨zero_le _, Nat.lt_of_succ_lt_succ hi⟩)

end MerkleTree
