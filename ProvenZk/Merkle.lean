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

def itemAtFin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)): F :=
  MerkleTree.itemAt Tree i.toBitsBE

instance : GetElem (MerkleTree α H d) Nat α (fun _ i => i < 2^d) where
  getElem tree ix inb := tree.itemAtFin ⟨ix, inb⟩

def proof {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Bool depth) : Vector F depth := match depth with
  | Nat.zero => Vector.nil
  | Nat.succ _ => Vector.cons (t.treeFor !p.head).root ((t.treeFor p.head).proof p.tail)

def proofAtFin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)): Vector F d :=
  MerkleTree.proof Tree i.toBitsBE

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

def recoverAtFin {depth : Nat} {F: Type} (H : Hash F 2) (ix : Fin (2^depth)) (proof : Vector F depth) (item : F) : F :=
  recover H ix.toBitsBE proof item

def set { depth : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Bool depth) (item : F) : MerkleTree F H depth := match depth with
  | Nat.zero => leaf item
  | Nat.succ _ => match ix.head with
    | false => bin (set tree.left ix.tail item) tree.right
    | true => bin tree.left (set tree.right ix.tail item)

def setAtFin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)) (Item : F): MerkleTree F H d :=
  MerkleTree.set Tree i.toBitsBE Item

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

theorem itemAtFin_setAtFin_invariant_of_neq {tree : MerkleTree α H depth} {ix₁ ix₂ : Fin (2 ^ depth)} (hneq : ix₁ ≠ ix₂):
  (tree.setAtFin ix₂ item).itemAtFin ix₁ = tree.itemAtFin ix₁ := by
  apply itemAt_set_invariant_of_neq
  intro h
  rw [Fin.toBitsBE_injective, eq_comm] at h
  contradiction

@[simp]
theorem itemAt_set_eq_self { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {ix : Vector Bool depth} {item : F}:
  itemAt (set tree ix item) ix = item := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases ix using Vector.casesOn
    cases tree
    simp [set, itemAt, treeFor, left, right, *]
    split <;> simp [ih]

@[simp]
theorem itemAtFin_setAtFin_eq_self {F: Type} {H : Hash F 2} {tree : MerkleTree F H d} {ix : Fin (2^d)} {item : F}:
  (tree.setAtFin ix item).itemAtFin ix = item := itemAt_set_eq_self

@[simp]
theorem recover_eq_root_iff_proof_and_item_correct { depth : Nat } {F: Type} {H : Hash F 2} [Fact (CollisionResistant H)] {tree : MerkleTree F H depth} {ix : Vector Bool depth} {proof : Vector F depth} {item : F}:
  recover H ix proof item = tree.root ↔ proof = tree.proof ix ∧ item = tree.itemAt ix := by
  induction depth with
  | zero =>
    cases tree
    cases ix using Vector.casesOn
    cases proof using Vector.casesOn
    simp [recover, root, itemAt]
  | succ n ih =>
    cases tree
    cases proof using Vector.casesOn
    cases ix using Vector.casesOn; rename_i hix _
    cases hix <;> {
      simp [recover, proof, root, treeFor, left, right, ih, Vector.eq_cons_iff]
      tauto
    }

@[simp]
theorem recoverAtFin_eq_root_iff_proof_and_item_correct {F: Type} {H : Hash F 2} [Fact (CollisionResistant H)] {tree : MerkleTree F H d} {ix : Fin (2^d)} {proof : Vector F d} {item : F}:
  recoverAtFin H ix proof item = tree.root ↔ proof = tree.proofAtFin ix ∧ item = tree.itemAtFin ix := by
  simp [recoverAtFin, proofAtFin, itemAtFin]

@[simp]
theorem proof_set_eq_proof { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {ix : Vector Bool depth} {item : F}:
  (set tree ix item).proof ix = tree.proof ix := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases ix using Vector.casesOn; rename_i hix _
    cases hix <;> {
      simp [set, proof, treeFor, left, right, root, ih]
    }

@[simp]
theorem proofAtFin_setAtFin_eq_proof {F: Type} {H : Hash F 2} {tree : MerkleTree F H d} {ix : Fin (2^d)} {item : F}:
    (tree.setAtFin ix item).proofAtFin ix = tree.proofAtFin ix := proof_set_eq_proof

theorem root_set_eq_recover { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {ix : Vector Bool depth} {item : F}:
  (set tree ix item).root = recover H ix (tree.proof ix) item := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases tree
    cases ix using Vector.casesOn; rename_i hix _
    cases hix <;> {
      simp [set, proof, treeFor, left, right, root, ih, recover]
    }

theorem root_setAtFin_eq_recoverAtFin {F: Type} {H : Hash F 2} {tree : MerkleTree F H d} {ix : Fin (2^d)} {item : F}:
  (tree.setAtFin ix item).root = recoverAtFin H ix (tree.proofAtFin ix) item := by
  simp [root_set_eq_recover, recoverAtFin, proofAtFin, setAtFin]

end MerkleTree
