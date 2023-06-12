import Mathlib
import ProvenZk.Vect

inductive Dir : Type
| left : Dir
| right : Dir

namespace Dir

def swap : Dir -> Dir
| left => right
| right => left

end Dir

structure Hash (F: Type) :=
  hash : F -> F -> F
  perfect_hash : (a : F) -> (b : F) -> (c : F) -> (d : F) -> (hash a b = hash c d) -> (a = c) ∧ (b = d)

inductive MerkleTree (F: Type) (H : Hash F) : Nat -> Type
| leaf : F  -> MerkleTree F H 0
| bin : MerkleTree F H depth -> MerkleTree F H depth -> MerkleTree F H (depth+1)

namespace MerkleTree

def eq (a b : Nat) := a == b

def left {depth : Nat} {F: Type} {H: Hash F} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin l _ => l

def right {depth : Nat} {F: Type} {H: Hash F} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin _ r => r

def tree_for {depth : Nat} {F: Type} {H: Hash F} (t : MerkleTree F H (Nat.succ depth)) (dir : Dir) : MerkleTree F H depth := match dir with
| Dir.left => t.left
| Dir.right => t.right

def root {depth : Nat} {F: Type} {H: Hash F} (t : MerkleTree F H depth) : F  := match t with
| leaf f => f
| bin l r => H.hash (root l) (root r)

def item_at {depth : Nat} {F: Type} {H: Hash F} (t : MerkleTree F H depth) (p : Vect Dir depth) : F := match depth with
  | Nat.zero => match t with 
    | leaf f => f
  | Nat.succ _ => (t.tree_for p.head).item_at p.tail

def proof {depth : Nat} {F: Type} {H: Hash F} (t : MerkleTree F H depth) (p : Vect Dir depth) : Vect F depth := match depth with
  | Nat.zero => Vect.nil
  | Nat.succ _ => Vect.cons (t.tree_for p.head.swap).root ((t.tree_for p.head).proof p.tail)

def recover {depth : Nat} {F: Type} (H : Hash F) (ix : Vect Dir depth) (proof : Vect F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let proof' := proof.tail
    match ix.head with
      | Dir.left => H.hash (recover H ix.tail proof' item) pitem
      | Dir.right => H.hash pitem (recover H ix.tail proof' item)

def recover_rev {depth F} (H: Hash F) (ix : Vect Dir depth) (proof : Vect F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let next := match ix.head with
      | Dir.left => H.hash item proof.head 
      | Dir.right => H.hash proof.head item
    recover_rev H ix.tail proof.tail next

lemma recover_rev_snoc 
  {depth F} 
  (H: Hash F)
  (ix : Vect Dir depth)
  (dir : Dir)
  (proof : Vect F depth)
  (pitem : F)
  (item : F):
  recover_rev H (ix.snoc dir) (proof.snoc pitem) item = match dir with
    | Dir.left => H.hash (recover_rev H ix proof item) pitem
    | Dir.right => H.hash pitem (recover_rev H ix proof item) := by
  induction depth generalizing dir pitem item with
  | zero =>
    cases ix; cases proof;
    rfl
  | succ _ ih =>
    conv => 
      lhs
      rw [recover_rev, Vect.head_of_snoc, Vect.head_of_snoc, Vect.tail_of_snoc, Vect.tail_of_snoc, ih]

theorem recover_rev_sound
  {F depth}
  (H : Hash F)
  (ix : Vect Dir depth)
  (proof : Vect F depth)
  (item : F) :
  recover_rev H ix.reverse proof.reverse item = recover H ix proof item := by
  induction depth with
  | zero => rfl
  | succ _ ih =>
    cases ix; rename_i dir ix;
    cases proof; rename_i pitem proof;
    cases dir <;> {
      simp [recover, Vect.reverse]
      rw [recover_rev_snoc, ih]
    }

theorem recover_proof_is_root
  {F depth}
  (H : Hash F)
  (ix : Vect Dir depth)
  (tree : MerkleTree F H depth):
  recover H ix (tree.proof ix) (tree.item_at ix) = tree.root := by
  induction depth with
  | zero =>
    cases tree
    simp [recover, proof, item_at, root]
  | succ _ ih =>
    cases ix; rename_i dir ix;
    cases tree; rename_i l r;
    cases dir <;> {
      simp [recover, Vect.head, proof, Vect.tail, tree_for, Dir.swap, right, left, root, item_at]
      rw [ih]
    }

def set { depth : Nat } {F: Type} {H : Hash F} (tree : MerkleTree F H depth) (ix : Vect Dir depth) (item : F) : MerkleTree F H depth := match depth with
  | Nat.zero => leaf item
  | Nat.succ _ => match ix.head with
    | Dir.left => bin (set tree.left ix.tail item) tree.right
    | Dir.right => bin tree.left (set tree.right ix.tail item)

theorem read_after_insert_sound {depth : Nat} {F: Type} {H: Hash F} (tree : MerkleTree F H depth) (ix : Vect Dir depth) (new : F) :
  (tree.set ix new).item_at ix = new := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases tree
    simp [set]
    split <;> simp [item_at, tree_for, left, right, *]

theorem proof_ceritfies_item {depth : Nat} {F: Type} {H: Hash F} (ix : Vect Dir depth) (tree : MerkleTree F H depth) (proof : Vect F depth) (item : F) :
  recover H ix proof item = tree.root → tree.item_at ix = item := by
  intro h
  induction depth with
  | zero =>
    cases tree
    simp [recover, root] at h
    simp [item_at]
    rw [h]
  | succ depth ih =>
    cases tree
    simp [item_at, tree_for, left, right]
    split <;> {
      simp [recover, root, *] at h
      cases H.perfect_hash _ _ _ _ h
      apply ih
      assumption
    }

theorem proof_insert_invariant {depth : Nat} {F: Type} {H: Hash F} (ix : Vect Dir depth) (tree : MerkleTree F H depth) (old new : F) (proof : Vect F depth) :
  recover H ix proof old = tree.root → recover H ix proof new = (tree.set ix new).root := by
  intro h
  induction depth with
  | zero => rfl
  | succ _ ih =>
    cases tree
    simp [set]
    split <;> {
      simp [root, recover, *] at h
      cases H.perfect_hash _ _ _ _ h
      simp [left, right, root, recover, *]
      congr
      apply ih
      assumption
    }


end MerkleTree