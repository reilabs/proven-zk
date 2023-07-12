import ProvenZk.VectorExtensions
import ProvenZk.Hash

inductive Dir : Type
| left : Dir
| right : Dir

namespace Dir

def swap : Dir -> Dir
| left => right
| right => left

instance : Inhabited Dir where
  default := left

end Dir

inductive MerkleTree (F: Type) (H : Hash F 2) : Nat -> Type
| leaf : F  -> MerkleTree F H 0
| bin : MerkleTree F H depth -> MerkleTree F H depth -> MerkleTree F H (depth+1)

namespace MerkleTree

def eq (a b : Nat) := a == b

def left {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin l _ => l

def right {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin _ r => r

def tree_for {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) (dir : Dir) : MerkleTree F H depth := match dir with
| Dir.left => t.left
| Dir.right => t.right

def root {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) : F  := match t with
| leaf f => f
| bin l r => H vec![root l, root r]

def item_at {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Dir depth) : F := match depth with
  | Nat.zero => match t with
    | leaf f => f
  | Nat.succ _ => (t.tree_for p.head).item_at p.tail

def proof {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Dir depth) : Vector F depth := match depth with
  | Nat.zero => Vector.nil
  | Nat.succ _ => Vector.cons (t.tree_for p.head.swap).root ((t.tree_for p.head).proof p.tail)

def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : Vector Dir depth) (proof : Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let proof' := proof.tail
    match ix.head with
      | Dir.left => H vec![recover H ix.tail proof' item, pitem]
      | Dir.right => H vec![pitem, recover H ix.tail proof' item]

def recover_tail {depth F} (H: Hash F 2) (ix : Vector Dir depth) (proof : Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let next := match ix.head with
      | Dir.left => H vec![item, proof.head]
      | Dir.right => H vec![proof.head, item]
    recover_tail H ix.tail proof.tail next

lemma recover_tail_snoc
  {depth F}
  (H: Hash F 2)
  (ix : Vector Dir depth)
  (dir : Dir)
  (proof : Vector F depth)
  (pitem : F)
  (item : F):
  recover_tail H (ix.snoc dir) (proof.snoc pitem) item = match dir with
    | Dir.left => H vec![recover_tail H ix proof item, pitem]
    | Dir.right => H vec![pitem, recover_tail H ix proof item] := by
  induction depth generalizing dir pitem item with
  | zero => simp [Vector.eq_nil, recover_tail]
  | succ _ ih =>
      conv =>
        lhs
        rw [recover_tail, Vector.head_snoc, Vector.head_snoc, Vector.tail_snoc, Vector.tail_snoc, ih]

theorem recover_tail_reverse
  {F depth}
  (H : Hash F 2)
  (ix : Vector Dir depth)
  (proof : Vector F depth)
  (item : F) :
  recover_tail H ix.reverse proof.reverse item = recover H ix proof item := by
  induction depth with
  | zero => rfl
  | succ _ ih =>
    rw [←ix.cons_head_tail,
        ←proof.cons_head_tail,
        Vector.reverse_cons_snoc,
        Vector.reverse_cons_snoc,
        recover_tail_snoc]
    unfold recover
    split <;> simp [*]

theorem recover_proof_is_root
  {F depth}
  (H : Hash F 2)
  (ix : Vector Dir depth)
  (tree : MerkleTree F H depth):
  recover H ix (tree.proof ix) (tree.item_at ix) = tree.root := by
  induction depth with
  | zero =>
    cases tree
    simp [recover, proof, item_at, root]
  | succ _ ih =>
    cases tree; rename_i l r
    simp [recover]
    split <;> (
      unfold root
      congr <;> simp [*, proof, tree_for, left, right, Dir.swap, item_at, ih]
    )

def set { depth : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Dir depth) (item : F) : MerkleTree F H depth := match depth with
  | Nat.zero => leaf item
  | Nat.succ _ => match ix.head with
    | Dir.left => bin (set tree.left ix.tail item) tree.right
    | Dir.right => bin tree.left (set tree.right ix.tail item)

theorem read_after_insert_sound {depth : Nat} {F: Type} {H: Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Dir depth) (new : F) :
  (tree.set ix new).item_at ix = new := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases tree
    simp [set]
    split <;> simp [item_at, tree_for, left, right, *]

theorem proof_ceritfies_item
  {depth : Nat}
  {F: Type}
  {H: Hash F 2}
  [Fact (perfect_hash H)]
  (ix : Vector Dir depth)
  (tree : MerkleTree F H depth)
  (proof : Vector F depth)
  (item : F)
  :
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
      have inps_same := Vector.elems_eq (Fact.elim (inferInstance : Fact (perfect_hash H)) h)
      simp at inps_same
      cases inps_same
      apply ih
      assumption
    }

theorem proof_insert_invariant
  {depth : Nat}
  {F: Type}
  {H: Hash F 2}
  [Fact (perfect_hash H)]
  (ix : Vector Dir depth)
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
      simp [root, recover, *] at h
      have inps_same := Vector.elems_eq (Fact.elim (inferInstance : Fact (perfect_hash H)) h)
      simp at inps_same
      cases inps_same
      simp [left, right, root, recover, *]
      congr
      apply ih
      assumption
    }


end MerkleTree