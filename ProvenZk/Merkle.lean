import ProvenZk.VectorExtensions
import ProvenZk.Hash

inductive Dir : Type
| left : Dir
| right : Dir
deriving Repr

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
deriving Repr

namespace MerkleTree

def eq (a b : Nat) := a == b

def left {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin l _ => l

def right {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin _ r => r

-- Return left/right subtree
def tree_for {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) (dir : Dir) : MerkleTree F H depth := match dir with
| Dir.left => t.left
| Dir.right => t.right

-- Recursively walk the tree and return the root
def root {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) : F := match t with
| leaf f => f
| bin l r => H vec![root l, root r]

-- Walk the tree using path Vector and return leaf
def item_at {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Dir depth) : F := match depth with
  | Nat.zero => match t with
    | leaf f => f
  | Nat.succ _ => (t.tree_for p.head).item_at p.tail

-- Walk the tree using path Vector and return list of Hashes along the path
def proof {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Dir depth) : Vector F depth := match depth with
  | Nat.zero => Vector.nil
  | Nat.succ _ => Vector.cons (t.tree_for p.head.swap).root ((t.tree_for p.head).proof p.tail)

-- Recover the Merkle tree from partial hashes. From bottom to top. It returns the item at the top (i.e. root)
def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : Vector Dir depth) (proof : Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let recover' := recover H ix.tail proof.tail item
    match ix.head with
      | Dir.left => H vec![recover', pitem]
      | Dir.right => H vec![pitem, recover']

-- Recover the Merkle tree from partial hashes. From top to bottom. It returns the item at the bottom (i.e. leaf)
def recover_tail {depth : Nat} {F: Type} (H: Hash F 2) (ix : Vector Dir depth) (proof : Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let next := match ix.head with
      | Dir.left => H vec![item, pitem]
      | Dir.right => H vec![pitem, item]
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

-- recover_tail on reverse Vectors is equal to recover
theorem recover_tail_reverse_equals_recover
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

-- recover on Merke Tree returns root
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

lemma recover_tail_reverse_is_root
  {F depth}
  (H : Hash F 2)
  (ix : Vector Dir depth)
  (tree : MerkleTree F H depth) :
  recover_tail H ix.reverse (tree.proof ix).reverse (tree.item_at ix) = tree.root := by
  sorry

-- Set item in the tree at position ix
def set { depth : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Dir depth) (item : F) : MerkleTree F H depth := match depth with
  | Nat.zero => leaf item
  | Nat.succ _ => match ix.head with
    | Dir.left => bin (set tree.left ix.tail item) tree.right
    | Dir.right => bin tree.left (set tree.right ix.tail item)

-- Check set function changes the tree
theorem read_after_insert_sound {depth : Nat} {F: Type} {H: Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Dir depth) (new : F) :
  (tree.set ix new).item_at ix = new := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases tree
    simp [set]
    split <;> simp [item_at, tree_for, left, right, *]

-- Related to recover_proof_is_root
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

lemma proof_ceritfies_item'
  {depth : Nat}
  {F: Type}
  {H: Hash F 2}
  [Fact (perfect_hash H)]
  (ix : Vector Dir depth)
  (tree : MerkleTree F H depth)
  (proof : Vector F depth)
  (item : F)
  :
  tree.root = recover H ix proof item → tree.item_at ix = item := by
  sorry

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