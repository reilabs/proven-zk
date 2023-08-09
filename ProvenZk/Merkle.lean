import ProvenZk.Ext.Vector
import ProvenZk.Hash

/-- Dir type is used to walk through a tree Left or Right -/
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

def toNat : Dir -> Nat := fun b => match b with
  | Dir.left => 0
  | Dir.right => 1

def toZMod {n} : Dir -> ZMod n := fun b => match b with
  | Dir.left => 0
  | Dir.right => 1

def toDir : Nat -> Dir
  | 0 => Dir.left
  | 1 => Dir.right
  | Nat.succ (Nat.succ _) => panic "Dir can be 0 or 1"

def toDir_fact (x : Nat) [Fact (x=0 ∨ x=1)] : Dir := match p : x with
  | 0 => Dir.left
  | 1 => Dir.right
  | Nat.succ (Nat.succ n) => False.elim (by
  have : x=0 ∨ x=1 := (inferInstance : Fact (x=0 ∨ x=1)).elim
  induction n generalizing x with
  | zero =>
    cases this
    case _ => {
      rename_i h₁
      subst x
      simp [*] at h₁
    }
    case _ => {
      rename_i h₁
      subst x
      simp [*] at h₁
    }
  | succ _ _ =>
    cases this
    case _ => {
      subst x
      rename_i h₁
      simp [*] at h₁
    }
    case _ => {
      subst x
      rename_i h₁
      simp [*] at h₁
    }
  )

def toDir_vec {n} {depth} (ix: Vector (ZMod n) depth) : Vector Dir depth :=
  Vector.map Dir.toDir (Vector.map ZMod.val ix)

@[simp]
lemma toDir_vec_reverse {n} {depth} (ix : Vector (ZMod n) depth) :
  toDir_vec ix.reverse = (toDir_vec ix).reverse := by
  simp [toDir_vec]
  apply Vector.eq
  simp [Vector.toList_reverse, List.map_reverse]

@[simp]
lemma create_dir_vec_cons {n} {ix : ZMod n} {ixes: Vector (ZMod n) d} :
  toDir_vec (ix ::ᵥ ixes) = Dir.toDir ix.val ::ᵥ toDir_vec ixes := by
  simp [toDir_vec]

end Dir

inductive MerkleTree (F: Type) (H : Hash F 2) : Nat -> Type
| leaf : F  -> MerkleTree F H 0
| bin : MerkleTree F H depth -> MerkleTree F H depth -> MerkleTree F H (depth+1)
deriving Repr

namespace MerkleTree

def eq (a b : Nat) := a == b

def left_branch {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin l _ => l

def right_branch {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin _ r => r

/-- tree_for returns left/right subtree -/
def tree_for {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) (dir : Dir) : MerkleTree F H depth := match dir with
| Dir.left => t.left_branch
| Dir.right => t.right_branch

/-- root recursively walks the tree and returns the root -/
def root {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) : F := match t with
| leaf f => f
| bin l r => H vec![root l, root r]

/-- item_at walks the tree using path Vector and return leaf -/
def item_at {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Dir depth) : F := match depth with
  | Nat.zero => match t with
    | leaf f => f
  | Nat.succ _ => (t.tree_for p.head).item_at p.tail

/-- proof walks the tree using path Vector and return list of Hashes along the path -/
def proof {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Dir depth) : Vector F depth := match depth with
  | Nat.zero => Vector.nil
  | Nat.succ _ => Vector.cons (t.tree_for p.head.swap).root ((t.tree_for p.head).proof p.tail)

/-- recover recovers the Merkle tree from partial hashes. From bottom to top. It returns the item at the top (i.e. root) -/
def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : Vector Dir depth) (proof : Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let recover' := recover H ix.tail proof.tail item
    match ix.head with
      | Dir.left => H vec![recover', pitem]
      | Dir.right => H vec![pitem, recover']

/-- equal_recover_equal_tree proves that same proof and path imply same item -/
theorem equal_recover_equal_tree {depth : Nat} {F: Type} (H : Hash F 2)
  (ix : Vector Dir depth) (proof : Vector F depth) (item₁ : F) (item₂ : F)
  [Fact (perfect_hash H)]
  :
  (MerkleTree.recover H ix proof item₁ = MerkleTree.recover H ix proof item₂) ↔ (item₁ = item₂) := by
  apply Iff.intro
  case mp =>
    induction depth with
    | zero =>
      intro h
      unfold recover at h
      assumption
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

/-- recover_tail re-generates the Merkle tree from partial hashes. From top to bottom. It returns the item at the bottom (i.e. leaf) -/
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

/-- recover_tail_reverse_equals_recover proves that recover_tail on reverse Vectors is equal to recover -/
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
        Vector.reverse_cons,
        Vector.reverse_cons,
        recover_tail_snoc]
    unfold recover
    split <;> simp [*]

/-- recover_proof_is_root proves that recover on Merke Tree returns root -/
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
      congr <;> simp [*, proof, tree_for, left_branch, right_branch, Dir.swap, item_at, ih]
    )

/-- set sets item in the tree at position ix -/
def set { depth : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Dir depth) (item : F) : MerkleTree F H depth := match depth with
  | Nat.zero => leaf item
  | Nat.succ _ => match ix.head with
    | Dir.left => bin (set tree.left_branch ix.tail item) tree.right_branch
    | Dir.right => bin tree.left_branch (set tree.right_branch ix.tail item)

/-- read_after_insert_sound checks that set function changes the tree -/
theorem read_after_insert_sound {depth : Nat} {F: Type} {H: Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Dir depth) (new : F) :
  (tree.set ix new).item_at ix = new := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases tree
    simp [set]
    split <;> simp [item_at, tree_for, left_branch, right_branch, *]

/-- proof_ceritfies_item proves that if recover from item returns the root, then item_at returns the item -/
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
    simp [item_at, tree_for, left_branch, right_branch]
    split <;> {
      simp [recover, root, *, Vector.eq_cons_iff] at h
      cases h
      apply ih (proof := proof.tail)
      assumption
    }

/-!
proof_insert_invariant proves that if an item in the tree is overwritten,
proof and ix don't change to recover the tree
-/
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
      simp [root, recover, *, Vector.eq_cons_iff] at h
      simp [left_branch, right_branch, root, recover, *]
      congr
      apply ih
      simp [*]
    }

end MerkleTree