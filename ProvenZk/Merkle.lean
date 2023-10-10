import ProvenZk.Ext.Vector
import ProvenZk.Hash
import ProvenZk.Binary

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

def nat_to_dir : Nat -> Dir
  | 0 => Dir.left
  | 1 => Dir.right
  | Nat.succ (Nat.succ _) => panic "Dir can be 0 or 1"

def dir_mod_two (inp : Nat) : Dir := match h:inp%2 with
 | 0 => Dir.left
 | 1 => Dir.right
 | x + 2 => False.elim (by
   have := Nat.mod_lt inp (y := 2)
   rw [h] at this
   simp at this
   contradiction
 )

def nat_to_list_le : Nat → List Dir
  | 0 => [Dir.left]
  | 1 => [Dir.right]
  | x+2 => dir_mod_two x :: nat_to_list_le ((x + 2) / 2)
termination_by nat_to_list_le x => x
decreasing_by simp_wf; simp_arith; apply Nat.div_le_self

def nat_to_list_be (d: Nat) (ix: Nat): Vector Dir d := match d with
| 0 => Vector.nil
| Nat.succ d' => if ix ≥ 2^d'
  then Dir.right ::ᵥ nat_to_list_be d' (ix - 2^d')
  else Dir.left ::ᵥ nat_to_list_be d' ix

def dir_to_bit : Dir → Bit
  | Dir.left => Bit.zero
  | Dir.right => Bit.one

def bit_to_dir : Bit → Dir
  | Bit.zero => Dir.left
  | Bit.one => Dir.right

theorem bit_to_dir_to_bit : Dir.bit_to_dir (Dir.dir_to_bit x) = x := by cases x <;> rfl

def nat_to_dir_vec (idx : Nat) (depth : Nat ): Option <| Vector Dir depth :=
  (Vector.reverse ∘ Vector.map bit_to_dir) <$> nat_to_bits_le depth idx

def create_dir_vec {n} {depth} (ix: Vector (ZMod n) depth) : Vector Dir depth :=
  Vector.map Dir.nat_to_dir (Vector.map ZMod.val ix)

def list_to_vec_n (L : List Dir) (n : Nat) : Vector Dir n := ⟨List.takeI n L, List.takeI_length n L⟩

@[simp]
theorem list_to_vec_cons_succ : list_to_vec_n (x :: xs) (Nat.succ n) = x ::ᵥ list_to_vec_n xs n := by
  rfl

@[simp]
theorem list_to_vec_nil: list_to_vec_n [] n = Vector.replicate n Dir.left := by
  apply Vector.eq
  simp [list_to_vec_n, Vector.replicate, default]

@[simp]
lemma create_dir_vec_reverse {n} {depth} (ix : Vector (ZMod n) depth) :
  create_dir_vec ix.reverse = (create_dir_vec ix).reverse := by
  simp [create_dir_vec]
  apply Vector.eq
  simp [Vector.toList_reverse, List.map_reverse]

@[simp]
lemma create_dir_vec_cons {n} {ix : ZMod n} {ixes: Vector (ZMod n) d} :
  create_dir_vec (ix ::ᵥ ixes) = Dir.nat_to_dir ix.val ::ᵥ create_dir_vec ixes := by
  simp [create_dir_vec]

theorem dir_bit_dir : Dir.nat_to_dir x = Dir.bit_to_dir (nat_to_bit x) := by
  cases x
  . rfl
  . rename_i x; cases x <;> rfl

theorem create_dir_vec_bit : Dir.create_dir_vec w = Vector.map Dir.bit_to_dir (vector_zmod_to_bit w) := by
  induction w using Vector.inductionOn with
  | h_nil => rfl
  | h_cons ih =>
    simp [ih]
    congr
    rw [dir_bit_dir]

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

def item_at_nat {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) : Option F := do
  t.item_at <$> Dir.nat_to_dir_vec idx depth

-- Walk the tree using path Vector and return list of Hashes along the path
def proof {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Dir depth) : Vector F depth := match depth with
  | Nat.zero => Vector.nil
  | Nat.succ _ => Vector.cons (t.tree_for p.head.swap).root ((t.tree_for p.head).proof p.tail)

def proof_at_nat (t : MerkleTree F H depth) (idx: Nat): Option (Vector F depth) :=
  t.proof <$> Dir.nat_to_dir_vec idx depth

-- Recover the Merkle tree from partial hashes. From bottom to top. It returns the item at the top (i.e. root)
def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : Vector Dir depth) (proof : Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let recover' := recover H ix.tail proof.tail item
    match ix.head with
      | Dir.left => H vec![recover', pitem]
      | Dir.right => H vec![pitem, recover']

-- Same proof and path imply same item
theorem equal_recover_equal_tree {depth : Nat} {F: Type} (H : Hash F 2)
  (ix : Vector Dir depth) (proof : Vector F depth) (item₁ : F) (item₂ : F)
  [Fact (perfect_hash H)]
  :
  (recover H ix proof item₁ = recover H ix proof item₂) ↔ (item₁ = item₂) := by
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
        Vector.reverse_cons,
        Vector.reverse_cons,
        recover_tail_snoc]
    unfold recover
    split <;> simp [*]

theorem recover_tail_equals_recover_reverse
  {F depth}
  (H : Hash F 2)
  (ix : Vector Dir depth)
  (proof : Vector F depth)
  (item : F) :
  recover_tail H ix proof item = recover H ix.reverse proof.reverse item := by
  have : ix = ix.reverse.reverse:= by simp
  rw [this]
  have : proof = proof.reverse.reverse := by simp
  rw [this]
  rw [recover_tail_reverse_equals_recover]
  simp

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

-- Set item in the tree at position ix
def set { depth : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Dir depth) (item : F) : MerkleTree F H depth := match depth with
  | Nat.zero => leaf item
  | Nat.succ _ => match ix.head with
    | Dir.left => bin (set tree.left ix.tail item) tree.right
    | Dir.right => bin tree.left (set tree.right ix.tail item)

def set_at_nat(t : MerkleTree F H depth) (idx: Nat) (newVal: F): Option (MerkleTree F H depth) :=
  (t.set · newVal) <$> Dir.nat_to_dir_vec idx depth

theorem item_at_invariant { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {ix₁ ix₂ : Vector Dir depth} {item₁ : F} {neq : ix₁ ≠ ix₂}:
  item_at (set tree ix₁ item₁) ix₂ = item_at tree ix₂ := by
  induction depth with
  | zero =>
    cases ix₁ using Vector.casesOn
    cases ix₂ using Vector.casesOn
    cases (neq rfl)
  | succ depth ih =>
    cases ix₁ using Vector.casesOn; rename_i ix₁_hd ix₁_tl
    cases ix₂ using Vector.casesOn; rename_i ix₂_hd ix₂_tl
    cases tree; rename_i tree_l tree_r
    simp [item_at, set, tree_for, set, left, right]
    simp [Vector.vector_eq_cons] at neq
    cases ix₁_hd <;> { cases ix₂_hd <;> { simp [ih, neq] } }

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
      simp [recover, root, *, Vector.eq_cons_iff] at h
      cases h
      apply ih (proof := proof.tail)
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
      simp [root, recover, *, Vector.eq_cons_iff] at h
      simp [left, right, root, recover, *]
      congr
      apply ih
      simp [*]
    }

theorem recover_proof_reversible {H : Hash α 2} [Fact (perfect_hash H)] {Tree : MerkleTree α H d} {Proof : Vector α d}:
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
      have : perfect_hash H := (inferInstance : Fact (perfect_hash H)).out
      have := this h
      rw [Vector.vector_eq_cons, Vector.vector_eq_cons] at this
      casesm* (_ ∧ _)
      subst_vars
      simp [tree_for, Dir.swap, left, right]
      congr
      apply ih
      assumption
    }

end MerkleTree