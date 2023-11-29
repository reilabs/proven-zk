import Mathlib.Data.Vector.MapLemmas

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

theorem nat_to_dir_vec_unique {ix₁ ix₂ : Nat} {r₁ r₂ : Vector Dir d}:
  Dir.nat_to_dir_vec ix₁ d = some r₁ → Dir.nat_to_dir_vec ix₂ d = some r₂ → r₁ = r₂ → ix₁ = ix₂ := by
  simp [Dir.nat_to_dir_vec]
  intros
  subst_vars
  rw [←recover_binary_nat_to_bits_le, Vector.vector_reverse_inj, Vector.vector_map_inj] at *
  subst_vars
  rfl
  . intro a b; cases a <;> { cases b <;> tauto }

lemma dropLastOrder {d n : Nat} {out : Vector (ZMod n) d} : Dir.create_dir_vec (Vector.dropLast out) = (Dir.create_dir_vec out).dropLast := by
  induction out using Vector.inductionOn with
  | h_nil =>
    simp [Dir.create_dir_vec, Vector.dropLast, Dir.nat_to_dir, Vector.map]
  | h_cons ih₁ =>
    rename_i x₁ xs
    induction xs using Vector.inductionOn with
    | h_nil =>
      simp [Dir.create_dir_vec, Vector.dropLast, Dir.nat_to_dir, Vector.map]
    | h_cons _ =>
      rename_i x₂ xs
      simp [Vector.vector_list_vector]
      simp [ih₁]

def fin_to_dir_vec {depth : Nat} (idx : Fin (2 ^ depth)): Vector Dir depth :=
  (Vector.map Dir.bit_to_dir (fin_to_bits_le idx))

lemma zmod_to_bit_and_dir {n : Nat} [Fact (n > 1)] {x : ZMod n} {h : is_bit x}:
  Dir.bit_to_dir (zmod_to_bit x) = Dir.nat_to_dir (ZMod.val x) := by
  simp only [zmod_to_bit]
  simp only [Dir.bit_to_dir]
  simp only [Dir.nat_to_dir]
  cases h with
  | inl =>
    rename_i h
    simp [h]
  | inr =>
    rename_i h
    simp [h]
    rw [ZMod.val_one]

lemma vector_zmod_to_bit_and_dir {n : Nat} [Fact (n > 1)] {w : Vector (ZMod n) d} :
  is_vector_binary w →
  Vector.map (fun x => Dir.bit_to_dir (zmod_to_bit x)) w = Vector.map (fun x => Dir.nat_to_dir (ZMod.val x)) w := by
  induction w using Vector.inductionOn with
  | h_nil =>
    simp
  | h_cons ih =>
    intro h
    simp [is_vector_binary_cons] at h
    cases h
    rename_i y ys
    simp
    rw [zmod_to_bit_and_dir]
    rw [ih]
    assumption
    assumption

theorem recover_binary_zmod'_to_dir {n d : Nat} [Fact (n > 1)] {v : ZMod n} {w : Vector (ZMod n) d}:
  v.val < 2^d →
  n > 2^d →
  is_vector_binary w →
  recover_binary_zmod' w = v →
  fin_to_dir_vec v.val = (Dir.create_dir_vec w) := by
  intros
  simp [fin_to_dir_vec]
  simp [fin_to_bits_le]
  split
  . simp [Dir.create_dir_vec]
    rename_i r _
    have : some r = some (vector_zmod_to_bit w) := by
      rw [<-@recover_binary_zmod'_to_bits_le (v:= v)]
      apply Eq.symm
      rename_i h
      rw [ZMod.cast_eq_val] at h
      rw [Fin.val_cast_of_lt] at h
      assumption
      assumption
      assumption
      linarith
      assumption
      assumption
    simp at this
    rw [this]
    simp [vector_zmod_to_bit]
    rw [vector_zmod_to_bit_and_dir]
    assumption
  . rename_i hfin _ _ _ h
    rw [ZMod.cast_eq_val] at h
    rw [Fin.val_cast_of_lt] at h
    apply False.elim (by
      have := nat_to_bits_le_some_of_lt hfin
      cases this
      simp [*] at h
    )
    assumption

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

def item_at {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Dir depth) : F := match depth with
  | Nat.zero => match t with
    | leaf f => f
  | Nat.succ _ => (t.tree_for p.head).item_at p.tail

def item_at_nat {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) : Option F := do
  t.item_at <$> Dir.nat_to_dir_vec idx depth

def tree_item_at_fin_dropLast {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^(d+1))): F :=
  MerkleTree.item_at Tree (Dir.fin_to_dir_vec i).dropLast.reverse

def tree_item_at_fin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)): F :=
  MerkleTree.item_at Tree (Dir.fin_to_dir_vec i).reverse

def proof {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : Vector Dir depth) : Vector F depth := match depth with
  | Nat.zero => Vector.nil
  | Nat.succ _ => Vector.cons (t.tree_for p.head.swap).root ((t.tree_for p.head).proof p.tail)

def proof_at_nat (t : MerkleTree F H depth) (idx: Nat): Option (Vector F depth) :=
  t.proof <$> Dir.nat_to_dir_vec idx depth

def tree_proof_at_fin_dropLast {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^(d+1))): Vector F d :=
  MerkleTree.proof Tree (Dir.fin_to_dir_vec i).dropLast.reverse

def tree_proof_at_fin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)): Vector F d :=
  MerkleTree.proof Tree (Dir.fin_to_dir_vec i).reverse

lemma proof_at_nat_to_fin {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
  MerkleTree.proof_at_nat t idx = some (MerkleTree.tree_proof_at_fin t idx) := by
  simp [MerkleTree.proof_at_nat, MerkleTree.tree_proof_at_fin]
  simp [Dir.nat_to_dir_vec, Dir.fin_to_dir_vec]
  simp [fin_to_bits_le_is_some h]

lemma proof_at_nat_to_fin_some {depth : Nat} {F: Type} {H: Hash F 2} {a : Vector F depth} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
  MerkleTree.proof_at_nat t idx = some a ↔
  MerkleTree.tree_proof_at_fin t idx = a := by
  rw [proof_at_nat_to_fin (h := h)]
  . simp

def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : Vector Dir depth) (proof : Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let recover' := recover H ix.tail proof.tail item
    match ix.head with
      | Dir.left => H vec![recover', pitem]
      | Dir.right => H vec![pitem, recover']

theorem equal_recover_equal_tree {depth : Nat} {F: Type} (H : Hash F 2)
  (ix : Vector Dir depth) (proof : Vector F depth) (item₁ : F) (item₂ : F)
  [Fact (CollisionResistant H)]
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

def set_at_nat(t : MerkleTree F H depth) (idx: Nat) (newVal: F): Option (MerkleTree F H depth) :=
  (t.set · newVal) <$> Dir.nat_to_dir_vec idx depth

def tree_set_at_fin {F: Type} {H: Hash F 2} (Tree : MerkleTree F H d) (i : Fin (2^d)) (Item : F): MerkleTree F H d :=
  MerkleTree.set Tree (Dir.fin_to_dir_vec i).reverse Item

lemma set_at_nat_to_fin {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) (item : F) (h : idx < 2 ^ depth):
  MerkleTree.set_at_nat t idx item = some (MerkleTree.tree_set_at_fin t idx item) := by
  simp [MerkleTree.set_at_nat, MerkleTree.tree_set_at_fin]
  simp [Dir.nat_to_dir_vec]
  simp [Dir.fin_to_dir_vec]
  simp [fin_to_bits_le_is_some h]

lemma set_at_nat_to_fin_some {depth : Nat} {F: Type} {H: Hash F 2} {a : MerkleTree F H depth} (t : MerkleTree F H depth) (idx : Nat) (item : F) (h : idx < 2 ^ depth):
  MerkleTree.set_at_nat t idx item = some a ↔
  MerkleTree.tree_set_at_fin t idx item = a := by
  rw [set_at_nat_to_fin (h := h)]
  . simp

lemma item_at_nat_to_fin {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
  MerkleTree.item_at_nat t idx = some (MerkleTree.tree_item_at_fin t idx) := by
  simp [MerkleTree.item_at_nat, MerkleTree.tree_item_at_fin]
  simp [Dir.nat_to_dir_vec, Dir.fin_to_dir_vec]
  simp [fin_to_bits_le_is_some h]

lemma item_at_nat_to_fin_some {depth : Nat} {F: Type} {H: Hash F 2} {a : F} (t : MerkleTree F H depth) (idx : Nat) (h : idx < 2 ^ depth):
  MerkleTree.item_at_nat t idx = some a ↔
  MerkleTree.tree_item_at_fin t idx = a := by
  rw [item_at_nat_to_fin (h := h)]
  . simp

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

theorem item_at_nat_invariant {H : Hash α 2} {tree tree': MerkleTree α H depth} { neq : ix₁ ≠ ix₂ }:
  set_at_nat tree ix₁ item₁ = some tree' →
  item_at_nat tree' ix₂ = item_at_nat tree ix₂ := by
  simp [set_at_nat, item_at_nat]
  intros; subst_vars
  cases h : Dir.nat_to_dir_vec ix₂ depth with
  | none => rfl
  | some ix =>
    simp
    rw [item_at_invariant]
    intro hp
    refine (neq ?_)
    apply Dir.nat_to_dir_vec_unique <;> assumption

theorem item_at_fin_invariant {H : Hash α 2} {tree tree': MerkleTree α H depth} { neq : ix₁ ≠ ix₂ } {h₁ : ix₁ < 2 ^ depth} {h₂ : ix₂ < 2 ^ depth}:
  MerkleTree.tree_set_at_fin tree ix₁ item₁ = tree' →
  MerkleTree.tree_item_at_fin tree' ix₂ = MerkleTree.tree_item_at_fin tree ix₂ := by
  rw [<-set_at_nat_to_fin_some (h := h₁)]
  rw [<-item_at_nat_to_fin_some (h := h₂)]
  rw [<-item_at_nat_to_fin (h := h₂)]
  apply MerkleTree.item_at_nat_invariant (neq := neq)

theorem read_after_insert_sound {depth : Nat} {F: Type} {H: Hash F 2} (tree : MerkleTree F H depth) (ix : Vector Dir depth) (new : F) :
  (tree.set ix new).item_at ix = new := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    cases tree
    simp [set]
    split <;> simp [item_at, tree_for, left, right, *]

lemma set_implies_item_at { depth : Nat } {F: Type} {H : Hash F 2} {t₁ t₂ : MerkleTree F H depth} {ix : Vector Dir depth} {item : F} :
  set t₁ ix item = t₂ → item_at t₂ ix = item := by
  intro h
  rw [<-h]
  apply read_after_insert_sound

theorem proof_ceritfies_item
  {depth : Nat}
  {F: Type}
  {H: Hash F 2}
  [Fact (CollisionResistant H)]
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
  [Fact (CollisionResistant H)]
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
      rw [Vector.vector_eq_cons, Vector.vector_eq_cons] at this
      casesm* (_ ∧ _)
      subst_vars
      simp [tree_for, Dir.swap, left, right]
      congr
      apply ih
      assumption
    }

theorem recover_equivalence
  {F depth}
  (H : Hash F 2)
  [Fact (CollisionResistant H)]
  (tree : MerkleTree F H depth)
  (Path : Vector Dir depth)
  (Proof : Vector F depth)
  (Item : F) :
    (item_at tree Path = Item ∧ proof tree Path = Proof) ↔
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

lemma proof_of_set_is_proof
  {F d}
  (H : Hash F 2)
  [Fact (CollisionResistant H)]
  (Tree : MerkleTree F H d)
  (ix : Vector Dir d)
  (item : F):
  (MerkleTree.proof (MerkleTree.set Tree ix item) ix) = MerkleTree.proof Tree ix := by
  induction d with
  | zero =>
    simp [MerkleTree.set, MerkleTree.proof]
  | succ d ih =>
    cases Tree
    simp [MerkleTree.set, MerkleTree.proof, MerkleTree.tree_for]
    split
    . rename_i hdir
      have : Dir.swap (Dir.swap (Vector.head ix)) = Dir.right := by
        rw [hdir]
        simp [Dir.swap]
      have : Vector.head ix = Dir.right := by
        rw [<-this]
        simp [Dir.swap]
        cases ix.head
        . simp
        . simp
      rw [this]
      simp [MerkleTree.set, MerkleTree.left, MerkleTree.right]
      simp [Vector.vector_eq_cons]
      rw [ih]
    . rename_i hdir
      have : Dir.swap (Dir.swap (Vector.head ix)) = Dir.left := by
        rw [hdir]
        simp [Dir.swap]
      have : Vector.head ix = Dir.left := by
        rw [<-this]
        simp [Dir.swap]
        cases ix.head
        . simp
        . simp
      rw [this]
      simp [MerkleTree.set, MerkleTree.left, MerkleTree.right]
      simp [Vector.vector_eq_cons]
      rw [ih]

lemma proof_of_set_fin
  {F d}
  (H : Hash F 2)
  [Fact (CollisionResistant H)]
  (Tree : MerkleTree F H d)
  (ix : Fin (2^d))
  (item : F):
  (tree_proof_at_fin (tree_set_at_fin Tree ix item) ix) = tree_proof_at_fin Tree ix := by
  simp [tree_proof_at_fin, tree_set_at_fin]
  simp [proof_of_set_is_proof]

def multi_set { depth b : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (path : Vector (Vector Dir depth) b) (item : F) : MerkleTree F H depth :=
  match b with
  | Nat.zero => tree
  | Nat.succ _ => multi_set (tree.set path.head item) path.tail item

lemma tree_set_comm  { depth : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {p₁ p₂ : Vector Dir depth} {item : F}:
  MerkleTree.set (MerkleTree.set tree p₁ item) p₂ item = MerkleTree.set (MerkleTree.set tree p₂ item) p₁ item := by
  induction depth with
  | zero => rfl
  | succ d ih => cases tree with | bin l r =>
    cases p₁ using Vector.casesOn with | cons p₁h p₁t =>
    cases p₂ using Vector.casesOn with | cons p₂h p₂t =>
    cases p₁h <;> {
      cases p₂h <;> { simp [MerkleTree.set, MerkleTree.left, MerkleTree.right]; try rw [ih] }
    }

lemma multi_set_set { depth b : Nat } {F: Type} {H : Hash F 2} {tree : MerkleTree F H depth} {p : Vector Dir depth} {path : Vector (Vector Dir depth) b} {item : F}:
  multi_set (MerkleTree.set tree p item) path item = MerkleTree.set (multi_set tree path item) p item := by
  induction path using Vector.inductionOn generalizing tree p with
  | h_nil => rfl
  | h_cons ih => simp [multi_set, ih, tree_set_comm]

def multi_item_at { depth b : Nat } {F: Type} {H : Hash F 2} (tree : MerkleTree F H depth) (path : Vector (Vector Dir depth) b) (item : F) : Prop :=
  match b with
  | Nat.zero => true
  | Nat.succ _ => tree.item_at path.head = item ∧ multi_item_at tree path.tail item

theorem multi_set_is_item_at { depth b : Nat } {F: Type} {H : Hash F 2} {initialTree finalTree: MerkleTree F H depth} {path : Vector (Vector Dir depth) b} {item : F} :
  (multi_set initialTree path item = finalTree →
  multi_item_at finalTree path item) := by
  induction path using Vector.inductionOn generalizing initialTree finalTree with
  | h_nil =>
    simp [multi_set, multi_item_at]
  | @h_cons b' x xs ih =>
    unfold multi_set
    unfold multi_item_at
    simp only [Vector.tail_cons, Vector.head_cons]
    intro h
    refine ⟨?_, ?_⟩
    . rw [←h, multi_set_set, MerkleTree.read_after_insert_sound]
    . apply ih h

theorem multi_set_is_item_at_all_item { depth b i : Nat } {range : i ∈ [0:b]} {F: Type} {H : Hash F 2}
  {initialTree finalTree: MerkleTree F H depth} {path : Vector (Vector Dir depth) b} {item : F} :
  multi_set initialTree path item = finalTree →
  MerkleTree.item_at finalTree (path[i]'(by rcases range; tauto)) = item := by
  intro hp
  induction path using Vector.inductionOn generalizing i initialTree finalTree with
  | h_nil =>
    rcases range with ⟨lo, hi⟩
    have := Nat.ne_of_lt (Nat.lt_of_le_of_lt lo hi)
    contradiction
  | @h_cons b' x xs ih =>
    rcases range with ⟨lo, hi⟩
    cases lo with
    | refl =>
      have hitem_at : multi_item_at finalTree (x ::ᵥ xs) item := multi_set_is_item_at hp
      unfold multi_item_at at hitem_at
      tauto
    | @step i h =>
      exact ih (by assumption) (range := ⟨zero_le _, Nat.lt_of_succ_lt_succ hi⟩)

end MerkleTree
