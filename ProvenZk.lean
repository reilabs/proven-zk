import Mathlib

import ProvenZk.Binary
import ProvenZk.Gates
import ProvenZk.Hash
import ProvenZk.Merkle
import ProvenZk.VectorExtensions

def Order : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
variable [Fact (Nat.Prime Order)]
abbrev F := ZMod Order

set_option maxHeartbeats 0

def DummyPoseidon1 (In: F) (k: F -> Prop): Prop :=
    ∃gate_0, gate_0 = Gates.mul In In ∧
    k gate_0

def DummyPoseidon2 (In_1: F) (In_2: F) (k: F -> Prop): Prop :=
    ∃gate_0, gate_0 = Gates.mul In_1 In_2 ∧
    k gate_0

def MerkleTreeInclusionProof_3_3 (Leaf: F) (PathIndices: Vector F 3) (Siblings: Vector F 3) (k: F -> Prop): Prop :=
    Gates.is_bool PathIndices[0] ∧
    DummyPoseidon2 Leaf Siblings[0] fun gate_1 =>
    DummyPoseidon2 Siblings[0] Leaf fun gate_2 =>
    ∃gate_3, Gates.select PathIndices[0] gate_2 gate_1 gate_3 ∧
    Gates.is_bool PathIndices[1] ∧
    DummyPoseidon2 gate_3 Siblings[1] fun gate_5 =>
    DummyPoseidon2 Siblings[1] gate_3 fun gate_6 =>
    ∃gate_7, Gates.select PathIndices[1] gate_6 gate_5 gate_7 ∧
    Gates.is_bool PathIndices[2] ∧
    DummyPoseidon2 gate_7 Siblings[2] fun gate_9 =>
    DummyPoseidon2 Siblings[2] gate_7 fun gate_10 =>
    ∃gate_11, Gates.select PathIndices[2] gate_10 gate_9 gate_11 ∧
    k gate_11

def circuit (IdentityNullifier: F) (IdentityTrapdoor: F) (TreePathIndices: Vector F 3) (TreeSiblings: Vector F 3) (SignalHash: F) (ExternalNullifier: F) (NullifierHash: F) (MTRoot: F): Prop :=
    DummyPoseidon2 IdentityNullifier IdentityTrapdoor fun gate_0 =>
    DummyPoseidon1 gate_0 fun gate_1 =>
    DummyPoseidon2 ExternalNullifier IdentityNullifier fun gate_2 =>
    Gates.eq gate_2 NullifierHash ∧
    MerkleTreeInclusionProof_3_3 gate_1 vec![TreePathIndices[0], TreePathIndices[1], TreePathIndices[2]] vec![TreeSiblings[0], TreeSiblings[1], TreeSiblings[2]] fun gate_4 =>
    Gates.eq gate_4 MTRoot ∧
    ∃_ignored_, _ignored_ = Gates.mul SignalHash SignalHash ∧
    True

def nat_to_dir : Nat -> Dir
    | 0 => Dir.right
    | 1 => Dir.left
    | Nat.succ (Nat.succ _) => panic "Dir can be 0 or 1"

def create_dir_vec {depth} (ix: Vector F depth) : Vector Dir depth :=
    Vector.map nat_to_dir (Vector.map ZMod.val ix)

def identity_commitment {F: Type} (H₁: Hash F 1) (H₂: Hash F 2) (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
    H₁ vec![H₂ vec![IdentityNullifier, IdentityTrapdoor]]

def nullifier_hash {F: Type} (H₂: Hash F 2) (IdentityNullifier: F) (ExternalNullifier: F) : F :=
    H₂ vec![ExternalNullifier, IdentityNullifier]

def dummy_hash₁ : Hash F 1 := fun a => a[0] * a[0]
def dummy_hash₂ : Hash F 2 := fun a => a[0] * a[1]

def circuit_simpl (H₁: Hash F 1) (H₂: Hash F 2) (IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root: F) (Path Proof: Vector F 3): Prop :=
    NullifierHash = nullifier_hash H₂ ExternalNullifier IdentityNullifier ∧
    MerkleTree.recover H₂ (create_dir_vec Path) Proof (identity_commitment H₁ H₂ IdentityNullifier IdentityTrapdoor) = Root

lemma circuit_simplified (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash Root: F) (Path Proof: Vector F 3):
    circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExternalNullifier NullifierHash Root ↔
    circuit_simpl dummy_hash₁ dummy_hash₂ IdentityNullifier IdentityTrapdoor SignalHash ExternalNullifier NullifierHash Root Path Proof := by sorry

theorem always_possible_to_signal
    (IdentityNullifier IdentitityTrapdoor SignalHash ExtNullifier : F)
    (Tree : MerkleTree F dummy_hash₂ 3)
    (Path : Vector F 3)
    (comm_in_tree : Tree.item_at (create_dir_vec Path) = identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier IdentitityTrapdoor)
    :
    circuit
        IdentityNullifier
        IdentitityTrapdoor
        Path
        (Tree.proof (create_dir_vec Path)) -- Siblings
        SignalHash
        ExtNullifier
        (nullifier_hash dummy_hash₂ ExtNullifier IdentityNullifier) -- NullifierHash
        Tree.root := by
        rw [circuit_simplified IdentityNullifier _ SignalHash ExtNullifier _ _ _ _]
        rw [<-MerkleTree.recover_proof_is_root _ (create_dir_vec Path) Tree]
        rw [comm_in_tree]
        unfold circuit_simpl
        simp

theorem circuit_proof (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash : F) (Path Proof: Vector F 3) (Tree : MerkleTree F dummy_hash₂ 3) :
    circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExternalNullifier NullifierHash Tree.root =
    circuit IdentityNullifier IdentityTrapdoor Path (MerkleTree.proof Tree (create_dir_vec Path)) SignalHash ExternalNullifier NullifierHash Tree.root := by
    sorry

theorem symmetry_prop {a b : F} (h : a = b) : b = a := by sorry

theorem signaller_is_in_tree
    (IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash : F)
    (Tree : MerkleTree F dummy_hash₂ 3)
    (Path Proof: Vector F 3)
    [Fact (perfect_hash dummy_hash₂)]
    :
    circuit IdentityNullifier IdentityTrapdoor Path Proof SignalHash ExtNullifier NullifierHash Tree.root →
    Tree.item_at (create_dir_vec Path) = identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier IdentityTrapdoor := by
    rw [circuit_proof IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash Path Proof Tree]
    rw [circuit_simplified IdentityNullifier IdentityTrapdoor SignalHash ExtNullifier NullifierHash _]
    unfold circuit_simpl
    rw [<-MerkleTree.recover_proof_is_root _ (create_dir_vec Path) Tree]
    let path := create_dir_vec Path
    let proof := MerkleTree.proof Tree (create_dir_vec Path)
    rw [MerkleTree.equal_recover_equal_tree dummy_hash₂ path proof (identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier IdentityTrapdoor)
                                                                   (MerkleTree.item_at Tree (create_dir_vec Path))]
    intro h
    cases h
    apply symmetry_prop
    assumption

theorem no_double_signal_with_same_commitment
    (IdentityNullifier₁ IdentityNullifier₂ IdentityTrapdoor₁ IdentityTrapdoor₂ SignalHash₁ SignalHash₂ ExtNullifier₁ ExtNullifier₂ NullifierHash₁ NullifierHash₂ Root₁ Root₂ : F)
    (Path₁ Proof₁ Path₂ Proof₂: Vector F 3)
    [Fact (perfect_hash dummy_hash₂)]
    [Fact (perfect_hash dummy_hash₁)]
    :
    circuit IdentityNullifier₁ IdentityTrapdoor₁ Path₁ Proof₁ SignalHash₁ ExtNullifier₁ NullifierHash₁ Root₁ →
    circuit IdentityNullifier₂ IdentityTrapdoor₂ Path₂ Proof₂ SignalHash₂ ExtNullifier₂ NullifierHash₂ Root₂ →
    identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier₁ IdentityTrapdoor₁ = identity_commitment dummy_hash₁ dummy_hash₂ IdentityNullifier₂ IdentityTrapdoor₂ →
    NullifierHash₁ = NullifierHash₂ := by
    rw [circuit_simplified IdentityNullifier₁ IdentityTrapdoor₁ SignalHash₁ ExtNullifier₁ NullifierHash₁ Root₁ Path₁ Proof₁]
    rw [circuit_simplified IdentityNullifier₂ IdentityTrapdoor₂ SignalHash₂ ExtNullifier₂ NullifierHash₂ Root₂ Path₂ Proof₂]
    unfold circuit_simpl
    intro h₁
    intro h₂
    intro h₃
    -- cases h₁.left
    -- cases h₂.left
    -- unfold identity_commitment
    -- unfold nullifier_hash
    sorry