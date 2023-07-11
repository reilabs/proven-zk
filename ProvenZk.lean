import Mathlib

import ProvenZk.Binary
import ProvenZk.Gates
import ProvenZk.Merkle
import ProvenZk.VectorExtensions

def Order : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
variable [Fact (Nat.Prime Order)]
abbrev F := ZMod Order

set_option maxHeartbeats 0

def DummyPoseidon1 (In: F) (k: F -> Prop): Prop :=
    ∃gate_0, gate_0 = Gates.mul In In ∧
    k gate_0

-- DummyPoseidon1 = In*In

-- def proof (In : F) : Prop :=
--     In

-- theorem dummy_poseidon_sound (In: F) : Prop :=
--     DummyPoseidon1 In proof

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
    
def generate_item {F: Type} (H: Hash F) (IdentityNullifier: F) (IdentityTrapdoor: F) : F :=
    H.hash₁ (H.hash IdentityNullifier IdentityTrapdoor)

def generate_nullifier {F: Type} (H: Hash F) (IdentityNullifier: F) (ExternalNullifier: F) : F :=
    H.hash IdentityNullifier ExternalNullifier

axiom fake_anti_collision {a b c d : F} : a * b = c * d → a = c ∧ b = d

def dummy_hash : Hash F := Hash.mk (fun a b => a * b) (fun a => a * a) (by
    simp
    apply fake_anti_collision
)

theorem member_in_tree (IdentityNullifier: F) (IdentityTrapdoor: F) (TreePathIndices: Vector F 3) (TreeSiblings: Vector F 3) (SignalHash: F) (ExternalNullifier: F) (NullifierHash: F) (MTRoot: F) :
    circuit IdentityNullifier IdentityTrapdoor TreePathIndices TreeSiblings SignalHash ExternalNullifier NullifierHash MTRoot → 
    MerkleTree.recover dummy_hash (create_dir_vec TreePathIndices) TreeSiblings (generate_item dummy_hash IdentityNullifier IdentityTrapdoor) = MTRoot := by
    sorry

theorem double_vote (IdentityNullifier: F) (IdentityTrapdoor: F) (TreePathIndices: Vector F 3) (TreeSiblings: Vector F 3) (SignalHash: F) (ExternalNullifier: F) (NullifierHash: F) (MTRoot: F) :
    circuit IdentityNullifier IdentityTrapdoor TreePathIndices TreeSiblings SignalHash ExternalNullifier NullifierHash MTRoot → 
    generate_nullifier dummy_hash IdentityNullifier ExternalNullifier = NullifierHash := by
    sorry