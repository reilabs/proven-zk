import Mathlib

import ProvenZk.Binary
import ProvenZk.Gates
import ProvenZk.Merkle
import ProvenZk.VectorExtensions

def Order : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
variable [Fact (Nat.Prime Order)]
abbrev F := ZMod Order

set_option maxHeartbeats 0
