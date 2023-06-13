import Mathlib
import Mathlib.Data.Vector

import ProvenZk.Merkle
import ProvenZk.Binary
import ProvenZk.Gates
import ProvenZk.Vect
import ProvenZk.VectorExtensions

def Order : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
variable [Fact (Nat.Prime Order)]
abbrev F := ZMod Order

set_option maxHeartbeats 0

def hash (in_0: F) (in_1: F) (k: F -> Prop): Prop :=
    ∃gate_0, gate_0 = Gates.mul in_0 in_1 ∧
    k gate_0

def circuit (Root: F) (Element: F) (Path: Vect Bool depth) (Proof: Vect F depth): Prop :=
    hash Element Proof[0]! fun gate_0 =>
    hash Proof[0]! Element fun gate_1 =>
    ∃gate_2, Gates.sel Path[0]! gate_1 gate_0 gate_2 ∧
    hash gate_2 Proof[1]! fun gate_3 =>
    hash Proof[1]! gate_2 fun gate_4 =>
    ∃gate_5, Gates.sel Path[1]! gate_4 gate_3 gate_5 ∧
    hash gate_5 Proof[2]! fun gate_6 =>
    hash Proof[2]! gate_5 fun gate_7 =>
    ∃gate_8, Gates.sel Path[2]! gate_7 gate_6 gate_8 ∧
    hash gate_8 Proof[3]! fun gate_9 =>
    hash Proof[3]! gate_8 fun gate_10 =>
    ∃gate_11, Gates.sel Path[3]! gate_10 gate_9 gate_11 ∧
    hash gate_11 Proof[4]! fun gate_12 =>
    hash Proof[4]! gate_11 fun gate_13 =>
    ∃gate_14, Gates.sel Path[4]! gate_13 gate_12 gate_14 ∧
    hash gate_14 Proof[5]! fun gate_15 =>
    hash Proof[5]! gate_14 fun gate_16 =>
    ∃gate_17, Gates.sel Path[5]! gate_16 gate_15 gate_17 ∧
    hash gate_17 Proof[6]! fun gate_18 =>
    hash Proof[6]! gate_17 fun gate_19 =>
    ∃gate_20, Gates.sel Path[6]! gate_19 gate_18 gate_20 ∧
    hash gate_20 Proof[7]! fun gate_21 =>
    hash Proof[7]! gate_20 fun gate_22 =>
    ∃gate_23, Gates.sel Path[7]! gate_22 gate_21 gate_23 ∧
    hash gate_23 Proof[8]! fun gate_24 =>
    hash Proof[8]! gate_23 fun gate_25 =>
    ∃gate_26, Gates.sel Path[8]! gate_25 gate_24 gate_26 ∧
    hash gate_26 Proof[9]! fun gate_27 =>
    hash Proof[9]! gate_26 fun gate_28 =>
    ∃gate_29, Gates.sel Path[9]! gate_28 gate_27 gate_29 ∧
    hash gate_29 Proof[10]! fun gate_30 =>
    hash Proof[10]! gate_29 fun gate_31 =>
    ∃gate_32, Gates.sel Path[10]! gate_31 gate_30 gate_32 ∧
    hash gate_32 Proof[11]! fun gate_33 =>
    hash Proof[11]! gate_32 fun gate_34 =>
    ∃gate_35, Gates.sel Path[11]! gate_34 gate_33 gate_35 ∧
    hash gate_35 Proof[12]! fun gate_36 =>
    hash Proof[12]! gate_35 fun gate_37 =>
    ∃gate_38, Gates.sel Path[12]! gate_37 gate_36 gate_38 ∧
    hash gate_38 Proof[13]! fun gate_39 =>
    hash Proof[13]! gate_38 fun gate_40 =>
    ∃gate_41, Gates.sel Path[13]! gate_40 gate_39 gate_41 ∧
    hash gate_41 Proof[14]! fun gate_42 =>
    hash Proof[14]! gate_41 fun gate_43 =>
    ∃gate_44, Gates.sel Path[14]! gate_43 gate_42 gate_44 ∧
    hash gate_44 Proof[15]! fun gate_45 =>
    hash Proof[15]! gate_44 fun gate_46 =>
    ∃gate_47, Gates.sel Path[15]! gate_46 gate_45 gate_47 ∧
    hash gate_47 Proof[16]! fun gate_48 =>
    hash Proof[16]! gate_47 fun gate_49 =>
    ∃gate_50, Gates.sel Path[16]! gate_49 gate_48 gate_50 ∧
    hash gate_50 Proof[17]! fun gate_51 =>
    hash Proof[17]! gate_50 fun gate_52 =>
    ∃gate_53, Gates.sel Path[17]! gate_52 gate_51 gate_53 ∧
    hash gate_53 Proof[18]! fun gate_54 =>
    hash Proof[18]! gate_53 fun gate_55 =>
    ∃gate_56, Gates.sel Path[18]! gate_55 gate_54 gate_56 ∧
    hash gate_56 Proof[19]! fun gate_57 =>
    hash Proof[19]! gate_56 fun gate_58 =>
    ∃gate_59, Gates.sel Path[19]! gate_58 gate_57 gate_59 ∧
    Gates.eq gate_59 Root ∧
    True

def merkle_recover {depth F} (hash: F->F->F) (path: Vect Bool depth) (proof: Vect F depth) (item: F) : F :=
  match depth with
  | Nat.zero => item
  | Nat.succ _ => 
      let head := match path.head with
      | Bool.false => hash item proof.head
      | Bool.true => hash proof.head item
      merkle_recover hash path.tail proof.tail head

theorem circuit_program_equiv (path : Vect Bool 20) (proof : Vect F 20) (item result: F):
  circuit path proof item result <-> merkle_recover some_hash path proof item = result := by sorry