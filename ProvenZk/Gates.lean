import Mathlib.Data.ZMod.Defs

import ProvenZk.Binary

open BigOperators

namespace GatesDef
variable {N : Nat}
def is_bool (a : ZMod N): Prop := (1-a)*a = 0
def add (a b : ZMod N): ZMod N := a + b
def mul_acc (a b c : ZMod N): ZMod N := a + (b * c)
def neg (a : ZMod N): ZMod N := a * (-1)
def sub (a b : ZMod N): ZMod N := a - b
def mul (a b : ZMod N): ZMod N := a * b
def div_unchecked (a b out : ZMod N): Prop := (b ≠ 0 ∧ out*b = a) ∨ (a = 0 ∧ b = 0 ∧ out = 0)
def div (a b out : ZMod N): Prop := b ≠ 0 ∧ out*b = a
def inv (a out : ZMod N): Prop := a ≠ 0 ∧ out*a = 1
def xor (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a+b-a*b-a*b
def or (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a+b-a*b
def and (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a*b
def select (b i1 i2 out : ZMod N): Prop := is_bool b ∧ out = i2 - b*(i2-i1)
def lookup (b0 b1 i0 i1 i2 i3 out : ZMod N): Prop :=
  is_bool b0 ∧ is_bool b1 ∧
  out = (i2 - i0) * b1 + i0 + (((i3 - i2 - i1 + i0) * b1 + i1 - i0) * b0)

-- In gnark 8 the number is decomposed in a binary vector with the length of the field order
-- however this doesn't guarantee that the number is unique.
def cmp_8 (a b out : ZMod N): Prop :=
  ∃z w: Fin (binary_length N), z.val % N = a.val ∧ w.val % N = b.val ∧
  ((z = w ∧ out = 0) ∨
  (z.val < w.val ∧ out = -1) ∨
  (z.val > w.val ∧ out = 1))

-- In gnark 9 the number is reduced to the smallest representation, ensuring it is unique.
def cmp_9 (a b out : ZMod N): Prop :=
  (a = b ∧ out = 0) ∨
  (a.val < b.val ∧ out = -1) ∨
  (a.val > b.val ∧ out = 1)

def is_zero (a out: ZMod N): Prop := (a ≠ 0 ∧ out = 0) ∨ (a = 0 ∧ out = 1)
def eq (a b : ZMod N): Prop := a = b
def ne (a b : ZMod N): Prop := a ≠ b

def le_8 (a b : ZMod N): Prop :=
  ∃z w: Fin (binary_length N), z.val % N = a.val ∧ w.val % N = b.val ∧
  z.val <= w.val

def le_9 (a b : ZMod N): Prop :=
  a.val <= b.val

def to_binary (a : ZMod N) (d : Nat) (out : List.Vector (ZMod N) d): Prop :=
  @recover_binary_zmod' d N out = a ∧ is_vector_binary out
def from_binary {d} (a : List.Vector (ZMod N) d) (out : ZMod N) : Prop :=
  @recover_binary_zmod' d N a = out ∧ is_vector_binary a
end GatesDef

structure Gates_base (α : Type) : Type where
  is_bool : α → Prop
  add : α → α → α
  mul_acc : α → α → α → α
  neg : α → α
  sub : α → α → α
  mul : α → α → α
  div_unchecked : α → α → α → Prop
  div : α → α → α → Prop
  inv : α → α → Prop
  xor : α → α → α → Prop
  or : α → α → α → Prop
  and : α → α → α → Prop
  select : α → α → α → α → Prop
  lookup : α → α → α → α → α → α → α → Prop
  cmp : α → α → α → Prop
  is_zero : α → α → Prop
  eq : α → α → Prop
  ne : α → α → Prop
  le : α → α → Prop
  to_binary : α → (n : Nat) → List.Vector α n → Prop
  from_binary : List.Vector α d → α → Prop

def GatesGnark8 (N : Nat) [Fact (Nat.Prime N)] : Gates_base (ZMod N) := {
  is_bool := GatesDef.is_bool,
  add := GatesDef.add,
  mul_acc := GatesDef.mul_acc,
  neg := GatesDef.neg,
  sub := GatesDef.sub,
  mul := GatesDef.mul,
  div_unchecked := GatesDef.div_unchecked,
  div := GatesDef.div,
  inv := GatesDef.inv,
  xor := GatesDef.xor,
  or := GatesDef.or,
  and := GatesDef.and,
  select := GatesDef.select,
  lookup := GatesDef.lookup,
  cmp := GatesDef.cmp_8,
  is_zero := GatesDef.is_zero,
  eq := GatesDef.eq,
  ne := GatesDef.ne,
  le := GatesDef.le_8,
  to_binary := GatesDef.to_binary,
  from_binary := GatesDef.from_binary
}

def GatesGnark9 (N : Nat) [Fact (Nat.Prime N)] : Gates_base (ZMod N) := {
  GatesGnark8 N with
    cmp := GatesDef.cmp_9
    le := GatesDef.le_9
}
