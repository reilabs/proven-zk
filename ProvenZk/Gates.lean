import Init.Prelude
import Mathlib.Data.ZMod.Defs
import Mathlib.Init.Data.Nat.Bitwise

import ProvenZk.Binary

namespace Gates
variable {N : Nat}
variable [Fact (Nat.Prime N)]
def is_bool (a : ZMod N): Prop := (1-a)*a = 0 --a = 0 ∨ a = 1
def add (a b : ZMod N): ZMod N := a + b
def mul_acc (a b c : ZMod N): ZMod N := a + (b * c)
def neg (a : ZMod N): ZMod N := a * (-1)
def sub (a b : ZMod N): ZMod N := a - b
def mul (a b : ZMod N): ZMod N := a * b
def div_unchecked (a b out : ZMod N): Prop := (b ≠ 0 ∧ out*b = a) ∨ (a = 0 ∧ b = 0 ∧ out = 0) --(b ≠ 0 ∧ out = a * (1 / b)) ∨ (a = 0 ∧ b = 0 ∧ out = 0)
def div (a b out : ZMod N): Prop := b ≠ 0 ∧ out*b = a --b ≠ 0 ∧ out = a * (1 / b)
def inv (a out : ZMod N): Prop := a ≠ 0 ∧ out*a = 1 --a ≠ 0 ∧ out = 1 / a
def xor (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a+b-a*b-a*b
def or (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a+b-a*b
def and (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a*b
def select (b i1 i2 out : ZMod N): Prop := is_bool b ∧ out = i2 - b*(i2-i1) --((b = 1 ∧ out = i1) ∨ (b = 0 ∧ out = i2))
def lookup (b0 b1 i0 i1 i2 i3 out : ZMod N): Prop := is_bool b0 ∧ is_bool b1 ∧
  out = (i2 - i0) * b1 + i0 + (((i3 - i2 - i1 + i0) * b1 + i1 - i0) * b0)
/-(
  (b0 = 0 ∧ b1 = 0 ∧ out = i0) ∨
  (b0 = 1 ∧ b1 = 0 ∧ out = i1) ∨
  (b0 = 0 ∧ b1 = 1 ∧ out = i2) ∨
  (b0 = 1 ∧ b1 = 1 ∧ out = i3)
)-/
def cmp_8 (a b out : ZMod N): Prop :=
  ((recover_binary_nat (nat_to_bits_le_full_n (binary_length N) a.val)) % N = a.val) ∧
  ((recover_binary_nat (nat_to_bits_le_full_n (binary_length N) b.val)) % N = b.val) ∧
  ((a = b ∧ out = 0) ∨
  (ZMod.val a < ZMod.val b ∧ out = -1) ∨
  (ZMod.val a > ZMod.val b ∧ out = 1))

def cmp_9 (a b out : ZMod N): Prop :=
  ((recover_binary_nat (nat_to_bits_le_full_n (binary_length N) a.val)) = a.val) ∧
  ((recover_binary_nat (nat_to_bits_le_full_n (binary_length N) b.val)) = b.val) ∧
  ((a = b ∧ out = 0) ∨
  (ZMod.val a < ZMod.val b ∧ out = -1) ∨
  (ZMod.val a > ZMod.val b ∧ out = 1))

-- Inverse is calculated using a Hint at circuit execution
def is_zero (a out: ZMod N): Prop := (a ≠ 0 ∧ out = 1-(a*(1/a))) ∨ (a = 0 ∧ out = 1)  -- (a = 0 ∧ out = 1) ∨ (a != 0 ∧ out = 0)
def eq (a b : ZMod N): Prop := a = b
def ne (a b : ZMod N): Prop := a ≠ b
def le (a b : ZMod N): Prop :=
  ((recover_binary_nat (nat_to_bits_le_full_n (binary_length N) a.val)) % N = a.val) ∧
  ((recover_binary_nat (nat_to_bits_le_full_n (binary_length N) b.val)) % N = b.val) ∧
  ZMod.val a <= ZMod.val b
-- `a(.val)` is always less than `N` because it's `ZMod`.
-- If `a` doesn't fit in `n`, then the result of `recover_binary_zmod'` is `a % 2^n`
-- If `a` fits `n`, the result is exact
def to_binary (a : ZMod N) (d : Nat) (out : Vector (ZMod N) d): Prop :=
  (@recover_binary_zmod' d N out).val = (a.val % 2^d) ∧ is_vector_binary out
def from_binary {d} (a : Vector (ZMod N) d) (out : ZMod N) : Prop :=
  (@recover_binary_zmod' d N a).val = (out.val % 2^d)
end Gates

variable {N : Nat}
variable [Fact (Nat.Prime N)]

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
  to_binary : α → (n : Nat) → Vector α n → Prop
  from_binary : Vector α d → α → Prop

def GatesGnark_8 : Gates_base (ZMod N) := {
  is_bool := Gates.is_bool,
  add := Gates.add,
  mul_acc := Gates.mul_acc,
  neg := Gates.neg,
  sub := Gates.sub,
  mul := Gates.mul,
  div_unchecked := Gates.div_unchecked,
  div := Gates.div,
  inv := Gates.inv,
  xor := Gates.xor,
  or := Gates.or,
  and := Gates.and,
  select := Gates.select,
  lookup := Gates.lookup,
  cmp := Gates.cmp_8,
  is_zero := Gates.is_zero,
  eq := Gates.eq,
  ne := Gates.ne,
  le := Gates.le,
  to_binary := Gates.to_binary,
  from_binary := Gates.from_binary
}

--def GatesGnark_9 := { GatesGnark_8 with cmp := Gates.cmp_9  }
