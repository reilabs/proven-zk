import Mathlib
import Mathlib.Data.ZMod.Basic

namespace Gates
variable {N : Nat}
variable [Fact (Nat.Prime N)]
def is_bool (a : ZMod N): Prop := a = 0 ∨ a = 1
def add (a b : ZMod N): ZMod N := a + b
def mul_acc (a b c : ZMod N): ZMod N := a + (b * c)
def neg (a : ZMod N): ZMod N := a * (-1)
def sub (a b : ZMod N): ZMod N := a - b
def mul (a b : ZMod N): ZMod N := a * b
def div_unchecked (a b out : ZMod N): Prop := (b ≠ 0 ∧ out = a * (1 / b)) ∨ (a = 0 ∧ b = 0 ∧ out = 0)
def div (a b out : ZMod N): Prop := b ≠ 0 ∧ out = a * (1 / b)
def inv (a out : ZMod N): Prop := a ≠ 0 ∧ out = 1 / a
def xor (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a*(1-2*b)+b
def or (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a+b-a*b
def and (a b out : ZMod N): Prop := is_bool a ∧ is_bool b ∧ out = a*b
def select (b i1 i2 out : ZMod N): Prop := is_bool b ∧ ((b = 1 ∧ out = i1) ∨ (b = 0 ∧ out = i2))
def lookup (b0 b1 i0 i1 i2 i3 out : ZMod N): Prop := is_bool b0 ∧ is_bool b1 ∧ (
  (b0 = 0 ∧ b1 = 0 ∧ out = i0) ∨
  (b0 = 1 ∧ b1 = 0 ∧ out = i1) ∨
  (b0 = 0 ∧ b1 = 1 ∧ out = i2) ∨
  (b0 = 1 ∧ b1 = 1 ∧ out = i3)
)
def cmp (a b : ZMod N) (out : ZMod N): Prop := (a = b ∧ out = 0) ∨
(ZMod.val a < ZMod.val b ∧ out = -1) ∨
( ZMod.val a > ZMod.val b ∧ out = 1)
def is_zero (a out: ZMod N): Prop := (a = 0 ∧ out = 1) ∨ (a != 0 ∧ out = 0)
def eq (a b : ZMod N): Prop := a = b
def ne (a b : ZMod N): Prop := a ≠ b
def le (a b : ZMod N): Prop := ZMod.val a <= ZMod.val b
end Gates
