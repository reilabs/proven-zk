import Mathlib.Data.List.Basic
import Mathlib.Data.List.Indexes

namespace List

-- lemma foldr_snoc_cons {α β} {f : α -> β -> β} {b : β} {x : α} {xs : List α}
--   {f_comm_assoc : ∀ x y z, f x (f y z) = f y (f x z)} :
--   List.foldr f b (xs ++ [x]) = List.foldr f b (x :: xs) := by

--   rw [List.foldr_append, List.foldr_cons, List.foldr_nil]
--   induction xs generalizing x with
--   | nil => rfl
--   | cons x' xs ih =>
--     conv =>
--       lhs
--       simp only [List.foldr]
--       tactic => have : (xs ++ [x]) = xs.append [x] := by simp
--       rw [←this, ih]
--     simp [List.foldr, f_comm_assoc]

-- lemma foldr_reverse_assoc {α β} {f : α -> β -> β} {b : β} {xs : List α}
--   { f_comm_assoc : ∀ x y z, f x (f y z) = f y (f x z) } :
--   List.foldr f b xs = List.foldr f b xs.reverse := by
--   induction xs with
--   | nil => rfl
--   | cons x xs ih =>
--     rw [List.reverse_cons, foldr_snoc_cons]
--     simp only [List.foldr, ih]
--     assumption

-- theorem dropLast_cons {head₁ head₂ : α} {tail : List α} : List.dropLast (head₁ :: head₂ :: tail) = head₁ :: (head₂ :: tail).dropLast := by
--   induction tail with
--   | nil => simp
--   | cons _ _ _ => simp [List.dropLast]

end List
