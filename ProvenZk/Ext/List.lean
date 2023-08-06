import Mathlib

namespace List

-- mapIdx_compose combines the concatenation of two calls to mapIdx into a single
-- call of mapIdx
theorem mapIdx_compose {α β γ : Type} (f : ℕ → α → β) (g : ℕ → β → γ) (xs : List α) :
  mapIdx g (mapIdx f xs) = mapIdx (fun i x => g i (f i x)) xs := by
  induction xs using reverseRecOn with
  | H0 => rfl
  | H1 x xs ih =>
    simp [mapIdx_append]
    exact ih

-- foldr_snoc_cons proves that if f is associative,
-- it doesn't matter the position where x is added to xs:
-- foldr gives the same result
lemma foldr_snoc_cons {α β} {f : α -> β -> β} {b : β} {x : α} {xs : List α}
  {f_comm_assoc : ∀ x y z, f x (f y z) = f y (f x z)} :
  List.foldr f b (xs ++ [x]) = List.foldr f b (x :: xs) := by
  induction xs generalizing x with
  | nil => rfl
  | cons x' xs ih =>
    conv =>
      lhs
      simp only [List.foldr]
      tactic => have : (xs ++ [x]) = xs.append [x] := by simp
      rw [←this, ih]
    simp [List.foldr, f_comm_assoc]

-- foldr_reverse_assoc proves that if f is associative,
-- then it doesn't matter how xs is sorted: foldr gives the same result
lemma foldr_reverse_assoc {α β} {f : α -> β -> β} {b : β} {xs : List α}
  { f_comm_assoc : ∀ x y z, f x (f y z) = f y (f x z) } :
  List.foldr f b xs = List.foldr f b xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, foldr_snoc_cons]
    simp only [List.foldr, ih]
    assumption

end List