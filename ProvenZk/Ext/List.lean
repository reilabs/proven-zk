import Mathlib

namespace List

theorem mapIdx_compose {α β γ : Type} (f : ℕ → α → β) (g : ℕ → β → γ) (xs : List α) :
  mapIdx g (mapIdx f xs) = mapIdx (fun i x => g i (f i x)) xs := by
  induction xs using reverseRecOn with
  | H0 => rfl
  | H1 x xs ih =>
    simp [mapIdx_append]
    exact ih

end List