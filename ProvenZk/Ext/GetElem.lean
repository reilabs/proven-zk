import Mathlib

theorem getElem?_eq_some_getElem_of_valid_index [GetElem cont idx elem domain] [(container: cont) → (index: idx) → Decidable (domain container index)] (h : domain container index):
  container[index]? = some container[index] := by
  simp [getElem?, *]

theorem getElem!_eq_getElem_of_valid_index [GetElem cont idx elem domain] [(container: cont) → (index: idx) →Decidable (domain container index)] [Inhabited elem] (h : domain container index):
  container[index]! = container[index] := by
  simp [getElem!, decidableGetElem?, h]

theorem getElem_of_getElem! [GetElem cont idx elem domain] [(container: cont) → (index: idx) → Decidable (domain container index)] [Inhabited elem] (ix_ok : domain container index) (h : container[index]! = element):
  container[index] = element := by
  simp [getElem!, ix_ok, decidableGetElem?] at h
  assumption

theorem getElem?_none_of_invalid_index [GetElem cont idx elem domain] [(container: cont) → (index: idx) → Decidable (domain container index)] (h : ¬ domain container index):
  container[index]? = none := by
  simp [getElem?, getElem!, decidableGetElem?, h]

theorem valid_index_of_getElem?_some [GetElem cont idx elem domain] [(container: cont) → (index: idx) → Decidable (domain container index)] (h : container[index]? = some element):
  domain container index := by
  simp [getElem?, decidableGetElem?] at h
  cases h
  assumption

theorem getElem_of_getElem?_some [GetElem cont idx elem domain] [(container: cont) → (index: idx) → Decidable (domain container index)] {index: idx} {container: cont} (h : container[index]? = some element):
  container[index]'(valid_index_of_getElem?_some h) = element := by
  simp [getElem?, decidableGetElem?] at h
  cases h
  assumption

theorem getElem?_some_of_getElem [GetElem cont idx elem domain] [(container: cont) → (index: idx) → Decidable (domain container index)] {ix_valid : domain container index} (h : container[index]'ix_valid = element):
  container[index]? = some element := by
  simp [getElem?, decidableGetElem?, *]

theorem getElem!_eq_getElem?_get! [GetElem cont idx elem domain] [(container: cont) → (index: idx) → Decidable (domain container index)] [Inhabited elem] {index: idx} {container: cont}:
  container[index]! = container[index]?.get! := by
  simp only [getElem!, getElem?, decidableGetElem?]
  split <;> {
    rename_i h
    rw [h]
    rfl
  }
