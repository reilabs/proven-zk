import Mathlib

theorem getElem?_eq_some_getElem_of_valid_index [GetElem cont idx elem domain] [Decidable (domain container index)] (h : domain container index):
  container[index]? = some container[index] := by
  unfold getElem?
  split
  . rfl
  . contradiction

theorem getElem!_eq_getElem_of_valid_index [GetElem cont idx elem domain] [Decidable (domain container index)] [Inhabited elem] (h : domain container index):
  container[index]! = container[index] := by
  simp [getElem!, h]

theorem getElem_of_getElem! [GetElem cont idx elem domain] [Decidable (domain container index)] [Inhabited elem] (ix_ok : domain container index) (h : container[index]! = element):
  container[index] = element := by
  simp [getElem!, ix_ok] at h
  assumption

theorem getElem?_none_of_invalid_index [GetElem cont idx elem domain] [Decidable (domain container index)] (h : ¬ domain container index):
  container[index]? = none := by
  unfold getElem?
  split
  . tauto
  . rfl

theorem valid_index_of_getElem?_some [GetElem cont idx elem domain] [Decidable (domain container index)] (h : container[index]? = some element):
  domain container index := by
  unfold getElem? at h
  split at h
  . assumption
  . contradiction

theorem getElem_of_getElem?_some [GetElem cont idx elem domain] [Decidable (domain container index)] (h : container[index]? = some element):
  container[index]'(valid_index_of_getElem?_some h) = element := by
  unfold getElem? at h
  split at h
  . injection h
  . contradiction

theorem getElem?_some_of_getElem [GetElem cont idx elem domain] [Decidable (domain container index)] {ix_valid : domain container index} (h : container[index]'ix_valid = element):
  container[index]? = some element := by
  unfold getElem?
  split
  . congr
  . contradiction

theorem getElem!_eq_getElem?_get! [GetElem cont idx elem domain] [Decidable (domain container index)] [Inhabited elem]:
  container[index]! = container[index]?.get! := by
  simp [getElem!, getElem?]
  split
  . rfl
  . unfold Option.get!; rfl
