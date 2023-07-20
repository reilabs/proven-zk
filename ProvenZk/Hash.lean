import ProvenZk.VectorExtensions

def Hash (F: Type) (n: Nat) : Type := Vector F n -> F

def perfect_hash {F n} (h: Hash F n): Prop := ∀{i1 i2}, h i1 = h i2 → i1 = i2