import ProvenZk.Ext.Vector

def Hash (F: Type) (n: Nat) : Type := Vector F n -> F

def perfect_hash {F n} (h: Hash F n): Prop := ∀{i1 i2}, h i1 = h i2 → i1 = i2

@[simp] theorem simp_hash {h : Hash F n} [Fact (perfect_hash h)] {a b : Vector F n}: h a = h b ↔ a = b := by
    have : perfect_hash h := (inferInstance : Fact (perfect_hash h)).elim
    apply Iff.intro
    { apply (inferInstance : Fact (perfect_hash h)).elim }
    { tauto }