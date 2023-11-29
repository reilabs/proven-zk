import ProvenZk.Ext.Vector

def Hash (F: Type) (n: Nat) : Type := Vector F n -> F

def CollisionResistant {F n} (h: Hash F n): Prop := ∀{i1 i2}, h i1 = h i2 → i1 = i2

@[simp] theorem simp_hash {h : Hash F n} [Fact (CollisionResistant h)] {a b : Vector F n}: h a = h b ↔ a = b := by
    have : CollisionResistant h := (inferInstance : Fact (CollisionResistant h)).elim
    apply Iff.intro
    { apply (inferInstance : Fact (CollisionResistant h)).elim }
    { tauto }
