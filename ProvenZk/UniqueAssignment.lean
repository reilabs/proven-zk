
structure UniqueAssignment (f : (β → Prop) → Prop) (emb : α → β) where
  val : α
  equiv : ∀k, f k = k (emb val)

namespace UniqueAssignment

def constant (x : α) (emb : α → β): UniqueAssignment (fun k => k (emb x)) emb := ⟨x, fun _ => rfl⟩

def constant' (x : α) (y : β) (emb : α → β) (hp : y = emb x): UniqueAssignment (fun k => k y) emb := ⟨x, fun k => congrArg k hp⟩

def compose { f: (β → Prop) → Prop } {g : β → (γ → Prop) → Prop}
  (f_constant : UniqueAssignment f embf) (g_constant : ∀c, UniqueAssignment (g (embf c)) embg):
  UniqueAssignment (fun k => f (λx ↦ g x k)) embg := UniqueAssignment.mk
    (g_constant f_constant.val).val
    (fun _ => Eq.trans (f_constant.equiv _) ((g_constant _).equiv _))

end UniqueAssignment
