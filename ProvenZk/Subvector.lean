import ProvenZk.Ext.Vector

abbrev SubVector α n prop := Subtype (α := Vector α n) (Vector.allIxes prop)

namespace SubVector

def nil : SubVector α 0 prop := ⟨Vector.nil, by simp⟩

def snoc (vs: SubVector α n prop) (v : Subtype prop): SubVector α n.succ prop :=
  ⟨vs.val.snoc v.val, by
    intro i
    cases i using Fin.lastCases with
    | last => simp [GetElem.getElem, Fin.last_def, Subtype.property]
    | cast i =>
      have := vs.prop i
      simp at this
      simp [*]
  ⟩

@[elab_as_elim]
def revCases {C : ∀ {n:Nat}, SubVector α n prop → Sort _} (v : SubVector α n prop)
  (nil : C nil)
  (snoc : ∀ {n : Nat} (vs : SubVector α n prop) (v : Subtype prop), C (vs.snoc v)): C v := by
  rcases v with ⟨v, h⟩
  cases v using Vector.revCasesOn with
  | nil => exact nil
  | snoc vs v =>
    refine snoc ⟨vs, ?vsp⟩ ⟨v, ?vp⟩
    case vsp =>
      intro i
      have := h i.castSucc
      simp at this
      simp [this]
    case vp =>
      have := h (Fin.last _)
      simp [GetElem.getElem, Fin.last_def] at this
      exact this

instance : GetElem (SubVector α n prop) (Fin n) (Subtype prop) (fun _ _ => True) where
  getElem v i _ := ⟨v.val.get i, v.prop i⟩

def lower (v: SubVector α n prop): Vector {v : α // prop v} n :=
  Vector.ofFn fun i => v[i]

def lift {prop : α → Prop} (v : Vector (Subtype prop) n): SubVector α n prop :=
  ⟨v.map Subtype.val, by
    intro i
    simp [GetElem.getElem, Subtype.property]⟩

theorem snoc_lower {vs : SubVector α n prop} {v : Subtype prop}:
  (vs.snoc v).lower = vs.lower.snoc v := by
  unfold lower
  rw [Vector.ofFn_snoc']
  congr
  . funext i
    cases n with
    | zero => cases i using finZeroElim
    | _ => simp [GetElem.getElem, snoc]
  . simp [GetElem.getElem, snoc, Fin.nat_cast_last]

end SubVector
