import NSSE.MultiConstructorUnifiedRays

/-! An isolated unpinned Y vertex at a proper frontier gives an earlier
unified witness by changing only that terminal label to Bottom. -/
namespace NSSE.MultiConstructorIsolatedPrefix
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawValidity MultiConstructorTrees
open MultiConstructorUnifiedWords MultiConstructorUnifiedPrefix MultiConstructorUnifiedRays
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

omit [DecidableEq H] in
theorem left_value (w : List (Fin D)) (heads : Fin w.length → H) (m k : Nat)
    (hm : m < w.length) (hk : k ≤ m) (ex ey : Label H) :
    value (w.take m) (restrictHeads w heads m) (.node (heads ⟨m,hm⟩)) .bot false k =
      value w heads ex ey false k := by
  by_cases hkm : k < m
  · exact value_restrict w heads m k (by omega) hkm ex ey _ _ false
  · have he : k = m := by omega
    subst k
    rw [value,dif_neg (by simp only [List.length_take]; omega)]
    change .node (heads ⟨m,hm⟩) = value w heads ex ey false m
    rw [value,dif_pos hm]

theorem lower_assignment (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : Label H) (ha : Assignment phi x y w heads ex ey)
    (m : Nat) (hm : m < w.length)
    (hp : lowerPins phi (row phi x y w m).2 = ∅) (hi : ¬IncidentY phi x y w m) :
    Assignment phi x y (w.take m) (restrictHeads w heads m) (.node (heads ⟨m,hm⟩)) .bot := by
  have hlen : (w.take m).length = m := by simp only [List.length_take,Nat.min_eq_left (by omega : m ≤ w.length)]
  refine ⟨local_restrict phi x y w heads m ha.1,?_,?_⟩
  · unfold Final
    rw [hlen,row_prefix phi x y w m m le_rfl]
    have hl := ha.1 ⟨m,hm⟩
    exact ⟨hl.1,((common_domains phi _ _).mpr hl.2.1).1,hp,by intro h; cases h⟩
  · intro a b l hb hal hbl hmatch
    have ham : a.val ≤ m := by have := a.isLt; omega
    have hbm : b.val ≤ m := by have := b.isLt; omega
    have hlm : l.val ≤ m := by have := l.isLt; omega
    have halm : a.val+l.val ≤ m := by simpa only [hlen] using hal
    have hblm : b.val+l.val ≤ m := by simpa only [hlen] using hbl
    have hb' := (born_prefix phi x y w m a.val b.val ham hbm).mp hb
    have hm' := (match_prefix w m a.val b.val l.val halm hblm).mp hmatch
    have hstrict : b.val+l.val < m := by
      by_cases hs : b.val+l.val < m
      · exact hs
      · exact False.elim (hi (ray_incidentY phi x y w m a.val b.val l.val halm
          (Nat.le_antisymm hblm (Nat.le_of_not_gt hs)) hb' hm'))
    have h := ha.2.2 ⟨a.val,by omega⟩ ⟨b.val,by omega⟩ ⟨l.val,by omega⟩ hb'
      (by change a.val+l.val ≤ w.length; omega)
      (by change b.val+l.val ≤ w.length; omega) hm'
    rw [left_value w heads m (a.val+l.val) hm halm ex ey,
      value_restrict w heads m (b.val+l.val) (by omega) hstrict ex ey _ _ true]
    exact h

theorem lower_witness (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : Label H) (ha : Assignment phi x y w heads ex ey)
    (m : Nat) (hm : m < w.length)
    (hp : lowerPins phi (row phi x y w m).2 = ∅) (hi : ¬IncidentY phi x y w m) :
    Witness phi x y (w.take m) :=
  ⟨restrictHeads w heads m,.node (heads ⟨m,hm⟩),.bot,lower_assignment phi x y w heads ex ey ha m hm hp hi⟩

def First (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) : Prop :=
  Witness phi x y w ∧ ∀ m, m < w.length → ¬Witness phi x y (w.take m)

theorem first_lower_incident (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (hf : First phi x y w) (heads : Fin w.length → H) (ex ey : Label H)
    (ha : Assignment phi x y w heads ex ey) (m : Nat) (hm : m < w.length)
    (hp : lowerPins phi (row phi x y w m).2 = ∅) : IncidentY phi x y w m := by
  by_contra hi
  exact hf.2 m hm (lower_witness phi x y w heads ex ey ha m hm hp hi)

end NSSE.MultiConstructorIsolatedPrefix
