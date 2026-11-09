import NSSE.MultiConstructorGoodCommon

/-! An unpinned isolated endpoint of a proper common assignment can be
replaced by its allowed extreme. This realizes a U-witness of the same word. -/
namespace NSSE.MultiConstructorExtremeWitness
open MultiConstructorConstraints MultiConstructorTrees MultiConstructorTokens MultiConstructorRawValidity
open MultiConstructorUnifiedWords MultiConstructorUnifiedRays MultiConstructorCommonWord
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem lower_assignment (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (h : H) (hc : Common phi x y w heads h)
    (hp : lowerPins phi (row phi x y w w.length).2 = ∅) (hi : ¬IncidentY phi x y w w.length) :
    Assignment phi x y w heads (.node h) .bot := by
  refine ⟨hc.1,⟨hc.2.1,((common_domains phi _ h).mpr hc.2.2.1).1,hp,by intro he; cases he⟩,?_⟩
  intro a b l hb hal hbl hm
  have hstrict : b.val+l.val < w.length := by
    by_cases hs : b.val+l.val < w.length
    · exact hs
    · exact False.elim (hi (ray_incidentY phi x y w w.length a.val b.val l.val hal
        (Nat.le_antisymm hbl (Nat.le_of_not_gt hs)) hb hm))
  have hr := hc.2.2.2 a b l hb hal hbl hm
  simpa only [value,dif_pos hstrict,if_false] using hr

theorem upper_assignment (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (h : H) (hc : Common phi x y w heads h)
    (hp : upperPins phi (row phi x y w w.length).1 = ∅) (hi : ¬IncidentX phi x y w w.length) :
    Assignment phi x y w heads .top (.node h) := by
  refine ⟨hc.1,⟨hc.2.1,hp,((common_domains phi _ h).mpr hc.2.2.1).2,by intro he; cases he⟩,?_⟩
  intro a b l hb hal hbl hm
  have hstrict : a.val+l.val < w.length := by
    by_cases hs : a.val+l.val < w.length
    · exact hs
    · have he : a.val+l.val = w.length := Nat.le_antisymm hal (Nat.le_of_not_gt hs)
      apply False.elim
      apply hi
      refine ⟨b.val+l.val,hbl,?_⟩
      exact (GeneralCopyGrid.active_iff_ray _ w.length (b.val+l.val) w.length).mpr
        ⟨le_rfl,a.val,b.val,l.val,he,rfl,(ray_exact phi x y w a.val b.val l.val).mpr ⟨hb,hm⟩⟩
  have hr := hc.2.2.2 a b l hb hal hbl hm
  simpa only [value,dif_pos hstrict,if_true] using hr

theorem lower_witness (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (h : H) (hc : Common phi x y w heads h)
    (hp : lowerPins phi (row phi x y w w.length).2 = ∅) (hi : ¬IncidentY phi x y w w.length) :
    Witness phi x y w := ⟨heads,.node h,.bot,lower_assignment phi x y w heads h hc hp hi⟩

theorem upper_witness (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (h : H) (hc : Common phi x y w heads h)
    (hp : upperPins phi (row phi x y w w.length).1 = ∅) (hi : ¬IncidentX phi x y w w.length) :
    Witness phi x y w := ⟨heads,.top,.node h,upper_assignment phi x y w heads h hc hp hi⟩

end NSSE.MultiConstructorExtremeWitness
