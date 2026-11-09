import NSSE.MultiVarianceShapeRank

/-! Original literals determine the initial finite-shape heads. Signed
child refinement is already the actual two-set move theorem, shared with
the regular canonical model rather than re-assumed here. -/
namespace NSSE.MultiVarianceShapeLiterals
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceModelTokens MultiVarianceShapeTokens MultiVarianceShapeHead
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat} (pol : Polarity arity)

theorem lower_pin (phi : Constraints arity n) (a : Bound arity n) (ha : a∈phi.lower) :
    a.head∈lowerPins phi (start pol phi a.parent).1 :=
  (mem_lowerPins phi _ _).mpr ⟨a,ha,down_self pol phi a.parent,rfl⟩
theorem upper_pin (phi : Constraints arity n) (a : Bound arity n) (ha : a∈phi.upper) :
    a.head∈upperPins phi (start pol phi a.parent).2 :=
  (mem_upperPins phi _ _).mpr ⟨a,ha,up_self pol phi a.parent,rfl⟩

theorem upper_head (phi : Constraints arity n) (hn : ¬LabelClash pol phi)
    (a : Bound arity n) (ha : a∈phi.upper) :
    head phi (start pol phi a.parent)=.bot ∨ head phi (start pol phi a.parent)=.node a.head := by
  have hu := upper_pin pol phi a ha
  by_cases hl : lowerPins phi (start pol phi a.parent).1=∅
  · exact Or.inl (empty_lower_upper phi _ hl (Finset.nonempty_iff_ne_empty.mp ⟨a.head,hu⟩))
  · obtain ⟨g,hg⟩ := Finset.nonempty_iff_ne_empty.mpr hl
    have he := pins_equal pol phi hn _ (start_compatible pol phi a.parent) g a.head hg hu
    exact Or.inr (node_of_pins pol phi hn _ (start_compatible pol phi a.parent) a.head (he ▸ hg) hu)

theorem lower_head (phi : Constraints arity n) (hn : ¬LabelClash pol phi)
    (a : Bound arity n) (ha : a∈phi.lower) :
    head phi (start pol phi a.parent)=.top ∨ head phi (start pol phi a.parent)=.node a.head := by
  have hl := lower_pin pol phi a ha
  by_cases hu : upperPins phi (start pol phi a.parent).2=∅
  · exact Or.inl (nonempty_lower_no_upper phi _ (Finset.nonempty_iff_ne_empty.mp ⟨a.head,hl⟩) hu)
  · obtain ⟨g,hg⟩ := Finset.nonempty_iff_ne_empty.mpr hu
    have he := pins_equal pol phi hn _ (start_compatible pol phi a.parent) a.head g hl hg
    exact Or.inr (node_of_pins pol phi hn _ (start_compatible pol phi a.parent) a.head hl (he.symm ▸ hg))

theorem bot_head (phi : Constraints arity n) (hn : ¬LabelClash pol phi) (x : Fin n) (hx : x∈phi.bot) :
    head phi (start pol phi x)=.bot := by
  have hl : lowerPins phi (start pol phi x).1=∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro h hh
    obtain ⟨a,ha,hp,_⟩ := (mem_lowerPins phi _ _).mp hh
    exact hn (Or.inr (Or.inr (Or.inl ⟨a,ha,x,hx,(mem_down pol phi x a.parent).mp hp⟩)))
  exact empty_lower_bottom phi _ hl ⟨x,hx,up_self pol phi x⟩

theorem top_head (phi : Constraints arity n) (hn : ¬LabelClash pol phi) (x : Fin n) (hx : x∈phi.top) :
    head phi (start pol phi x)=.top := by
  have hu : upperPins phi (start pol phi x).2=∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro h hh
    obtain ⟨a,ha,hp,_⟩ := (mem_upperPins phi _ _).mp hh
    exact hn (Or.inr (Or.inl ⟨x,hx,a,ha,(mem_up pol phi x a.parent).mp hp⟩))
  have hb : ¬BottomHit phi (start pol phi x).2 := by
    rintro ⟨b,hb,hp⟩
    exact hn (Or.inl ⟨x,hx,b,hb,(mem_up pol phi x b).mp hp⟩)
  exact no_upper_no_bottom phi _ hu hb

end NSSE.MultiVarianceShapeLiterals
