import NSSE.MultiConstructorCommonWord

/-! When accepted unequal terminals replace a safe common proper terminal,
every changed side is unpinned and isolated in the original copy grid. -/
namespace NSSE.MultiConstructorTerminalIsolation
open MultiConstructorConstraints MultiConstructorTrees MultiConstructorTokens MultiConstructorRawValidity
open MultiConstructorUnifiedWords MultiConstructorUnifiedRays MultiConstructorCommonWord
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem upper_unpinned (phi : Constraints arity n) (s : MultiConstructorRawTrace.Row n)
    (h : H) (e : Label H) (hc : Compatible phi s h) (he : UpperDomain phi s e)
    (hne : e ≠ .node h) : upperPins phi s.1 = ∅ := by
  cases e with
  | bot => exact he.elim
  | top => exact he
  | node g =>
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro f hf
    exact hne (congrArg Label.node ((he f hf).symm.trans (((common_domains phi s h).mpr hc).1 f hf)))

theorem lower_unpinned (phi : Constraints arity n) (s : MultiConstructorRawTrace.Row n)
    (h : H) (e : Label H) (hc : Compatible phi s h) (he : LowerDomain phi s e)
    (hne : e ≠ .node h) : lowerPins phi s.2 = ∅ := by
  cases e with
  | bot => exact he
  | top => exact he.elim
  | node g =>
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro f hf
    exact hne (congrArg Label.node ((he f hf).symm.trans (((common_domains phi s h).mpr hc).2 f hf)))

theorem lower_isolated (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (h : H) (ex ey : Label H)
    (hc : Common phi x y w heads h) (ha : Assignment phi x y w heads ex ey)
    (hne : ey ≠ .node h) : ¬IncidentY phi x y w w.length := by
  rintro ⟨j,hj⟩
  have hjn : j ≤ w.length := ((GeneralCopyGrid.active_iff_ray _ w.length w.length j).mp hj).1
  have hjlt : j < w.length := by
    by_cases he : j = w.length
    · subst j
      exact (no_active_diagonal phi x y w heads ex ey ha _ _ le_rfl hj).elim
    · omega
  have ho := rays_active_agree phi x y w heads ex ey ha.2.2 _ _ _ le_rfl hjn hj
  have hp := rays_active_agree phi x y w heads (.node h) (.node h) hc.2.2.2 _ _ _ le_rfl hjn hj
  rw [value_terminal,value,dif_pos hjlt] at ho hp
  change P0DZBranch.Agree (.node (heads ⟨j,hjlt⟩)) ey at ho
  change P0DZBranch.Agree (.node (heads ⟨j,hjlt⟩)) (.node h) at hp
  exact hne ((P0DZTrace.agree_eq ho).symm.trans (P0DZTrace.agree_eq hp))

theorem upper_isolated (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (h : H) (ex ey : Label H)
    (hc : Common phi x y w heads h) (ha : Assignment phi x y w heads ex ey)
    (hne : ex ≠ .node h) : ¬IncidentX phi x y w w.length := by
  rintro ⟨j,hjn,hj⟩
  have hjlt : j < w.length := by
    by_cases he : j = w.length
    · subst j
      exact (no_active_diagonal phi x y w heads ex ey ha _ _ le_rfl hj).elim
    · omega
  have ho := rays_active_agree phi x y w heads ex ey ha.2.2 _ _ _ hjn le_rfl hj
  have hp := rays_active_agree phi x y w heads (.node h) (.node h) hc.2.2.2 _ _ _ hjn le_rfl hj
  rw [value_terminal,value,dif_pos hjlt] at ho hp
  change P0DZBranch.Agree ex (.node (heads ⟨j,hjlt⟩)) at ho
  change P0DZBranch.Agree (.node h) (.node (heads ⟨j,hjlt⟩)) at hp
  exact hne ((P0DZTrace.agree_eq ho).trans (P0DZTrace.agree_eq hp).symm)

theorem changed_side (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (h : H) (ex ey : Label H)
    (hc : Common phi x y w heads h) (ha : Assignment phi x y w heads ex ey) :
    (upperPins phi (row phi x y w w.length).1 = ∅ ∧ ¬IncidentX phi x y w w.length) ∨
      (lowerPins phi (row phi x y w w.length).2 = ∅ ∧ ¬IncidentY phi x y w w.length) := by
  by_cases hex : ex = .node h
  · have hey : ey ≠ .node h := by intro he; exact ha.2.1.2.2.2 (hex.trans he.symm)
    exact Or.inr ⟨lower_unpinned phi _ h ey hc.2.2.1 ha.2.1.2.2.1 hey,
      lower_isolated phi x y w heads h ex ey hc ha hey⟩
  · exact Or.inl ⟨upper_unpinned phi _ h ex hc.2.2.1 ha.2.1.2.1 hex,
      upper_isolated phi x y w heads h ex ey hc ha hex⟩

end NSSE.MultiConstructorTerminalIsolation
