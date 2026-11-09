import NSSE.MultiVarianceGlobalSound

/-! Model extension for the single globally indexed signed spine input.
The tail valuation is shared literally, including its two extremal slots.
No satisfiability, bounded-witness or independently split-value premise is used. -/
namespace NSSE.MultiVarianceGlobalComplete
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceConstraints
open MultiVarianceSpineSeparation MultiVarianceGlobal MultiVarianceGlobalSound
variable {H : Type*} {arity : H → Nat} (pol : Polarity arity)

theorem bottom_mem (s : Spine arity) : bottomAt s.depth ∈ (compile pol s).bot := by
  cases s with
  | stop a b =>
    cases b <;> simp [compile, bottomAt, Spine.depth,
      MultiVarianceFlatStop.stopConstraints, MultiVarianceFlatStop.bottomAssertions]
  | step h i s =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨4, by simp [MultiVarianceFlatStep.stepConstraints], stepEmbed_bot s.depth⟩

theorem top_mem (s : Spine arity) : topAt s.depth ∈ (compile pol s).top := by
  cases s with
  | stop a b =>
    cases a <;> simp [compile, topAt, Spine.depth,
      MultiVarianceFlatStop.stopConstraints, MultiVarianceFlatStop.topAssertions]
  | step h i s =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨5, by simp [MultiVarianceFlatStep.stepConstraints], stepEmbed_top s.depth⟩

theorem compile_extremes (s : Spine arity)
    (rho : Fin (width s.depth) → Tree pol) (hs : Satisfies (compile pol s) rho) :
    rho (bottomAt s.depth) = ⊥ ∧ rho (topAt s.depth) = ⊤ :=
  ⟨hs.2.2.1 _ (bottom_mem pol s), hs.2.2.2 _ (top_mem pol s)⟩

/-- Add the two new roots and retain every tail value at its shifted slot. -/
def prepend {d : Nat} (x y : Tree pol) (rho : Fin (width d) → Tree pol)
    (k : Fin (width (d+1))) : Tree pol :=
  if k.val = 0 then x else if k.val = 1 then y
  else rho ⟨k.val-2, by have hk := k.isLt; simp only [width] at hk ⊢; omega⟩

@[simp] theorem prepend_rootX {d : Nat} (x y : Tree pol) (rho : Fin (width d) → Tree pol) :
    prepend pol x y rho (rootX (d+1)) = x := rfl

@[simp] theorem prepend_rootY {d : Nat} (x y : Tree pol) (rho : Fin (width d) → Tree pol) :
    prepend pol x y rho (rootY (d+1)) = y := rfl

@[simp] theorem prepend_shift {d : Nat} (x y : Tree pol) (rho : Fin (width d) → Tree pol)
    (k : Fin (width d)) : prepend pol x y rho (shift d k) = rho k := by
  simp only [prepend, shift]
  have hz : ¬k.val+2 = 0 := by omega
  have ho : ¬k.val+2 = 1 := by omega
  simp only [hz, ho, if_false]
  congr 1

theorem prepend_local {d : Nat} (x y : Tree pol) (rho : Fin (width d) → Tree pol)
    (hb : rho (bottomAt d) = ⊥) (ht : rho (topAt d) = ⊤) :
    (fun k => prepend pol x y rho (stepEmbed d k)) =
      MultiVarianceFlatStep.valuation pol x y (rho (rootX d)) (rho (rootY d)) := by
  funext k
  fin_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · change prepend pol x y rho (stepEmbed d 4) = ⊥
    rw [stepEmbed_bot, ← shift_bottom, prepend_shift, hb]
  · change prepend pol x y rho (stepEmbed d 5) = ⊤
    rw [stepEmbed_top, ← shift_top, prepend_shift, ht]

theorem formula_to_compile (s : Spine arity) (x y : Tree pol)
    (hf : MultiVarianceFlatSpine.Formula (pol := pol) s x y) :
    ∃ rho : Fin (width s.depth) → Tree pol,
      Satisfies (compile pol s) rho ∧ rho (rootX s.depth) = x ∧ rho (rootY s.depth) = y := by
  induction s generalizing x y with
  | stop a b =>
    exact ⟨MultiVarianceFlatStop.valuation pol x y, hf, rfl, rfl⟩
  | step h i s ih =>
    obtain ⟨u,v,hl,hr⟩ := hf
    obtain ⟨rho,hs,hx,hy⟩ := ih u v hr
    refine ⟨prepend pol x y rho, ?_, rfl, rfl⟩
    apply (satisfies_combine pol _ _ _).mpr
    constructor
    · apply (satisfies_remap pol _ _ _).mpr
      obtain ⟨hb,ht⟩ := compile_extremes pol s rho hs
      rw [prepend_local pol x y rho hb ht, hx, hy]
      exact hl
    · apply (satisfies_remap pol _ _ _).mpr
      simpa only [prepend_shift] using hs

/-- Exact equivalence with one actual finite four-form constraint system. -/
theorem formula_iff_compile (s : Spine arity) (x y : Tree pol) :
    MultiVarianceFlatSpine.Formula (pol := pol) s x y ↔
      ∃ rho : Fin (width s.depth) → Tree pol,
        Satisfies (compile pol s) rho ∧ rho (rootX s.depth) = x ∧ rho (rootY s.depth) = y := by
  constructor
  · exact formula_to_compile pol s x y
  · rintro ⟨rho,hs,hx,hy⟩
    simpa only [hx,hy] using compile_to_formula pol s rho hs

theorem fits_iff_compile (s : Spine arity) (x y : Tree pol) :
    Fits pol s x y ↔ ∃ rho : Fin (width s.depth) → Tree pol,
      Satisfies (compile pol s) rho ∧ rho (rootX s.depth) = x ∧ rho (rootY s.depth) = y :=
  (MultiVarianceSpineGadget.gadget_iff_fits pol s x y).symm.trans
    ((MultiVarianceFlatSpine.formula_iff_gadget pol s x y).symm.trans
      (formula_iff_compile pol s x y))

end NSSE.MultiVarianceGlobalComplete
