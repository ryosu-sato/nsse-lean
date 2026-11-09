import NSSE.MultiVarianceGlobal

/-!
Soundness of the SINGLE globally indexed original four-form signed
spine input: every solution exhibits the intended two-rail separating
spine in the original head-dependent signed tree semantics.
This is the direction needed to rule out spurious countermodels.
Completeness/model extension and root aliasing remain separate.
-/
namespace NSSE.MultiVarianceGlobalSound
open MultiConstructorConstraints (Constraints)
open MultiVarianceConstraints MultiVarianceEncoding MultiVarianceTrees
open MultiVarianceSpineSeparation MultiVarianceSpineGadget
open MultiVarianceGlobal
variable {H : Type*} {arity : H → Nat}
variable (pol : Polarity arity)

theorem step_any (h : H) (i : Fin (arity h))
    (rho : Fin 6 → Tree pol)
    (hs : Satisfies (MultiVarianceFlatStep.stepConstraints pol h i) rho) :
    lowerShell pol h i (rho 2) (rho 3) ≤ rho 0 ∧
      rho 1 ≤ upperShell pol h i (rho 2) (rho 3) := by
  have hb : rho 4 = ⊥ :=
    hs.2.2.1 4 (by simp [MultiVarianceFlatStep.stepConstraints])
  have ht : rho 5 = ⊤ :=
    hs.2.2.2 5 (by simp [MultiVarianceFlatStep.stepConstraints])
  have he : rho = MultiVarianceFlatStep.valuation pol (rho 0) (rho 1) (rho 2) (rho 3) := by
    funext k
    fin_cases k <;> simp [MultiVarianceFlatStep.valuation, hb, ht]
  rw [he] at hs
  simpa only [MultiVarianceFlatStep.valuation_x,
    MultiVarianceFlatStep.valuation_y,MultiVarianceFlatStep.valuation_u,
    MultiVarianceFlatStep.valuation_v] using
    (MultiVarianceFlatStep.step_satisfies_iff pol h i _ _ _ _).mp hs

theorem stop_any (a b : MultiConstructorTrees.Label H)
    (rho : Fin 4 → Tree pol)
    (hs : Satisfies (MultiVarianceFlatStop.stopConstraints pol a b) rho) :
    lowHead pol a ≤ rho 0 ∧ rho 1 ≤ highHead pol b := by
  have hb : rho 2 = ⊥ :=
    hs.2.2.1 2 (by cases b <;>
      simp [MultiVarianceFlatStop.stopConstraints,
        MultiVarianceFlatStop.bottomAssertions])
  have ht : rho 3 = ⊤ :=
    hs.2.2.2 3 (by cases a <;>
      simp [MultiVarianceFlatStop.stopConstraints,
        MultiVarianceFlatStop.topAssertions])
  have he : rho = MultiVarianceFlatStop.valuation pol (rho 0) (rho 1) := by
    funext k
    fin_cases k <;> simp [MultiVarianceFlatStop.valuation,hb,ht]
  rw [he] at hs
  simpa only [MultiVarianceFlatStop.valuation_x,
    MultiVarianceFlatStop.valuation_y] using
    (MultiVarianceFlatStop.stop_satisfies_iff pol a b _ _).mp hs

@[simp] theorem stepEmbed_0 (d : Nat) :
    stepEmbed d 0 = rootX (d+1) := by apply Fin.ext; rfl
@[simp] theorem stepEmbed_1 (d : Nat) :
    stepEmbed d 1 = rootY (d+1) := by apply Fin.ext; rfl
@[simp] theorem stepEmbed_2 (d : Nat) :
    stepEmbed d 2 = shift d (rootX d) := by apply Fin.ext; rfl
@[simp] theorem stepEmbed_3 (d : Nat) :
    stepEmbed d 3 = shift d (rootY d) := by apply Fin.ext; rfl

theorem compile_to_formula (s : Spine arity)
    (rho : Fin (width s.depth) → Tree pol)
    (hs : Satisfies (compile pol s) rho) :
    MultiVarianceFlatSpine.Formula (pol := pol) s
      (rho (rootX s.depth)) (rho (rootY s.depth)) := by
  induction s with
  | stop a b =>
    change Satisfies (MultiVarianceFlatStop.stopConstraints pol a b) rho at hs
    have h := stop_any pol a b rho hs
    exact (MultiVarianceFlatStop.stop_satisfies_iff pol a b _ _).mpr h
  | step h i s ih =>
    change Satisfies
      (combine
        (remap (stepEmbed s.depth) (MultiVarianceFlatStep.stepConstraints pol h i))
        (remap (shift s.depth) (compile pol s))) rho at hs
    obtain ⟨hl,hr⟩ := (satisfies_combine pol _ _ rho).mp hs
    have hstep : Satisfies (MultiVarianceFlatStep.stepConstraints pol h i)
        (fun j => rho (stepEmbed s.depth j)) :=
      (satisfies_remap pol (stepEmbed s.depth)
        (MultiVarianceFlatStep.stepConstraints pol h i) rho).mp hl
    have htail : Satisfies (compile pol s) (fun j => rho (shift s.depth j)) :=
      (satisfies_remap pol (shift s.depth) (compile pol s) rho).mp hr
    have hlocal := step_any pol h i (fun j => rho (stepEmbed s.depth j)) hstep
    have htailForm := ih (fun j => rho (shift s.depth j)) htail
    let u : Tree pol := rho (stepEmbed s.depth 2)
    let v : Tree pol := rho (stepEmbed s.depth 3)
    have htail' : MultiVarianceFlatSpine.Formula (pol := pol) s u v := by
      simpa [u,v,stepEmbed_2,stepEmbed_3] using htailForm
    change ∃ u v : Tree pol,
      Satisfies (MultiVarianceFlatStep.stepConstraints pol h i)
        (MultiVarianceFlatStep.valuation pol
          (rho (rootX (s.depth+1))) (rho (rootY (s.depth+1))) u v) ∧
      MultiVarianceFlatSpine.Formula (pol := pol) s u v
    refine ⟨u,v,?_,htail'⟩
    apply (MultiVarianceFlatStep.step_satisfies_iff pol h i _ _ u v).mpr
    simpa [u,v,stepEmbed_0,stepEmbed_1,stepEmbed_2,stepEmbed_3]
      using hlocal

/-- The actual combined four-form constraints never yield a spurious
counterexample: every model really refutes the root comparison if the
supplied spine terminal labels are nonordered in the signed sense. -/
theorem compile_not_ordered (s : Spine arity) (hv : s.Valid)
    (rho : Fin (width s.depth) → Tree pol)
    (hs : Satisfies (compile pol s) rho) :
    ¬ rho (rootX s.depth) ≤ rho (rootY s.depth) := by
  apply (MultiVarianceSpineGadget.not_le_iff_gadget pol _ _).mpr
  exact ⟨s,hv,(MultiVarianceFlatSpine.formula_iff_gadget pol s _ _).mp
    (compile_to_formula pol s rho hs)⟩

end NSSE.MultiVarianceGlobalSound
