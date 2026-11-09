import NSSE.MultiVarianceOriginalSpine

/-! Executable canonical extensions of a supplied separating spine.
Finite/regular original values extend within their same tree class.
This is model transport for a supplied spine, not finite-SAT completeness. -/
namespace NSSE.MultiVarianceSpineAssignment
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceConstraints
open MultiVarianceSpineSeparation MultiVarianceSpineGadget
open MultiVarianceGlobal MultiVarianceGlobalComplete MultiVarianceOriginalSpine
variable {H : Type*} {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def assignment : (s : Spine arity) → Tree pol → Tree pol →
    (Fin (width s.depth) → Tree pol)
  | .stop _ _, x, y => MultiVarianceFlatStop.valuation pol x y
  | .step _ _ s, x, y => prepend pol x y (assignment s (lower pol s) (upper pol s))

@[simp] theorem assignment_rootX (s : Spine arity) (x y : Tree pol) :
    assignment pol s x y (rootX s.depth) = x := by cases s <;> rfl

@[simp] theorem assignment_rootY (s : Spine arity) (x y : Tree pol) :
    assignment pol s x y (rootY s.depth) = y := by cases s <;> rfl

theorem assignment_satisfies (s : Spine arity) (x y : Tree pol) (hf : Fits pol s x y) :
    Satisfies (compile pol s) (assignment pol s x y) := by
  induction s generalizing x y with
  | stop a b => exact (MultiVarianceFlatStop.stop_satisfies_iff pol a b x y).mpr hf
  | step h i s ih =>
    have ht := ih (lower pol s) (upper pol s) ⟨le_rfl,le_rfl⟩
    obtain ⟨hb,hu⟩ := compile_extremes pol s _ ht
    apply (satisfies_combine pol _ _ _).mpr
    constructor
    · apply (satisfies_remap pol _ _ _).mpr
      change Satisfies (MultiVarianceFlatStep.stepConstraints pol h i)
        (fun k => prepend pol x y (assignment pol s (lower pol s) (upper pol s)) (stepEmbed s.depth k))
      rw [prepend_local pol _ _ _ hb hu, assignment_rootX, assignment_rootY]
      exact (MultiVarianceFlatStep.step_satisfies_iff pol h i _ _ _ _).mpr hf
    · apply (satisfies_remap pol _ _ _).mpr
      simpa only [assignment, prepend_shift] using ht

variable (P : Tree pol → Prop) (pb : P ⊥) (pt : P ⊤)
    (pn : ∀ h c, (∀ i, P (c i)) → P (node h c))

include pb pt pn in
theorem bounds_class (s : Spine arity) : P (lower pol s) ∧ P (upper pol s) := by
  have hl (h : H) (i : Fin (arity h)) : P (lowFill pol h i) := by
    unfold lowFill
    split_ifs <;> assumption
  have hu (h : H) (i : Fin (arity h)) : P (highFill pol h i) := by
    unfold highFill
    split_ifs <;> assumption
  induction s with
  | stop a b =>
    constructor
    · cases a with
      | bot => exact pb
      | top => exact pt
      | node h => exact pn h _ (hl h)
    · cases b with
      | bot => exact pb
      | top => exact pt
      | node h => exact pn h _ (hu h)
  | step h i s ih =>
    constructor
    · apply pn
      intro j
      by_cases hj : j = i
      · subst j
        cases hp : pol h i
        · simpa [lower, bounds, hp] using ih.1
        · simpa [lower, bounds, hp] using ih.2
      · simpa [lower, bounds, hj] using hl h j
    · apply pn
      intro j
      by_cases hj : j = i
      · subst j
        cases hp : pol h i
        · simpa [upper, bounds, hp] using ih.2
        · simpa [upper, bounds, hp] using ih.1
      · simpa [upper, bounds, hj] using hu h j

include pb pt pn in
theorem assignment_class (s : Spine arity) (x y : Tree pol) (px : P x) (py : P y) :
    ∀ k, P (assignment pol s x y k) := by
  induction s generalizing x y with
  | stop a b =>
    intro k
    change P (MultiVarianceFlatStop.valuation pol x y k)
    unfold MultiVarianceFlatStop.valuation
    split_ifs <;> assumption
  | step h i s ih =>
    obtain ⟨pl,pu⟩ := bounds_class pol P pb pt pn s
    have hh := ih (lower pol s) (upper pol s) pl pu
    intro k
    change P (prepend pol x y (assignment pol s (lower pol s) (upper pol s)) k)
    unfold prepend
    split_ifs <;> first | assumption | exact hh _

def extend (Q : Query arity n) (s : Spine arity) (rho : Fin n → Tree pol) :
    Fin (count n s.depth) → Tree pol :=
  glue pol rho (assignment pol s (rho Q.left) (rho Q.right))

@[simp] theorem extend_old (Q : Query arity n) (s : Spine arity) (rho : Fin n → Tree pol)
    (x : Fin n) : extend pol Q s rho (old s.depth x) = rho x := glue_old pol _ _ x

theorem extend_satisfies (Q : Query arity n) (s : Spine arity) (rho : Fin n → Tree pol)
    (hr : Satisfies Q.constraints rho) (hf : Fits pol s (rho Q.left) (rho Q.right)) :
    Satisfies (extension pol Q s) (extend pol Q s rho) := by
  apply (extension_parts pol Q s _).mpr
  constructor
  · simpa only [extend_old] using hr
  · change Satisfies (compile pol s)
      (fun k => glue pol rho (assignment pol s (rho Q.left) (rho Q.right))
        (slot Q.left Q.right s.depth k))
    rw [glue_slot pol _ _ _ _ (assignment_rootX pol _ _ _) (assignment_rootY pol _ _ _)]
    exact assignment_satisfies pol s _ _ hf

include pb pt pn in
theorem extend_class (Q : Query arity n) (s : Spine arity) (rho : Fin n → Tree pol)
    (hr : ∀ x, P (rho x)) : ∀ k, P (extend pol Q s rho k) := by
  intro k
  unfold extend glue
  split_ifs
  · exact hr _
  · exact assignment_class pol P pb pt pn s _ _ (hr Q.left) (hr Q.right) _

theorem finite_node (h : H) (c : Fin (arity h) → Tree pol)
    (hc : ∀ i, MultiVarianceClasses.Finite (c i).raw) :
    MultiVarianceClasses.Finite (node h c).raw := by
  classical
  choose f hf using hc
  refine ⟨.node h f,?_⟩
  change MultiConstructorTrees.Tree.node h (fun i => MultiConstructorFiniteTrees.embed (f i)) =
    MultiConstructorTrees.Tree.node h (fun i => (c i).raw)
  congr 1
  funext i
  exact hf i

theorem extend_finite (Q : Query arity n) (s : Spine arity) (rho : Fin n → Tree pol)
    (hr : ∀ x, MultiVarianceClasses.Finite (rho x).raw) :
    ∀ k, MultiVarianceClasses.Finite (extend pol Q s rho k).raw :=
  extend_class pol (fun t => MultiVarianceClasses.Finite t.raw) ⟨.bot,rfl⟩ ⟨.top,rfl⟩
    (finite_node pol) Q s rho hr

theorem extend_regular (Q : Query arity n) (s : Spine arity) (rho : Fin n → Tree pol)
    (hr : ∀ x, MultiConstructorRegularTrees.Regular (rho x).raw) :
    ∀ k, MultiConstructorRegularTrees.Regular (extend pol Q s rho k).raw :=
  extend_class pol (fun t => MultiConstructorRegularTrees.Regular t.raw)
    MultiConstructorRegularTrees.bot_regular MultiConstructorRegularTrees.top_regular
    (fun h c hc => MultiConstructorRegularTrees.node_regular h (fun i => (c i).raw) hc) Q s rho hr

end NSSE.MultiVarianceSpineAssignment
