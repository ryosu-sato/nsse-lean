import NSSE.MultiVarianceQueryBridge

/-!
One x818 signed spine step as ACTUAL flat four-form Constraints.
The six variables are x,y,u,v,Bottom,Top (indices 0..5).
The negative child's two rail variables exchange their bound roles.
No symbolic approximation and no unsigned/covariant encoding is used.

This proves a local typed spine-step compiler. It does NOT yet construct
one global Constraints value over all steps of an arbitrary spine.
-/
namespace NSSE.MultiVarianceFlatStep
open MultiConstructorConstraints (Constraints)
open MultiVarianceConstraints MultiVarianceEncoding MultiVarianceTrees
open MultiVarianceSpineSeparation MultiVarianceSpineGadget
variable {H : Type*} {arity : H → Nat}
variable (pol : Polarity arity)

def lowerChild (h : H) (i j : Fin (arity h)) : Fin 6 :=
  if j = i then (if pol h i then 3 else 2)
  else if pol h j then 5 else 4

def upperChild (h : H) (i j : Fin (arity h)) : Fin 6 :=
  if j = i then (if pol h i then 2 else 3)
  else if pol h j then 4 else 5

/-- The original four forms, not a surrogate formula. -/
def stepConstraints (h : H) (i : Fin (arity h)) : Constraints arity 6 where
  upper := [⟨1,h,upperChild pol h i⟩]
  lower := [⟨0,h,lowerChild pol h i⟩]
  bot := [4]
  top := [5]

def valuation (x y u v : Tree pol) (k : Fin 6) : Tree pol :=
  if k = 0 then x else if k = 1 then y else if k = 2 then u
  else if k = 3 then v else if k = 4 then ⊥ else ⊤

@[simp] theorem valuation_x (x y u v : Tree pol) :
    valuation pol x y u v 0 = x := rfl
@[simp] theorem valuation_y (x y u v : Tree pol) :
    valuation pol x y u v 1 = y := rfl
@[simp] theorem valuation_u (x y u v : Tree pol) :
    valuation pol x y u v 2 = u := rfl
@[simp] theorem valuation_v (x y u v : Tree pol) :
    valuation pol x y u v 3 = v := rfl
@[simp] theorem valuation_bot (x y u v : Tree pol) :
    valuation pol x y u v 4 = ⊥ := rfl
@[simp] theorem valuation_top (x y u v : Tree pol) :
    valuation pol x y u v 5 = ⊤ := rfl

@[simp] theorem value_lowerChild (h : H) (i j : Fin (arity h))
    (x y u v : Tree pol) :
    valuation pol x y u v (lowerChild pol h i j) =
      (if j = i then (if pol h i then v else u) else lowFill pol h j) := by
  by_cases hj : j = i
  · subst j
    cases hp : pol h i <;> simp [lowerChild, hp]
  · cases hp : pol h j <;> simp [lowerChild, hj, hp, lowFill]

@[simp] theorem value_upperChild (h : H) (i j : Fin (arity h))
    (x y u v : Tree pol) :
    valuation pol x y u v (upperChild pol h i j) =
      (if j = i then (if pol h i then u else v) else highFill pol h j) := by
  by_cases hj : j = i
  · subst j
    cases hp : pol h i <;> simp [upperChild, hp]
  · cases hp : pol h j <;> simp [upperChild, hj, hp, highFill]

theorem step_satisfies_iff (h : H) (i : Fin (arity h))
    (x y u v : Tree pol) :
    Satisfies (stepConstraints pol h i) (valuation pol x y u v) ↔
      lowerShell pol h i u v ≤ x ∧ y ≤ upperShell pol h i u v := by
  have hstep : Satisfies (stepConstraints pol h i) (valuation pol x y u v) ↔
      (y ≤ upperShell pol h i u v) ∧
      (lowerShell pol h i u v ≤ x) := by
    simp [Satisfies,stepConstraints,lowerShell,upperShell]
  exact hstep.trans ⟨(fun h => ⟨h.2,h.1⟩), (fun h => ⟨h.2,h.1⟩)⟩

/-- An actual flat step with two existential rail values and the tail. -/
def RealizesStep (h : H) (i : Fin (arity h)) (s : Spine arity)
    (x y : Tree pol) : Prop :=
  ∃ u v : Tree pol,
    Satisfies (stepConstraints pol h i) (valuation pol x y u v) ∧
    GadgetHolds pol s u v

theorem realizesStep_iff (h : H) (i : Fin (arity h))
    (s : Spine arity) (x y : Tree pol) :
    RealizesStep pol h i s x y ↔
      GadgetHolds pol (.step h i s) x y := by
  constructor
  · rintro ⟨u,v,hs,ht⟩
    obtain ⟨hl,hr⟩ := (step_satisfies_iff pol h i x y u v).mp hs
    change ∃ u v : Tree pol,
      lowerShell pol h i u v ≤ x ∧
      y ≤ upperShell pol h i u v ∧ GadgetHolds pol s u v
    exact ⟨u,v,hl,hr,ht⟩
  · intro hh
    change ∃ u v : Tree pol,
      lowerShell pol h i u v ≤ x ∧
      y ≤ upperShell pol h i u v ∧ GadgetHolds pol s u v at hh
    obtain ⟨u,v,hl,hr,ht⟩ := hh
    exact ⟨u,v,(step_satisfies_iff pol h i x y u v).mpr ⟨hl,hr⟩,ht⟩

theorem realizesStep_not_ordered (h : H) (i : Fin (arity h))
    (s : Spine arity) (hv : s.Valid) (x y : Tree pol)
    (hr : RealizesStep pol h i s x y) : ¬ x ≤ y := by
  apply (not_le_iff_gadget pol x y).mpr
  exact ⟨.step h i s,hv,(realizesStep_iff pol h i s x y).mp hr⟩

end NSSE.MultiVarianceFlatStep
