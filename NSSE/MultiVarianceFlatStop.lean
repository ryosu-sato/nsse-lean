import NSSE.MultiVarianceFlatStep

/-!
Actual four-form terminal clauses for a signed separating spine.
The four variable slots are x,y,Bottom,Top (indices 0..3).
A terminal .node h is enforced by the variance-correct extremal children.
An extremal terminal on the lower rail is Top, on the upper rail Bottom;
the other extreme imposes no nontrivial bound.
-/
namespace NSSE.MultiVarianceFlatStop
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceConstraints MultiVarianceEncoding MultiVarianceTrees
open MultiVarianceSpineSeparation MultiVarianceSpineGadget
open MultiConstructorTrees (Label)
variable {H : Type*} {arity : H → Nat}
variable (pol : Polarity arity)

def lowerChild (h : H) (i : Fin (arity h)) : Fin 4 :=
  if pol h i then 3 else 2

def upperChild (h : H) (i : Fin (arity h)) : Fin 4 :=
  if pol h i then 2 else 3

def lowerBounds : Label H → List (Bound arity 4)
  | .node h => [⟨0,h,lowerChild pol h⟩]
  | _ => []

def upperBounds : Label H → List (Bound arity 4)
  | .node h => [⟨1,h,upperChild pol h⟩]
  | _ => []

def bottomAssertions : Label H → List (Fin 4)
  | .bot => [1,2]
  | _ => [2]

def topAssertions : Label H → List (Fin 4)
  | .top => [0,3]
  | _ => [3]

def stopConstraints (a b : Label H) : Constraints arity 4 where
  upper := upperBounds pol b
  lower := lowerBounds pol a
  bot := bottomAssertions b
  top := topAssertions a

def valuation (x y : Tree pol) (z : Fin 4) : Tree pol :=
  if z = 0 then x else if z = 1 then y else if z = 2 then ⊥ else ⊤

@[simp] theorem valuation_x (x y : Tree pol) :
    valuation pol x y 0 = x := rfl
@[simp] theorem valuation_y (x y : Tree pol) :
    valuation pol x y 1 = y := rfl
@[simp] theorem valuation_bot (x y : Tree pol) :
    valuation pol x y 2 = ⊥ := rfl
@[simp] theorem valuation_top (x y : Tree pol) :
    valuation pol x y 3 = ⊤ := rfl

@[simp] theorem value_lowerChild (h : H) (i : Fin (arity h))
    (x y : Tree pol) :
    valuation pol x y (lowerChild pol h i) = lowFill pol h i := by
  cases hp : pol h i <;> simp [lowerChild, lowFill, hp]

@[simp] theorem value_upperChild (h : H) (i : Fin (arity h))
    (x y : Tree pol) :
    valuation pol x y (upperChild pol h i) = highFill pol h i := by
  cases hp : pol h i <;> simp [upperChild, highFill, hp]

theorem top_le_iff_eq (x : Tree pol) : (⊤ : Tree pol) ≤ x ↔ x = ⊤ := by
  constructor
  · intro h
    exact le_antisymm le_top h
  · rintro rfl
    exact le_rfl

theorem le_bot_iff_eq (y : Tree pol) : y ≤ (⊥ : Tree pol) ↔ y = ⊥ := by
  constructor
  · intro h
    exact le_antisymm h bot_le
  · rintro rfl
    exact le_rfl

/-- Exact semantic meaning of BOTH terminal literals and extremal assertions. -/
theorem stop_satisfies_iff (a b : Label H) (x y : Tree pol) :
    Satisfies (stopConstraints pol a b) (valuation pol x y) ↔
      lowHead pol a ≤ x ∧ y ≤ highHead pol b := by
  cases a <;> cases b <;>
    simp [Satisfies, stopConstraints, lowerBounds, upperBounds,
      bottomAssertions, topAssertions, lowHead, highHead,
      top_le_iff_eq, le_bot_iff_eq, and_assoc, and_comm, and_left_comm]

/-- The terminal case of the semantic spine gadget is an ACTUAL flat input. -/
theorem stop_gadget_iff (a b : Label H) (x y : Tree pol) :
    Satisfies (stopConstraints pol a b) (valuation pol x y) ↔
      GadgetHolds pol (.stop a b) x y := by
  exact stop_satisfies_iff pol a b x y

theorem stop_sound (a b : Label H) (hv : ¬a ≤ b)
    (x y : Tree pol)
    (hs : Satisfies (stopConstraints pol a b) (valuation pol x y)) :
    ¬x ≤ y := by
  exact (not_le_iff_gadget pol x y).mpr
    ⟨.stop a b,hv,(stop_gadget_iff pol a b x y).mp hs⟩

end NSSE.MultiVarianceFlatStop
