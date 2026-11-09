import NSSE.MultiVarianceClashCharacterization

/-! Executable local label compatibility from the original finite literal
and extremal lists. No support or model of the enlarged gadget is queried. -/
namespace NSSE.MultiVarianceLocalDecision
open MultiConstructorConstraints (Constraints)
open MultiConstructorTrees (Label)
open MultiVarianceModelTokens (Tokens)
open MultiVarianceSpineSuffixes MultiVarianceLabelBounds MultiVarianceClashCharacterization
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def FiniteCompatible (phi : Constraints arity n) (r : Bool) (S : Tokens n) (a : Label H) : Prop :=
  (∀ b ∈ bounds phi (!r), b.parent ∈ S → if r then .node b.head ≤ a else a ≤ .node b.head) ∧
    (∀ z ∈ assertions phi (!r), z ∈ S → if r then extreme (!r) ≤ a else a ≤ extreme (!r))

def finiteCompatibleDecision (phi : Constraints arity n) (r : Bool) (S : Tokens n) (a : Label H) :
    Decidable (FiniteCompatible phi r S a) := by
  unfold FiniteCompatible
  infer_instance

omit [DecidableEq H] in
theorem compatible_iff_finite (phi : Constraints arity n) (r : Bool) (S : Tokens n) (a : Label H) :
    Compatible phi r S a ↔ FiniteCompatible phi r S a := by
  constructor
  · intro hc
    constructor
    · intro b hb hm
      exact hc b.parent hm (.node b.head) (Or.inl ⟨b,hb,rfl,rfl⟩)
    · intro z hz hm
      exact hc z hm (extreme (!r)) (Or.inr ⟨hz,rfl⟩)
  · rintro ⟨hc,he⟩ z hz a (⟨b,hb,rfl,rfl⟩ | ⟨ha,rfl⟩)
    · exact hc b hb hz
    · exact he z ha hz

def compatibleDecision (phi : Constraints arity n) (r : Bool) (S : Tokens n) (a : Label H) :
    Decidable (Compatible phi r S a) := by
  letI := finiteCompatibleDecision phi r S a
  exact decidable_of_iff (FiniteCompatible phi r S a) (compatible_iff_finite phi r S a).symm

def inspectLocal (phi : Constraints arity n) (r : Bool) (S : Tokens n) (a : Label H) : Bool :=
  @decide (Compatible phi r S a) (compatibleDecision phi r S a)

theorem inspectLocal_correct (phi : Constraints arity n) (r : Bool) (S : Tokens n) (a : Label H) :
    inspectLocal phi r S a = true ↔ Compatible phi r S a := by
  unfold inspectLocal
  simp only [decide_eq_true_eq]

end NSSE.MultiVarianceLocalDecision
