import NSSE.MultiVarianceWordOriginal
import NSSE.MultiVarianceBranchFamily

/-! Exact finite tests for arbitrary signed words and their first-prefix
property. Terminal choices are the actual finite head/extremum codes;
none of these tests decide unbounded word existence. -/
namespace NSSE.MultiVarianceWordDecision
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceWordReader MultiVarianceFirstPrefix
open MultiVarianceBranchFamily (label code label_code)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def acceptedDecision (Q : Query arity n) (w : List (Letter arity)) (ex ey : Label H) :
    Decidable (Accepted pol Q w ex ey) :=
  decidable_of_iff (MultiVarianceRawSpine.inspectSpine pol Q (make pol Q w ex ey)=true)
    (accepted_iff_inspect pol Q w ex ey).symm

theorem witness_iff_codes (Q : Query arity n) (w : List (Letter arity)) :
    Witness pol Q w ↔ ∃ a b : H ⊕ Bool, Accepted pol Q w (label a) (label b) := by
  constructor
  · rintro ⟨ex,ey,ha⟩
    exact ⟨code ex,code ey,by simpa only [label_code] using ha⟩
  · rintro ⟨a,b,ha⟩
    exact ⟨label a,label b,ha⟩

variable [Fintype H]

def witnessDecision (Q : Query arity n) (w : List (Letter arity)) : Decidable (Witness pol Q w) := by
  letI := acceptedDecision pol Q w
  exact decidable_of_iff (∃ a b : H ⊕ Bool, Accepted pol Q w (label a) (label b))
    (witness_iff_codes pol Q w).symm

def inspectWord (Q : Query arity n) (w : List (Letter arity)) : Bool :=
  @decide (Witness pol Q w) (witnessDecision pol Q w)

theorem inspectWord_correct (Q : Query arity n) (w : List (Letter arity)) :
    inspectWord pol Q w=true ↔ Witness pol Q w := by
  simp only [inspectWord,decide_eq_true_eq]

def firstDecision (Q : Query arity n) (w : List (Letter arity)) : Decidable (First pol Q w) := by
  letI := witnessDecision pol Q
  unfold First
  infer_instance

def inspectFirst (Q : Query arity n) (w : List (Letter arity)) : Bool :=
  @decide (First pol Q w) (firstDecision pol Q w)

theorem inspectFirst_correct (Q : Query arity n) (w : List (Letter arity)) :
    inspectFirst pol Q w=true ↔ First pol Q w := by
  simp only [inspectFirst,decide_eq_true_eq]

end NSSE.MultiVarianceWordDecision
