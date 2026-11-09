import NSSE.MultiVarianceFiniteCountermodelExtraction
import NSSE.MultiVarianceShapeGraph

/-! The selected ORIGINAL finite countermodel also has a shared graph.
Its roots unfold to exactly the returned finite values; every reachable
original tree is finite even though irrelevant graph states may cycle. -/
namespace NSSE.MultiVarianceFiniteCountermodelGraph
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceFiniteTrees MultiVarianceOriginalSpine
open MultiVarianceFiniteCountermodelExtraction
open MultiVarianceCountermodelExtraction (variableBound)
open MultiVarianceBranchFamilyExtraction (GraphCode realize)
variable {H : Type*} [DecidableEq H] [Fintype H] [Encodable H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def positiveCode (Q : Query arity n) (hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true) :
    GraphCode arity n :=
  let s := selected pol Q hc
  ⟨count n s.depth,⟨MultiVarianceShapeGraph.graph pol (extension pol Q s),
    fun x => MultiVarianceModelTokens.start pol (extension pol Q s) (old s.depth x)⟩⟩

theorem positive_eq (Q : Query arity n) (hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true)
    (x : Fin n) : realize pol (positiveCode pol Q hc) x=embed pol (positiveValues pol Q hc x) := by
  have hfinite := ((MultiVarianceFiniteDecision.inspect_criterion pol Q.constraints).mp (Bool.and_eq_true_iff.mp hc).1).2
  exact MultiVarianceShapeGraph.code_realize_eq pol (extension pol Q (selected pol Q hc))
    (MultiVarianceSpineCycles.no_cycle pol Q _ hfinite) (old (selected pol Q hc).depth x)

theorem positive_spec (Q : Query arity n) (hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true) :
    Satisfies Q.constraints (realize pol (positiveCode pol Q hc)) ∧
      ¬realize pol (positiveCode pol Q hc) Q.left≤realize pol (positiveCode pol Q hc) Q.right ∧
      ∀ x, ∃ t : Value arity, embed pol t=realize pol (positiveCode pol Q hc) x ∧
        MultiConstructorFiniteTrees.height t≤(variableBound n (MultiVarianceBranchFamily.alphabetSize arity))^2 := by
  have hs := MultiVarianceFiniteCountermodelExtraction.positive_spec pol Q hc
  have he := positive_eq pol Q hc
  refine ⟨?_,?_,fun x => ⟨_,(he x).symm,hs.2.2 x⟩⟩
  · simpa only [funext he] using hs.1
  · simpa only [he] using hs.2.1

def extract (Q : Query arity n) : Option (GraphCode arity n) :=
  if hc : MultiVarianceFiniteEntailmentDecision.counterexample pol Q=true then some (positiveCode pol Q hc) else none

theorem none_iff (Q : Query arity n) : extract pol Q=none ↔ MultiVarianceFiniteTrees.Entails pol Q := by
  unfold extract
  split_ifs with hc
  · simp only [Option.some_ne_none,false_iff]
    exact (MultiVarianceFiniteEntailmentDecision.counterexample_correct pol Q).mp hc
  · simp only [true_iff]
    exact Classical.not_not.mp (fun hn => hc ((MultiVarianceFiniteEntailmentDecision.counterexample_correct pol Q).mpr hn))

theorem some_spec (Q : Query arity n) (M : GraphCode arity n) (he : extract pol Q=some M) :
    Satisfies Q.constraints (realize pol M) ∧ ¬realize pol M Q.left≤realize pol M Q.right ∧
      ∀ x, ∃ t : Value arity, embed pol t=realize pol M x ∧
        MultiConstructorFiniteTrees.height t≤(variableBound n (MultiVarianceBranchFamily.alphabetSize arity))^2 := by
  unfold extract at he
  split_ifs at he with hc
  have hh := Option.some.inj he
  subst M
  exact positive_spec pol Q hc

theorem some_size (Q : Query arity n) (M : GraphCode arity n) (he : extract pol Q=some M) :
    M.1≤variableBound n (MultiVarianceBranchFamily.alphabetSize arity) := by
  unfold extract at he
  split_ifs at he with hc
  have hh := Option.some.inj he
  subst M
  exact selected_count pol Q hc

theorem some_states (Q : Query arity n) (M : GraphCode arity n) (he : extract pol Q=some M) :
    Fintype.card (MultiVarianceModelTokens.State M.1)≤4^(variableBound n (MultiVarianceBranchFamily.alphabetSize arity)) := by
  rw [MultiVarianceModelTokens.card_states]
  exact Nat.pow_le_pow_right (by omega) (some_size pol Q M he)

theorem returns_iff (Q : Query arity n) :
    (∃ M, extract pol Q=some M) ↔ ¬MultiVarianceFiniteTrees.Entails pol Q := by
  rw [← none_iff]
  cases extract pol Q <;> simp

end NSSE.MultiVarianceFiniteCountermodelGraph
