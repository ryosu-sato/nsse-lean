import NSSE.MultiVarianceSpineCycles
import NSSE.MultiVarianceFiniteDecision
import NSSE.MultiVarianceRawSpine

/-! The ACTUAL signed spine can be realized by finite values whenever
the original input has a finite solution and the spine passes its exact
checker. This yields finite/arbitrary entailment transfer on finite SAT. -/
namespace NSSE.MultiVarianceFiniteRealization
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceSpineSeparation
open MultiVarianceOriginalSpine MultiVarianceFiniteTrees
open MultiConstructorFiniteTrees (height)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat} (pol : Polarity arity)

theorem finite_extension_iff (Q : Query arity n) (s : Spine arity)
    (hf : MultiVarianceFiniteTrees.Satisfiable pol Q.constraints) :
    MultiVarianceFiniteTrees.Satisfiable pol (extension pol Q s) ↔
      MultiVarianceConstraints.Satisfiable pol (extension pol Q s) := by
  constructor
  · rintro ⟨rho,hs⟩
    exact ⟨fun x => embed pol (rho x),hs⟩
  · rintro ⟨rho,hs⟩
    apply (MultiVarianceFiniteModel.satisfiable_iff pol _).mpr
    exact ⟨no_label_clash _ rho hs,MultiVarianceSpineCycles.no_cycle pol Q s
      ((MultiVarianceFiniteModel.satisfiable_iff pol _).mp hf).2⟩

def values (Q : Query arity n) (s : Spine arity) : Fin n → Value arity :=
  fun x => MultiVarianceShapeGrammar.model pol (extension pol Q s) (old s.depth x)

theorem values_spec (Q : Query arity n) (s : Spine arity)
    (hf : MultiVarianceFiniteTrees.Satisfiable pol Q.constraints)
    (hi : MultiVarianceRawSpine.inspectSpine pol Q s=true) :
    Satisfies Q.constraints (fun x => embed pol (values pol Q s x)) ∧
      ¬embed pol (values pol Q s Q.left)≤embed pol (values pol Q s Q.right) ∧
      ∀ x, height (values pol Q s x)≤(count n s.depth)*(count n s.depth) := by
  obtain ⟨hv,hn⟩ := (MultiVarianceRawSpine.inspectSpine_correct pol Q s).mp hi
  have hc := MultiVarianceSpineCycles.no_cycle pol Q s
    ((MultiVarianceFiniteModel.satisfiable_iff pol _).mp hf).2
  have hs := MultiVarianceFiniteModel.satisfies pol (extension pol Q s) hn hc
  have hm := extension_countermodel pol Q s hv _ hs
  exact ⟨hm.1,hm.2,fun x => MultiVarianceShapeRank.model_height_bound pol _ hc (old s.depth x)⟩

theorem not_entails_iff (Q : Query arity n) :
    ¬MultiVarianceFiniteTrees.Entails pol Q ↔
      MultiVarianceFiniteTrees.Satisfiable pol Q.constraints ∧ ¬MultiVarianceConstraints.Entails pol Q := by
  classical
  constructor
  · intro hn
    obtain ⟨rho,hs,hbad⟩ : ∃ rho : Fin n → Value arity,
        Satisfies Q.constraints (fun x => embed pol (rho x)) ∧
        ¬embed pol (rho Q.left)≤embed pol (rho Q.right) := by
      by_contra hex
      apply hn
      intro rho hs
      by_contra hbad
      exact hex ⟨rho,hs,hbad⟩
    exact ⟨⟨rho,hs⟩,fun he => hbad (he _ hs)⟩
  · rintro ⟨hf,hn⟩ he
    obtain ⟨s,hv,hs⟩ := (not_entails_iff_extension pol Q).mp hn
    obtain ⟨rho,hr⟩ := (finite_extension_iff pol Q s hf).mpr hs
    have hm := extension_countermodel pol Q s hv _ hr
    exact hm.2 (he (fun x => rho (old s.depth x)) hm.1)

theorem entails_iff (Q : Query arity n) :
    MultiVarianceFiniteTrees.Entails pol Q ↔
      ¬MultiVarianceFiniteTrees.Satisfiable pol Q.constraints ∨ MultiVarianceConstraints.Entails pol Q := by
  classical
  constructor
  · intro he
    by_cases hf : MultiVarianceFiniteTrees.Satisfiable pol Q.constraints
    · right
      by_contra hn
      exact (not_entails_iff pol Q).mpr ⟨hf,hn⟩ he
    · exact Or.inl hf
  · rintro (hf | he) rho hs
    · exact False.elim (hf ⟨rho,hs⟩)
    · exact he _ hs

theorem entails_iff_of_finite_sat (Q : Query arity n)
    (hf : MultiVarianceFiniteTrees.Satisfiable pol Q.constraints) :
    MultiVarianceFiniteTrees.Entails pol Q ↔ MultiVarianceConstraints.Entails pol Q := by
  rw [entails_iff]
  simp only [hf,not_true_eq_false,false_or]

end NSSE.MultiVarianceFiniteRealization
