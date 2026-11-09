import NSSE.MultiVariancePositiveTermDecision

/-! Restrict actual flat finite/regular countermodels to ORIGINAL term
variables. Graph restriction only changes roots, preserving its state bound. -/
namespace NSSE.MultiVariancePositiveTermExtraction
open MultiConstructorTerms (Query)
open MultiConstructorTermLayout (layout)
open MultiVarianceEncoding MultiVarianceTerms MultiVarianceTermFlattening MultiVarianceTermClasses
open MultiVarianceFiniteTrees (Value embed)
open MultiVarianceBranchFamilyExtraction (GraphCode realize)
open MultiVarianceCountermodelExtraction (variableBound)
variable {H : Type*} {arity : H → Nat} {n : Nat}

def restrictCode (Q : Query arity n) (M : GraphCode arity (layout Q).count) : GraphCode arity n :=
  ⟨M.1,⟨M.2.graph,fun x => M.2.roots ((layout Q).old x)⟩⟩

theorem restrictCode_realize (pol : Polarity arity) (Q : Query arity n) (M : GraphCode arity (layout Q).count) :
    realize pol (restrictCode Q M)=(layout Q).restrict (realize pol M) := rfl

variable [DecidableEq H] [Fintype H] [Encodable H] (pol : Polarity arity)

def extractFinite (Q : Query arity n) (h : H) : Option (Fin n → Value arity) :=
  (MultiVarianceFiniteCountermodelExtraction.extract pol (flatten pol Q h)).map (layout Q).restrict
def extractAll (Q : Query arity n) (h : H) : Option (GraphCode arity n) :=
  (MultiVarianceCountermodelExtraction.extract pol (flatten pol Q h)).map (restrictCode Q)

theorem finite_none (Q : Query arity n) (h : H) (i : Fin (arity h)) : extractFinite pol Q h=none ↔ FiniteEntails pol Q := by
  have he : extractFinite pol Q h=none ↔ MultiVarianceFiniteCountermodelExtraction.extract pol (flatten pol Q h)=none := by
    unfold extractFinite
    cases MultiVarianceFiniteCountermodelExtraction.extract pol (flatten pol Q h) <;> simp
  exact he.trans ((MultiVarianceFiniteCountermodelExtraction.none_iff pol _).trans (finite_entails_iff pol Q h i))

theorem all_none (Q : Query arity n) (h : H) (i : Fin (arity h)) : extractAll pol Q h=none ↔ Entails pol Q := by
  have he : extractAll pol Q h=none ↔ MultiVarianceCountermodelExtraction.extract pol (flatten pol Q h)=none := by
    unfold extractAll
    cases MultiVarianceCountermodelExtraction.extract pol (flatten pol Q h) <;> simp
  exact he.trans ((MultiVarianceCountermodelExtraction.none_iff pol _).trans (entails_iff pol Q h i))

theorem finite_some (Q : Query arity n) (h : H) (i : Fin (arity h)) (rho : Fin n → Value arity)
    (he : extractFinite pol Q h=some rho) : Satisfies pol Q (fun x => embed pol (rho x)) ∧
      ¬embed pol (finiteEval rho Q.left)≤embed pol (finiteEval rho Q.right) := by
  unfold extractFinite at he
  cases hs : MultiVarianceFiniteCountermodelExtraction.extract pol (flatten pol Q h) with
  | none => simp [hs] at he
  | some sigma =>
    rw [hs] at he
    have hr : (layout Q).restrict sigma=rho := Option.some.inj he
    subst rho
    have hh := MultiVarianceFiniteCountermodelExtraction.some_spec pol (flatten pol Q h) sigma hs
    have hh' := countermodel_restrict pol Q h i (fun x => embed pol (sigma x)) hh.1 hh.2.1
    exact ⟨hh'.1,by simpa only [finite_eval_embed] using hh'.2⟩

theorem all_some (Q : Query arity n) (h : H) (i : Fin (arity h)) (M : GraphCode arity n)
    (he : extractAll pol Q h=some M) :
    Satisfies pol Q (realize pol M) ∧ ¬eval pol (realize pol M) Q.left≤eval pol (realize pol M) Q.right ∧
      ∀ x, MultiConstructorRegularTrees.Regular (realize pol M x).raw := by
  unfold extractAll at he
  cases hs : MultiVarianceCountermodelExtraction.extract pol (flatten pol Q h) with
  | none => simp [hs] at he
  | some M' =>
    rw [hs] at he
    have hr : restrictCode Q M'=M := Option.some.inj he
    subst M
    have hh := MultiVarianceCountermodelExtraction.some_spec pol (flatten pol Q h) M' hs
    have hh' := countermodel_restrict pol Q h i _ hh.1 hh.2.1
    exact ⟨hh'.1,hh'.2,fun x => hh.2.2 ((layout Q).old x)⟩

theorem finite_height (Q : Query arity n) (h : H) (rho : Fin n → Value arity)
    (he : extractFinite pol Q h=some rho) (x : Fin n) :
    MultiConstructorFiniteTrees.height (rho x)≤(variableBound (layout Q).count (MultiVarianceBranchFamily.alphabetSize arity))^2 := by
  unfold extractFinite at he
  cases hs : MultiVarianceFiniteCountermodelExtraction.extract pol (flatten pol Q h) with
  | none => simp [hs] at he
  | some sigma =>
    rw [hs] at he
    have hr : (layout Q).restrict sigma=rho := Option.some.inj he
    subst rho
    exact (MultiVarianceFiniteCountermodelExtraction.some_spec pol (flatten pol Q h) sigma hs).2.2 ((layout Q).old x)

theorem all_state_bound (Q : Query arity n) (h : H) (M : GraphCode arity n) (he : extractAll pol Q h=some M) :
    Fintype.card (MultiVarianceModelTokens.State M.1)≤4^(variableBound (layout Q).count (MultiVarianceBranchFamily.alphabetSize arity)) := by
  unfold extractAll at he
  cases hs : MultiVarianceCountermodelExtraction.extract pol (flatten pol Q h) with
  | none => simp [hs] at he
  | some M' =>
    rw [hs] at he
    have hr : restrictCode Q M'=M := Option.some.inj he
    subst M
    exact MultiVarianceCountermodelExtraction.some_states pol (flatten pol Q h) M' hs

end NSSE.MultiVariancePositiveTermExtraction
