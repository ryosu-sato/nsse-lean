import NSSE.UnsafetyCyclePreservation
import NSSE.FiniteSubtypeConsistency
import NSSE.FiniteForwardSoundness
import NSSE.FinitePathSafetyDecision

/-! # ACTUAL finite right recognition and a computed rejected-word model

Original finite SAT and literal right-automaton rejection produce an
original finite unsafe valuation. Neither compiler SAT nor a model is
supplied. This closes the right semantic completeness implication.
-/

namespace NSSE.FiniteRightRecognition

open SubtypeConstraints FiniteSubtypeTrees FiniteSubtypeSafety
open FiniteUnsafetyCompiler ConstraintForwardTables

variable {n d : Nat}

def compiledModel (Q : Query n d) (path : List (Fin d)) : Fin (n + extra path) → Tree d :=
  FiniteSubtypeConsistency.model (compile Q .right path)

def countermodel (Q : Query n d) (path : List (Fin d)) (x : Fin n) : Tree d :=
  compiledModel Q path (old path x)

theorem rejected_compiled_model (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    Satisfies (constructor d) (compile Q .right path) (compiledModel Q path) := by
  obtain ⟨hl,hc⟩ := UnsafetyCyclePreservation.rejection_consistent Q hd path hs hr
  exact FiniteSubtypeConsistency.model_satisfies _ hl hc

theorem rejected_compiled_sat (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    Satisfiable (constructor d) (compile Q .right path) :=
  ⟨compiledModel Q path,rejected_compiled_model Q hd path hs hr⟩

theorem rejected_countermodel (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    Satisfies (constructor d) Q.constraints (countermodel Q path) ∧
      ¬ Safe .right (countermodel Q path Q.left) (countermodel Q path Q.right) path :=
  compiled_solution_unsafe Q .right path (compiledModel Q path)
    (rejected_compiled_model Q hd path hs hr)

theorem countermodel_height (Q : Query n d) (path : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints) (x : Fin n) :
    height (countermodel Q path x) ≤ (n + extra path) * (n + extra path) :=
  FiniteSubtypeConsistency.model_height (compile Q .right path)
    (UnsafetyCyclePreservation.finite_sat_no_full_cycle Q path hs) (old path x)

/-- Both directions concern ORIGINAL finite-tree safety and the ACTUAL
constraint-derived automaton, with original SAT at the required boundary. -/
theorem recognition (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints) :
    ForwardCapAutomaton.Accepts (automaton Q .right) path ↔ QuerySafe Q .right path := by
  constructor
  · exact FiniteForwardSoundness.accepts_sound Q .right path
  · intro hsafe
    by_contra hr
    obtain ⟨hφ,hu⟩ := rejected_countermodel Q hd path hs hr
    exact hu (hsafe (countermodel Q path) hφ)

theorem accepts_iff_decideSafe (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints) :
    ForwardCapAutomaton.Accepts (automaton Q .right) path ↔
      FinitePathSafetyDecision.decideSafe Q .right path = true :=
  (recognition Q hd path hs).trans (FinitePathSafetyDecision.decideSafe_correct Q .right path).symm

theorem rejection_not_entails (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hs : Satisfiable (constructor d) Q.constraints)
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    ¬ Entails (constructor d) Q := by
  obtain ⟨hφ,hu⟩ := rejected_countermodel Q hd path hs hr
  intro he
  exact hu (below_safe (he _ hφ) .right path)

theorem rejection_sat_iff (Q : Query n d) (hd : 0 < d) (path : List (Fin d))
    (hr : ¬ ForwardCapAutomaton.Accepts (automaton Q .right) path) :
    Satisfiable (constructor d) (compile Q .right path) ↔ Satisfiable (constructor d) Q.constraints := by
  constructor
  · rintro ⟨ρ,hρ⟩
    exact ⟨fun x => ρ (old path x),(compiled_solution_unsafe Q .right path ρ hρ).1⟩
  · intro hs
    exact rejected_compiled_sat Q hd path hs hr

end NSSE.FiniteRightRecognition
