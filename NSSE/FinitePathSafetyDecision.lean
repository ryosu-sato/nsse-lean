import NSSE.FiniteUnsafetyCompiler

/-! # Exact finite-tree path safety and a computed countermodel

This decides one GIVEN path, not all paths. Recognition completeness still
has to connect automaton rejection to the satisfiability of its compiled
unsafety constraints; no such implication is assumed here.
-/

namespace NSSE.FinitePathSafetyDecision

open FiniteSubtypeTrees FiniteSubtypeSafety SubtypeConstraints ForwardTableAutomaton
open FiniteUnsafetyCompiler FiniteSubtypeDecision FiniteSubtypeSmallModel

variable {n d : Nat}

def decideSafe (Q : Query n d) (side : Side) (path : List (Fin d)) : Bool :=
  !decideSatisfiable (FiniteUnsafetyCompiler.compile Q side path)

theorem decideSafe_correct (Q : Query n d) (side : Side) (path : List (Fin d)) :
    decideSafe Q side path = true ↔ QuerySafe Q side path := by
  classical
  simp only [decideSafe, Bool.not_eq_true', decideSatisfiable_false, compile_satisfiable_iff, not_not]

theorem decideSafe_false (Q : Query n d) (side : Side) (path : List (Fin d)) :
    decideSafe Q side path = false ↔ ¬ QuerySafe Q side path := by
  rw [← decideSafe_correct]
  cases decideSafe Q side path <;> simp

/-- Actual finite trees, computed without being supplied a countermodel. -/
def candidate (Q : Query n d) (side : Side) (path : List (Fin d)) (x : Fin n) : Tree d :=
  model (FiniteUnsafetyCompiler.compile Q side path) (old path x)

theorem candidate_correct (Q : Query n d) (side : Side) (path : List (Fin d))
    (h : decideSafe Q side path = false) :
    Satisfies (constructor d) Q.constraints (candidate Q side path) ∧
      ¬ Safe side (candidate Q side path Q.left) (candidate Q side path Q.right) path := by
  have hs := (compile_satisfiable_iff Q side path).mpr ((decideSafe_false Q side path).mp h)
  exact compiled_solution_unsafe Q side path _ (model_satisfies _ hs)

theorem candidate_height (Q : Query n d) (side : Side) (path : List (Fin d)) (x : Fin n) :
    height (candidate Q side path x) ≤ 2 ^ (n + extra path) * 2 ^ (n + extra path) := by
  rw [← stateBound_eq]
  exact unfold_height_le _ _ _

theorem false_not_entails (Q : Query n d) (side : Side) (path : List (Fin d))
    (h : decideSafe Q side path = false) : ¬ Entails (constructor d) Q := by
  obtain ⟨hs,hu⟩ := candidate_correct Q side path h
  intro he
  exact hu (below_safe (he _ hs) side path)

def safetyDecision (Q : Query n d) (side : Side) (path : List (Fin d)) : Decidable (QuerySafe Q side path) :=
  decidable_of_iff (decideSafe Q side path = true) (decideSafe_correct Q side path)

end NSSE.FinitePathSafetyDecision
