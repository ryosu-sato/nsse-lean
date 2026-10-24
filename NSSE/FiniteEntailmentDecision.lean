import NSSE.FiniteRecognition

/-! # The ACTUAL full finite-tree entailment decision, from original syntax

The original SAT branch is indispensable. Both directions below concern
original finite-tree entailment, not merely automaton universality.
-/

namespace NSSE.FiniteEntailmentDecision

open SubtypeConstraints FiniteSubtypeTrees FiniteSubtypeSafety ForwardTableAutomaton
open ConstraintForwardTables FiniteSubtypeDecision

variable {n d : Nat}

def decideEntails (Q : Query n d) : Bool :=
  !decideSatisfiable Q.constraints || decideBothSides Q

theorem decideEntails_correct (Q : Query n d) (hd : 0 < d) :
    decideEntails Q = true ↔ Entails (constructor d) Q := by
  classical
  by_cases hs : Satisfiable (constructor d) Q.constraints
  · have hb := (decideSatisfiable_correct Q.constraints).mpr hs
    simpa only [decideEntails, hb, Bool.not_true, Bool.false_or] using
      FiniteRecognition.decideBothSides_iff_entails Q hd hs
  · have hb := (decideSatisfiable_false Q.constraints).mpr hs
    have he := entails_of_unsatisfiable (constructor d) Q hs
    simp [decideEntails, hb, he]

theorem decideEntails_false (Q : Query n d) (hd : 0 < d) :
    decideEntails Q = false ↔
      ∃ ρ : Fin n → Tree d, Satisfies (constructor d) Q.constraints ρ ∧ ¬ ρ Q.left ≤ ρ Q.right := by
  classical
  have hn : ¬ Entails (constructor d) Q ↔
      ∃ ρ : Fin n → Tree d, Satisfies (constructor d) Q.constraints ρ ∧ ¬ ρ Q.left ≤ ρ Q.right := by
    simp [Entails]
  rw [← hn, ← decideEntails_correct Q hd]
  cases decideEntails Q <;> simp

def entailmentDecision (Q : Query n d) (hd : 0 < d) : Decidable (Entails (constructor d) Q) :=
  decidable_of_iff (decideEntails Q = true) (decideEntails_correct Q hd)

theorem false_satisfiable (Q : Query n d) (h : decideEntails Q = false) :
    Satisfiable (constructor d) Q.constraints := by
  apply (decideSatisfiable_correct Q.constraints).mp
  cases hs : decideSatisfiable Q.constraints <;> simp_all [decideEntails]

theorem false_unsafe_word (Q : Query n d) (hd : 0 < d) (h : decideEntails Q = false) :
    ∃ s w, FinitePathSafetyDecision.decideSafe Q s w = false := by
  classical
  have hn : ¬ Entails (constructor d) Q := by
    rw [← decideEntails_correct Q hd]
    simp [h]
  rw [entails_iff_all_safe] at hn
  obtain ⟨s,w,hw⟩ : ∃ s w, ¬ QuerySafe Q s w := by simpa only [not_forall] using hn
  exact ⟨s,w,(FinitePathSafetyDecision.decideSafe_false Q s w).mpr hw⟩

theorem decideEntails_rights (Q : Query n d) : decideEntails Q =
    (!decideSatisfiable Q.constraints ||
      (ForwardTableAutomaton.decideUniversal (tables Q) .right &&
        ForwardTableAutomaton.decideUniversal (tables (SubtypeDuality.dualQuery Q)) .right)) := by
  rw [decideEntails, ConstraintForwardDuality.decideBothSides_rights]

theorem reflexive_decision (φ : Constraints n d) (x : Fin n) (hd : 0 < d) :
    decideEntails ⟨φ,x,x⟩ = true :=
  (decideEntails_correct _ hd).mpr (fun _ _ => le_rfl)

def emptyQuery (d : Nat) : Query 2 d := ⟨⟨[],[],[],[]⟩,0,1⟩

/-- An unrestricted-arity negative family, with actual finite top/bottom
values. The final correctness statement is not vacuous through UNSAT. -/
theorem emptyQuery_false (hd : 0 < d) : decideEntails (emptyQuery d) = false := by
  apply (decideEntails_false (emptyQuery d) hd).mpr
  refine ⟨fun x => if x = 0 then Tree.top else Tree.bot, ?_, ?_⟩
  · simp [Satisfies, emptyQuery]
  · change ¬ Below Tree.top Tree.bot
    intro h; cases h

end NSSE.FiniteEntailmentDecision
