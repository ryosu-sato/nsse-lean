import NSSE.RegularSubtypeRecognition

/-! # Full original four-form entailment over regular AND arbitrary trees

The final input Boolean has no original SAT/recognition/bound premise.
Original clashes handle vacuous entailment; the two computed universality
tests handle the satisfiable branch. The semantics is actual label order.
-/

namespace NSSE.RegularEntailmentDecision

open AbsorbingSubtypeTrees AbsorbingSubtypeSafety RegularSubtypeTrees
open SubtypeConstraints SubtypeLabelClashes ConstraintForwardTables

variable {n d : Nat}

def decideEntails (Q : Query n d) : Bool := labelClashBool Q.constraints || decideBothSides Q

theorem decideEntails_correct (Q : Query n d) (hd : 0 < d) :
    decideEntails Q = true ↔ Entails (constructor d) Q := by
  classical
  by_cases hc : LabelClash Q.constraints
  · have hb := (labelClashBool_correct Q.constraints).mpr hc
    have hn : ¬ Satisfiable (constructor d) Q.constraints :=
      fun hs => (RegularSubtypeModel.satisfiable_iff Q.constraints).mp hs hc
    have he := entails_of_unsatisfiable (constructor d) Q hn
    simp [decideEntails, hb, he]
  · have hb : labelClashBool Q.constraints = false := by
      cases hb : labelClashBool Q.constraints
      · rfl
      · exact False.elim (hc ((labelClashBool_correct Q.constraints).mp hb))
    simpa only [decideEntails, hb, Bool.false_or] using
      RegularSubtypeRecognition.decideBothSides_iff_entails Q hd hc

theorem decideRegularEntails_correct (Q : Query n d) (hd : 0 < d) :
    decideEntails Q = true ↔ RegularEntails Q :=
  (decideEntails_correct Q hd).trans (RegularPathSafetyDecision.regular_entails_iff_all Q).symm

theorem decideEntails_false (Q : Query n d) (hd : 0 < d) :
    decideEntails Q = false ↔
      ∃ ρ : Fin n → Tree d, Satisfies (constructor d) Q.constraints ρ ∧ ¬ ρ Q.left ≤ ρ Q.right := by
  classical
  have hn : ¬ Entails (constructor d) Q ↔
      ∃ ρ : Fin n → Tree d, Satisfies (constructor d) Q.constraints ρ ∧ ¬ ρ Q.left ≤ ρ Q.right := by
    simp [Entails]
  rw [← hn, ← decideEntails_correct Q hd]
  cases decideEntails Q <;> simp

theorem decideRegularEntails_false (Q : Query n d) (hd : 0 < d) :
    decideEntails Q = false ↔
      ∃ ρ : Fin n → Tree d, (∀ x, Regular (ρ x)) ∧
        Satisfies (constructor d) Q.constraints ρ ∧ ¬ ρ Q.left ≤ ρ Q.right := by
  classical
  have hn : ¬ RegularEntails Q ↔
      ∃ ρ : Fin n → Tree d, (∀ x, Regular (ρ x)) ∧
        Satisfies (constructor d) Q.constraints ρ ∧ ¬ ρ Q.left ≤ ρ Q.right := by
    simp [RegularEntails]
  rw [← hn, ← decideRegularEntails_correct Q hd]
  cases decideEntails Q <;> simp

def entailmentDecision (Q : Query n d) (hd : 0 < d) : Decidable (Entails (constructor d) Q) :=
  decidable_of_iff (decideEntails Q = true) (decideEntails_correct Q hd)

def regularEntailmentDecision (Q : Query n d) (hd : 0 < d) : Decidable (RegularEntails Q) :=
  decidable_of_iff (decideEntails Q = true) (decideRegularEntails_correct Q hd)

theorem false_unsafe_word (Q : Query n d) (hd : 0 < d) (h : decideEntails Q = false) :
    ∃ s w, RegularPathSafetyDecision.decideSafe Q s w = false := by
  classical
  have hn : ¬ Entails (constructor d) Q := by
    rw [← decideEntails_correct Q hd]
    simp [h]
  rw [entails_iff_all_safe] at hn
  obtain ⟨s,w,hw⟩ : ∃ s w, ¬ QuerySafe Q s w := by simpa only [not_forall] using hn
  exact ⟨s,w,(RegularPathSafetyDecision.decideSafe_false Q s w).mpr hw⟩

theorem reflexive_decision (φ : Constraints n d) (x : Fin n) (hd : 0 < d) :
    decideEntails ⟨φ,x,x⟩ = true := (decideEntails_correct _ hd).mpr (fun _ _ => le_rfl)

def emptyQuery (d : Nat) : Query 2 d := ⟨⟨[],[],[],[]⟩,0,1⟩

/-- A negative family for every positive arity, not a vacuous SAT premise. -/
theorem emptyQuery_false (hd : 0 < d) : decideEntails (emptyQuery d) = false := by
  apply (decideEntails_false (emptyQuery d) hd).mpr
  refine ⟨fun x => if x = 0 then ⊤ else ⊥, ?_, ?_⟩
  · simp [Satisfies, emptyQuery]
  · simp only [emptyQuery, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    intro h
    exact (by decide : ¬ (2 : Label) ≤ 0) (h [])

end NSSE.RegularEntailmentDecision
