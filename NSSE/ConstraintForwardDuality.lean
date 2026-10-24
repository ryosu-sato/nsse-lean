import NSSE.ForwardTableDuality
import NSSE.ConstraintForwardTables

/-! # The computed original tables and both actual languages are dual

Every Boolean table equality follows from exact computed Support. No table,
language equivalence, or semantic recognition is supplied by the caller.
-/

namespace NSSE.ConstraintForwardDuality

open SubtypeConstraints SubtypeDuality ConstraintForwardTables ForwardTableAutomaton

variable {n d : Nat}

private theorem bool_eq (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

theorem tables_dual (Q : Query n d) : tables (dualQuery Q) = ForwardTableDuality.dual (tables Q) := by
  have hleft : (tables (dualQuery Q)).queryLeft = (ForwardTableDuality.dual (tables Q)).queryLeft := rfl
  have hright : (tables (dualQuery Q)).queryRight = (ForwardTableDuality.dual (tables Q)).queryRight := rfl
  have hu : (tables (dualQuery Q)).upper = (ForwardTableDuality.dual (tables Q)).upper := by
    funext a i b
    apply bool_eq
    change (tables (dualQuery Q)).upper a i b = true ↔ (tables Q).lower a i b = true
    rw [upper_correct, lower_correct]
    exact SubtypeDuality.upper_dual Q.constraints a i b
  have hl : (tables (dualQuery Q)).lower = (ForwardTableDuality.dual (tables Q)).lower := by
    funext a i b
    apply bool_eq
    change (tables (dualQuery Q)).lower a i b = true ↔ (tables Q).upper a i b = true
    rw [lower_correct, upper_correct]
    exact SubtypeDuality.lower_dual Q.constraints a i b
  have hb : (tables (dualQuery Q)).bot = (ForwardTableDuality.dual (tables Q)).bot := by
    funext a
    apply bool_eq
    change (tables (dualQuery Q)).bot a = true ↔ (tables Q).top a = true
    rw [bot_correct, top_correct]
    exact SubtypeDuality.bot_dual Q.constraints a
  have ht : (tables (dualQuery Q)).top = (ForwardTableDuality.dual (tables Q)).top := by
    funext a
    apply bool_eq
    change (tables (dualQuery Q)).top a = true ↔ (tables Q).bot a = true
    rw [top_correct, bot_correct]
    exact SubtypeDuality.top_dual Q.constraints a
  have hs : (tables (dualQuery Q)).le = (ForwardTableDuality.dual (tables Q)).le := by
    funext a b
    apply bool_eq
    change (tables (dualQuery Q)).le a b = true ↔ (tables Q).le b a = true
    rw [le_correct, le_correct]
    exact support_dual Q.constraints a b
  cases h₁ : tables (dualQuery Q)
  cases h₂ : ForwardTableDuality.dual (tables Q)
  simp_all

@[simp] theorem accepts_dual (Q : Query n d) (s : Side) (w : List (Fin d)) :
    ForwardCapAutomaton.Accepts (automaton (dualQuery Q) (opposite s)) w ↔
      ForwardCapAutomaton.Accepts (automaton Q s) w := by
  simp only [automaton, tables_dual, ForwardTableDuality.accepts_dual]

@[simp] theorem universal_dual (Q : Query n d) (s : Side) :
    ForwardCapAutomaton.Universal (automaton (dualQuery Q) (opposite s)) ↔
      ForwardCapAutomaton.Universal (automaton Q s) := by
  simp only [ForwardCapAutomaton.Universal, accepts_dual]

theorem decideBothSides_rights (Q : Query n d) : decideBothSides Q =
    (ForwardTableAutomaton.decideUniversal (tables Q) .right &&
      ForwardTableAutomaton.decideUniversal (tables (dualQuery Q)) .right) := by
  have h : ForwardTableAutomaton.decideUniversal (tables (dualQuery Q)) .right =
      ForwardTableAutomaton.decideUniversal (tables Q) .left := by
    rw [tables_dual]
    exact ForwardTableDuality.decideUniversal_dual (tables Q) .left
  simp only [decideBothSides, h, Bool.and_comm]

end NSSE.ConstraintForwardDuality
