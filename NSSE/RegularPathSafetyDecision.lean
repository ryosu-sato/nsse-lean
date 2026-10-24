import NSSE.AbsorbingUnsafetyCompiler

/-! # Exact given-word safety and same-word regular countermodels

The original compiler syntax, concrete absorbing semantics and computed
lower-set model compose without any SAT, acceptance, model or bound oracle.
This is a given-word decision; full entailment still quantifies over words.
-/

namespace NSSE.RegularPathSafetyDecision

open AbsorbingSubtypeTrees AbsorbingSubtypeSafety RegularSubtypeTrees SubtypeConstraints
open SubtypeLabelClashes ForwardTableAutomaton
open FiniteUnsafetyCompiler (extra old compile)

variable {n d : Nat}

theorem safe_iff_clash (Q : Query n d) (s : Side) (w : List (Fin d)) :
    QuerySafe Q s w ↔ LabelClash (compile Q s w) := by
  classical
  have h := (AbsorbingUnsafetyCompiler.compile_satisfiable_iff Q s w).symm.trans
    (RegularSubtypeModel.satisfiable_iff (compile Q s w))
  simpa only [not_not] using not_congr h

def decideSafe (Q : Query n d) (s : Side) (w : List (Fin d)) : Bool :=
  labelClashBool (compile Q s w)

theorem decideSafe_correct (Q : Query n d) (s : Side) (w : List (Fin d)) :
    decideSafe Q s w = true ↔ QuerySafe Q s w :=
  (labelClashBool_correct _).trans (safe_iff_clash Q s w).symm

theorem decideSafe_false (Q : Query n d) (s : Side) (w : List (Fin d)) :
    decideSafe Q s w = false ↔ ¬ QuerySafe Q s w := by
  rw [← decideSafe_correct]
  cases decideSafe Q s w <;> simp

/-- One finite graph is shared by ALL original variable roots. -/
def graph (Q : Query n d) (s : Side) (w : List (Fin d)) :
    Graph (Finset (Fin (n + extra w))) d := RegularSubtypeModel.graph (compile Q s w)

def root (Q : Query n d) (s : Side) (w : List (Fin d)) (x : Fin n) :
    Finset (Fin (n + extra w)) := SubtypeShapeGrammar.down (compile Q s w) (old w x)

def candidate (Q : Query n d) (s : Side) (w : List (Fin d)) (x : Fin n) : Tree d :=
  (graph Q s w).tree (root Q s w x)

theorem candidate_regular (Q : Query n d) (s : Side) (w : List (Fin d)) (x : Fin n) :
    Regular (candidate Q s w x) := (graph Q s w).regular _

theorem state_count (w : List (Fin d)) :
    Fintype.card (Finset (Fin (n + extra w))) = 2 ^ (n + 2 * w.length + 4) := by
  rw [RegularSubtypeModel.state_count]
  congr 1
  unfold extra
  omega

theorem candidate_of_no_clash (Q : Query n d) (s : Side) (w : List (Fin d))
    (h : ¬ LabelClash (compile Q s w)) :
    Satisfies (constructor d) Q.constraints (candidate Q s w) ∧
      ¬ Safe s (candidate Q s w Q.left) (candidate Q s w Q.right) w :=
  AbsorbingUnsafetyCompiler.compiled_solution_unsafe Q s w _
    (RegularSubtypeModel.model_satisfies (compile Q s w) h)

theorem candidate_correct (Q : Query n d) (s : Side) (w : List (Fin d))
    (h : decideSafe Q s w = false) :
    Satisfies (constructor d) Q.constraints (candidate Q s w) ∧
      ¬ Safe s (candidate Q s w Q.left) (candidate Q s w Q.right) w := by
  apply candidate_of_no_clash
  intro hc
  have hs := (decideSafe_correct Q s w).mpr ((safe_iff_clash Q s w).mpr hc)
  rw [h] at hs
  cases hs

/-- No positive-arity or original SAT premise. Side and word are unchanged. -/
theorem same_word_regularization (Q : Query n d) (s : Side) (w : List (Fin d))
    (ρ : Fin n → Tree d) (hρ : Satisfies (constructor d) Q.constraints ρ)
    (hu : ¬ Safe s (ρ Q.left) (ρ Q.right) w) :
    (∀ x, Regular (candidate Q s w x)) ∧
      Satisfies (constructor d) Q.constraints (candidate Q s w) ∧
      ¬ Safe s (candidate Q s w Q.left) (candidate Q s w Q.right) w := by
  have hn : ¬ QuerySafe Q s w := fun hs => hu (hs ρ hρ)
  exact ⟨candidate_regular Q s w,
    candidate_correct Q s w ((decideSafe_false Q s w).mpr hn)⟩

theorem regular_safe_iff_all (Q : Query n d) (s : Side) (w : List (Fin d)) :
    RegularQuerySafe Q s w ↔ QuerySafe Q s w := by
  classical
  constructor
  · intro hs ρ hρ
    by_contra hu
    obtain ⟨hr,hφ,hbad⟩ := same_word_regularization Q s w ρ hρ hu
    exact hbad (hs _ hr hφ)
  · intro hs ρ _ hρ
    exact hs ρ hρ

theorem decideRegularSafe_correct (Q : Query n d) (s : Side) (w : List (Fin d)) :
    decideSafe Q s w = true ↔ RegularQuerySafe Q s w :=
  (decideSafe_correct Q s w).trans (regular_safe_iff_all Q s w).symm

theorem compile_regular_satisfiable_iff (Q : Query n d) (s : Side) (w : List (Fin d)) :
    RegularSatisfiable (compile Q s w) ↔ ¬ RegularQuerySafe Q s w := by
  rw [RegularSubtypeModel.regular_satisfiable_iff, regular_safe_iff_all, safe_iff_clash]

theorem regular_entails_iff_all (Q : Query n d) :
    RegularEntails Q ↔ Entails (constructor d) Q := by
  simp only [regular_entails_iff_all_safe, entails_iff_all_safe, regular_safe_iff_all]

def safetyDecision (Q : Query n d) (s : Side) (w : List (Fin d)) : Decidable (QuerySafe Q s w) :=
  decidable_of_iff (decideSafe Q s w = true) (decideSafe_correct Q s w)

def regularSafetyDecision (Q : Query n d) (s : Side) (w : List (Fin d)) :
    Decidable (RegularQuerySafe Q s w) :=
  decidable_of_iff (decideSafe Q s w = true) (decideRegularSafe_correct Q s w)

end NSSE.RegularPathSafetyDecision
