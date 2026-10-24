import NSSE.SubtypeTermSemantics
import NSSE.FiniteEntailmentDecision
import NSSE.RegularEntailmentDecision

/-! # Actual term-input decisions for finite, regular and arbitrary trees

Input premises include inequalities AND equalities between nested finite
terms. These final specifications have no flattening, SAT, model, semantic
transport, acceptance or counterexample-bound premise.
-/

namespace NSSE.TermEntailmentDecision

open SubtypeTerms SubtypeTermLayout SubtypeTermFlattening

variable {n d : Nat}

def flat (Q : Query n d) (hd : 0 < d) : SubtypeConstraints.Query (layout Q).count d :=
  flatten Q ⟨0,hd⟩

def decideFiniteSatisfiable (Q : Query n d) (hd : 0 < d) : Bool :=
  FiniteSubtypeDecision.decideSatisfiable (flat Q hd).constraints

def decideAllSatisfiable (Q : Query n d) (hd : 0 < d) : Bool :=
  RegularSubtypeModel.decideSatisfiable (flat Q hd).constraints

def decideFinite (Q : Query n d) (hd : 0 < d) : Bool :=
  FiniteEntailmentDecision.decideEntails (flat Q hd)

def decideAll (Q : Query n d) (hd : 0 < d) : Bool :=
  RegularEntailmentDecision.decideEntails (flat Q hd)

theorem decideFiniteSatisfiable_correct (Q : Query n d) (hd : 0 < d) :
    decideFiniteSatisfiable Q hd = true ↔ Satisfiable (FiniteSubtypeTrees.constructor d) Q :=
  (FiniteSubtypeDecision.decideSatisfiable_correct _).trans
    (SubtypeTermFlattening.satisfiable_iff (FiniteSubtypeTrees.constructor d) Q ⟨0,hd⟩)

theorem decideAllSatisfiable_correct (Q : Query n d) (hd : 0 < d) :
    decideAllSatisfiable Q hd = true ↔ Satisfiable (AbsorbingSubtypeTrees.constructor d) Q :=
  (RegularSubtypeModel.decideSatisfiable_correct _).trans
    (SubtypeTermFlattening.satisfiable_iff (AbsorbingSubtypeTrees.constructor d) Q ⟨0,hd⟩)

theorem decideRegularSatisfiable_correct (Q : Query n d) (hd : 0 < d) :
    decideAllSatisfiable Q hd = true ↔ SubtypeTermSemantics.RegularSatisfiable Q :=
  (RegularSubtypeModel.decideRegularSatisfiable_correct _).trans
    (SubtypeTermSemantics.regular_satisfiable_iff Q ⟨0,hd⟩)

theorem decideFinite_correct (Q : Query n d) (hd : 0 < d) :
    decideFinite Q hd = true ↔ Entails (FiniteSubtypeTrees.constructor d) Q :=
  (FiniteEntailmentDecision.decideEntails_correct _ hd).trans
    (entails_iff (FiniteSubtypeTrees.constructor d) Q ⟨0,hd⟩)

theorem decideAll_correct (Q : Query n d) (hd : 0 < d) :
    decideAll Q hd = true ↔ Entails (AbsorbingSubtypeTrees.constructor d) Q :=
  (RegularEntailmentDecision.decideEntails_correct _ hd).trans
    (entails_iff (AbsorbingSubtypeTrees.constructor d) Q ⟨0,hd⟩)

theorem decideRegular_correct (Q : Query n d) (hd : 0 < d) :
    decideAll Q hd = true ↔ SubtypeTermSemantics.RegularEntails Q :=
  (RegularEntailmentDecision.decideRegularEntails_correct _ hd).trans
    (SubtypeTermSemantics.regular_entails_iff Q ⟨0,hd⟩)

theorem regular_entails_iff_all (Q : Query n d) (hd : 0 < d) :
    SubtypeTermSemantics.RegularEntails Q ↔ Entails (AbsorbingSubtypeTrees.constructor d) Q :=
  (decideRegular_correct Q hd).symm.trans (decideAll_correct Q hd)

theorem decideFinite_false (Q : Query n d) (hd : 0 < d) :
    decideFinite Q hd = false ↔
      ∃ ρ : Fin n → FiniteSubtypeTrees.Tree d, Satisfies (FiniteSubtypeTrees.constructor d) Q ρ ∧
        ¬ eval (FiniteSubtypeTrees.constructor d) ρ Q.left ≤ eval (FiniteSubtypeTrees.constructor d) ρ Q.right := by
  classical
  have hn := not_congr (decideFinite_correct Q hd)
  simpa [Entails, Bool.not_eq_true] using hn

theorem decideAll_false (Q : Query n d) (hd : 0 < d) :
    decideAll Q hd = false ↔
      ∃ ρ : Fin n → AbsorbingSubtypeTrees.Tree d, Satisfies (AbsorbingSubtypeTrees.constructor d) Q ρ ∧
        ¬ eval (AbsorbingSubtypeTrees.constructor d) ρ Q.left ≤ eval (AbsorbingSubtypeTrees.constructor d) ρ Q.right := by
  classical
  have hn := not_congr (decideAll_correct Q hd)
  simpa [Entails, Bool.not_eq_true] using hn

theorem decideRegular_false (Q : Query n d) (hd : 0 < d) :
    decideAll Q hd = false ↔
      ∃ ρ : Fin n → AbsorbingSubtypeTrees.Tree d, (∀ x, RegularSubtypeTrees.Regular (ρ x)) ∧
        Satisfies (AbsorbingSubtypeTrees.constructor d) Q ρ ∧
        ¬ eval (AbsorbingSubtypeTrees.constructor d) ρ Q.left ≤ eval (AbsorbingSubtypeTrees.constructor d) ρ Q.right := by
  classical
  have hn := not_congr (decideRegular_correct Q hd)
  simpa [SubtypeTermSemantics.RegularEntails, Bool.not_eq_true] using hn

def finiteDecision (Q : Query n d) (hd : 0 < d) : Decidable (Entails (FiniteSubtypeTrees.constructor d) Q) :=
  decidable_of_iff (decideFinite Q hd = true) (decideFinite_correct Q hd)

def allDecision (Q : Query n d) (hd : 0 < d) : Decidable (Entails (AbsorbingSubtypeTrees.constructor d) Q) :=
  decidable_of_iff (decideAll Q hd = true) (decideAll_correct Q hd)

def regularDecision (Q : Query n d) (hd : 0 < d) : Decidable (SubtypeTermSemantics.RegularEntails Q) :=
  decidable_of_iff (decideAll Q hd = true) (decideRegular_correct Q hd)

end NSSE.TermEntailmentDecision
