import NSSE.ContraTermFlattening
import NSSE.ContraSoundness
import NSSE.ContraFiniteSatisfiability

/-! # Term-input decisions for the contravariant signature (S7 part 1)

Input: ORIGINAL nested finite terms (`SubtypeTerms.Query n d`, premises `≤` and `=`),
one constructor of arity `d ≥ 1` with polarity vector `POL`.

Certified here, for term input:

* satisfiability decisions with full correctness: arbitrary and regular trees
  (`termDecideSatisfiable`, via `ContraSatisfiability.decideSatisfiable_correct`), finite
  trees (`termDecideFiniteSatisfiable`, via
  `ContraFiniteSatisfiability.decideFiniteSatisfiable_correct`);
* entailment candidates with SOUNDNESS only: `termDecideEntails := decideEntails ∘ flat`
  (arbitrary, regular, finite trees) and `termDecideFiniteEntails` (finite trees, with the
  finite satisfiability test);
* transfer theorems: any correctness theorem for the flat decision on the flattened query
  (as stage S4 is to provide) gives correctness for term input, and a flat countermodel
  restricts to a term countermodel.

COMPLETENESS IS NOT CLAIMED: it is stage S4.
-/

namespace NSSE.ContraTermDecision

open SubtypeTerms (Term Query)
open SubtypeTermLayout (layout)
open ContraTrees ContraFiniteTrees ContraRegularTrees ContraConstraints
open ContraTermSemantics ContraTermFlattening

variable {n d : Nat} {POL : Polarity d}

/-- The flat query of a term query, at the first position (`d ≥ 1`). -/
def flat (POL : Polarity d) (Q : Query n d) (hd : 0 < d) :
    SubtypeConstraints.Query (layout Q).count d :=
  flatten POL Q ⟨0, hd⟩

/-! ## Flat ⇔ term, for the three tree kinds -/

theorem flat_satisfiable_iff (Q : Query n d) (hd : 0 < d) :
    ContraConstraints.Satisfiable (treeConstructor POL) (flat POL Q hd).constraints ↔
      ContraTermSemantics.Satisfiable (treeConstructor POL) Q :=
  satisfiable_iff _ Q _

theorem flat_regularSatisfiable_iff (Q : Query n d) (hd : 0 < d) :
    ContraConstraints.RegularSatisfiable POL (flat POL Q hd).constraints ↔
      ContraTermSemantics.RegularSatisfiable POL Q :=
  regularSatisfiable_iff Q _

theorem flat_finiteSatisfiable_iff (Q : Query n d) (hd : 0 < d) :
    ContraConstraints.Satisfiable (finiteConstructor POL) (flat POL Q hd).constraints ↔
      ContraTermSemantics.Satisfiable (finiteConstructor POL) Q :=
  satisfiable_iff _ Q _

theorem flat_entails_iff (Q : Query n d) (hd : 0 < d) :
    ContraConstraints.Entails (treeConstructor POL) (flat POL Q hd) ↔
      ContraTermSemantics.Entails (treeConstructor POL) Q :=
  entails_iff _ Q _

theorem flat_regularEntails_iff (Q : Query n d) (hd : 0 < d) :
    ContraConstraints.RegularEntails POL (flat POL Q hd) ↔
      ContraTermSemantics.RegularEntails POL Q :=
  regularEntails_iff Q _

theorem flat_finiteEntails_iff (Q : Query n d) (hd : 0 < d) :
    ContraConstraints.Entails (finiteConstructor POL) (flat POL Q hd) ↔
      ContraTermSemantics.Entails (finiteConstructor POL) Q :=
  entails_iff _ Q _

/-! ## Satisfiability: full correctness for term input -/

def termDecideSatisfiable (POL : Polarity d) (Q : Query n d) (hd : 0 < d) : Bool :=
  ContraSatisfiability.decideSatisfiable POL (flat POL Q hd).constraints

def termDecideFiniteSatisfiable (POL : Polarity d) (Q : Query n d) (hd : 0 < d) : Bool :=
  ContraFiniteSatisfiability.decideFiniteSatisfiable POL (flat POL Q hd).constraints

theorem termDecideSatisfiable_correct (Q : Query n d) (hd : 0 < d) :
    termDecideSatisfiable POL Q hd = true ↔
      ContraTermSemantics.Satisfiable (treeConstructor POL) Q :=
  (ContraSatisfiability.decideSatisfiable_correct _).trans (flat_satisfiable_iff Q hd)

theorem termDecideRegularSatisfiable_correct (Q : Query n d) (hd : 0 < d) :
    termDecideSatisfiable POL Q hd = true ↔ ContraTermSemantics.RegularSatisfiable POL Q :=
  (ContraSatisfiability.decideRegularSatisfiable_correct _).trans
    (flat_regularSatisfiable_iff Q hd)

theorem termDecideFiniteSatisfiable_correct (Q : Query n d) (hd : 0 < d) :
    termDecideFiniteSatisfiable POL Q hd = true ↔
      ContraTermSemantics.Satisfiable (finiteConstructor POL) Q :=
  (ContraFiniteSatisfiability.decideFiniteSatisfiable_correct _).trans
    (flat_finiteSatisfiable_iff Q hd)

/-- Corollary: for term input, arbitrary-tree and regular-tree satisfiability agree. -/
theorem term_satisfiable_iff_regular (Q : Query n d) (hd : 0 < d) :
    ContraTermSemantics.Satisfiable (treeConstructor POL) Q ↔
      ContraTermSemantics.RegularSatisfiable POL Q :=
  (termDecideSatisfiable_correct Q hd).symm.trans (termDecideRegularSatisfiable_correct Q hd)

/-- On success, the explicit finite model of the flat system restricts to a finite term
model. -/
theorem termDecideFiniteSatisfiable_model (Q : Query n d) (hd : 0 < d)
    (h : termDecideFiniteSatisfiable POL Q hd = true) :
    ContraTermSemantics.Satisfies (finiteConstructor POL) Q
      ((layout Q).restrict (ContraFiniteSatisfiability.finiteModel POL (flat POL Q hd).constraints)) :=
  (restriction_spec (finiteConstructor POL) Q _ _
    (ContraFiniteSatisfiability.decideFiniteSatisfiable_model _ h)).1

/-! ## Entailment: soundness for term input -/

/-- The candidate entailment decision for term input: the S3 flat candidate on the
flattened query. -/
def termDecideEntails (POL : Polarity d) (Q : Query n d) (hd : 0 < d) : Bool :=
  ContraSoundness.decideEntails POL (flat POL Q hd)

/-- The finite-tree candidate: finitely unsatisfiable, or both Part II sides universal. -/
def termDecideFiniteEntails (POL : Polarity d) (Q : Query n d) (hd : 0 < d) : Bool :=
  !termDecideFiniteSatisfiable POL Q hd || ContraAutomaton.decideBothSides POL (flat POL Q hd)

theorem termDecideEntails_sound (Q : Query n d) (hd : 0 < d)
    (h : termDecideEntails POL Q hd = true) :
    ContraTermSemantics.Entails (treeConstructor POL) Q :=
  (flat_entails_iff Q hd).mp (ContraSoundness.decideEntails_sound _ h)

theorem termDecideEntails_regular_sound (Q : Query n d) (hd : 0 < d)
    (h : termDecideEntails POL Q hd = true) : ContraTermSemantics.RegularEntails POL Q :=
  (flat_regularEntails_iff Q hd).mp (ContraSoundness.decideEntails_regular_sound _ h)

theorem termDecideEntails_finite_sound (Q : Query n d) (hd : 0 < d)
    (h : termDecideEntails POL Q hd = true) :
    ContraTermSemantics.Entails (finiteConstructor POL) Q :=
  (flat_finiteEntails_iff Q hd).mp (ContraSoundness.decideEntails_finite_sound _ h)

theorem termDecideFiniteEntails_sound (Q : Query n d) (hd : 0 < d)
    (h : termDecideFiniteEntails POL Q hd = true) :
    ContraTermSemantics.Entails (finiteConstructor POL) Q := by
  apply (flat_finiteEntails_iff Q hd).mp
  simp only [termDecideFiniteEntails, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · exact ContraFiniteSatisfiability.finiteEntails_of_decide_false _ h
  · exact ContraSoundness.decideBothSides_finite_sound _ h

/-- The arbitrary-tree candidate is at least as strong as the finite one: a positive answer
of `termDecideEntails` is also a positive answer of `termDecideFiniteEntails`. -/
theorem termDecideFiniteEntails_of_termDecideEntails (Q : Query n d) (hd : 0 < d)
    (h : termDecideEntails POL Q hd = true) : termDecideFiniteEntails POL Q hd = true := by
  simp only [termDecideEntails, ContraSoundness.decideEntails, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  simp only [termDecideFiniteEntails, Bool.or_eq_true, Bool.not_eq_true']
  rcases h with h | h
  · left
    cases hf : termDecideFiniteSatisfiable POL Q hd
    · rfl
    · exfalso
      have hs := ContraTermSemantics.satisfiable_of_regularSatisfiable
        (ContraTermSemantics.regularSatisfiable_of_finite
          ((termDecideFiniteSatisfiable_correct Q hd).mp hf))
      have := (termDecideSatisfiable_correct (POL := POL) Q hd).mpr hs
      unfold termDecideSatisfiable at this
      rw [h] at this
      exact Bool.false_ne_true this
  · exact Or.inr h

/-! ## Transfer of flat correctness to term input (interface for S4) -/

/-- Any Boolean decider that is correct for the flattened query is correct for the term
query (arbitrary trees). -/
theorem term_correct_of_flat (Q : Query n d) (hd : 0 < d) (b : Bool)
    (h : b = true ↔ ContraConstraints.Entails (treeConstructor POL) (flat POL Q hd)) :
    b = true ↔ ContraTermSemantics.Entails (treeConstructor POL) Q :=
  h.trans (flat_entails_iff Q hd)

theorem term_regular_correct_of_flat (Q : Query n d) (hd : 0 < d) (b : Bool)
    (h : b = true ↔ ContraConstraints.RegularEntails POL (flat POL Q hd)) :
    b = true ↔ ContraTermSemantics.RegularEntails POL Q :=
  h.trans (flat_regularEntails_iff Q hd)

theorem term_finite_correct_of_flat (Q : Query n d) (hd : 0 < d) (b : Bool)
    (h : b = true ↔ ContraConstraints.Entails (finiteConstructor POL) (flat POL Q hd)) :
    b = true ↔ ContraTermSemantics.Entails (finiteConstructor POL) Q :=
  h.trans (flat_finiteEntails_iff Q hd)

/-- **Transfer (pointwise).** Correctness of `decideEntails` on the flattened query gives
correctness of `termDecideEntails` on the term query. -/
theorem termDecideEntails_correct_of_flat (Q : Query n d) (hd : 0 < d)
    (h : ContraSoundness.decideEntails POL (flat POL Q hd) = true ↔
      ContraConstraints.Entails (treeConstructor POL) (flat POL Q hd)) :
    termDecideEntails POL Q hd = true ↔ ContraTermSemantics.Entails (treeConstructor POL) Q :=
  term_correct_of_flat Q hd _ h

/-- **Transfer (uniform).** The exact shape S4 is to provide —
`decideEntails POL Q' = true ↔ Entails (treeConstructor POL) Q'` for every flat query — gives
correctness for every term query. -/
theorem termDecideEntails_correct_of_flat_all
    (h : ∀ (m : Nat) (Q' : SubtypeConstraints.Query m d),
      ContraSoundness.decideEntails POL Q' = true ↔ ContraConstraints.Entails (treeConstructor POL) Q')
    (Q : Query n d) (hd : 0 < d) :
    termDecideEntails POL Q hd = true ↔ ContraTermSemantics.Entails (treeConstructor POL) Q :=
  termDecideEntails_correct_of_flat Q hd (h _ _)

theorem termDecideEntails_regular_correct_of_flat (Q : Query n d) (hd : 0 < d)
    (h : ContraSoundness.decideEntails POL (flat POL Q hd) = true ↔
      ContraConstraints.RegularEntails POL (flat POL Q hd)) :
    termDecideEntails POL Q hd = true ↔ ContraTermSemantics.RegularEntails POL Q :=
  term_regular_correct_of_flat Q hd _ h

theorem termDecideFiniteEntails_correct_of_flat (Q : Query n d) (hd : 0 < d)
    (h : (!ContraFiniteSatisfiability.decideFiniteSatisfiable POL (flat POL Q hd).constraints ||
        ContraAutomaton.decideBothSides POL (flat POL Q hd)) = true ↔
      ContraConstraints.Entails (finiteConstructor POL) (flat POL Q hd)) :
    termDecideFiniteEntails POL Q hd = true ↔
      ContraTermSemantics.Entails (finiteConstructor POL) Q :=
  term_finite_correct_of_flat Q hd _ h

/-- With the S3 completeness target `Complete` on both sides of the flattened query, the
term decision is correct (arbitrary trees). -/
theorem termDecideEntails_correct_of_complete (Q : Query n d) (hd : 0 < d)
    (hl : ContraSoundness.Complete POL (flat POL Q hd) .left)
    (hr : ContraSoundness.Complete POL (flat POL Q hd) .right) :
    termDecideEntails POL Q hd = true ↔ ContraTermSemantics.Entails (treeConstructor POL) Q :=
  termDecideEntails_correct_of_flat Q hd
    (ContraSoundness.decideEntails_correct_of_complete _ hl hr)

/-! ## Countermodels: flat ⇒ term -/

theorem term_countermodel_of_flat {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]
    (F : ContraConstructor T POL) (Q : Query n d) (hd : 0 < d) (σ : Fin (layout Q).count → T)
    (hσ : ContraConstraints.Satisfies F (flat POL Q hd).constraints σ)
    (hn : ¬ σ (flat POL Q hd).left ≤ σ (flat POL Q hd).right) :
    ContraTermSemantics.Satisfies F Q ((layout Q).restrict σ) ∧
      ¬ eval F ((layout Q).restrict σ) Q.left ≤ eval F ((layout Q).restrict σ) Q.right := by
  obtain ⟨ho, hl, hr⟩ := restriction_spec F Q _ σ hσ
  refine ⟨ho, ?_⟩
  rw [hl, hr]
  exact hn

theorem term_regular_countermodel_of_flat (Q : Query n d) (hd : 0 < d)
    (σ : Fin (layout Q).count → CTree POL) (hr : ∀ x, CRegular (σ x))
    (hσ : ContraConstraints.Satisfies (treeConstructor POL) (flat POL Q hd).constraints σ)
    (hn : ¬ σ (flat POL Q hd).left ≤ σ (flat POL Q hd).right) :
    (∀ x, CRegular ((layout Q).restrict σ x)) ∧
      ContraTermSemantics.Satisfies (treeConstructor POL) Q ((layout Q).restrict σ) ∧
      ¬ eval (treeConstructor POL) ((layout Q).restrict σ) Q.left ≤
        eval (treeConstructor POL) ((layout Q).restrict σ) Q.right :=
  ⟨fun _ => hr _, term_countermodel_of_flat (treeConstructor POL) Q hd σ hσ hn⟩

end NSSE.ContraTermDecision
