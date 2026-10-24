import NSSE.CodedTermEntailment

/-! # The certified decision is not vacuous: it separates inputs

`CodedTermEntailment.finite_correct` and friends are equivalences, so any
concrete entailment fact and any concrete NON-entailment fact become statements
about what the decision returns on the corresponding BIT STRING — without
running it (the full pipeline is not practically executable, as recorded since
v1358).

This file supplies both directions: reflexivity, transport along a premise and
congruence under the constructor are entailed; a bare `x ≤ y` and `⊤ ≤ ⊥` are
not. The non-entailments need only that the order is nontrivial, which is
proved for both concrete tree semantics.
-/

namespace NSSE.CodedDecisionExamples

open SubtypeConstraints (Constructor)
open SubtypeTerms RawQueryCodec CodedQueryConversion CodedTermEntailment

variable {d : Nat}

/-! ## Five small queries -/

def Qrefl : Query 1 d := ⟨[],.var 0,.var 0⟩
def Qsep : Query 2 d := ⟨[],.var 0,.var 1⟩
def Qtrans : Query 2 d := ⟨[.le (.var 0) (.var 1)],.var 0,.var 1⟩
def Qnode : Query 2 d := ⟨[.le (.var 0) (.var 1)],.node (fun _ => .var 0),.node (fun _ => .var 1)⟩
def Qtb : Query 1 d := ⟨[],.top,.bot⟩

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem entails_refl (F : Constructor T d) : Entails F (Qrefl (d := d)) := by
  intro ρ _
  exact le_rfl

theorem entails_trans (F : Constructor T d) : Entails F (Qtrans (d := d)) := by
  intro ρ h
  have hle := h (Literal.le (Term.var 0) (Term.var 1)) (by simp [Qtrans])
  simpa only [Holds] using hle

theorem entails_node (F : Constructor T d) : Entails F (Qnode (d := d)) := by
  intro ρ h
  have hle := h (Literal.le (Term.var 0) (Term.var 1)) (by simp [Qnode])
  simp only [Holds] at hle
  simp only [Qnode, eval]
  exact (F.le_iff _ _).mpr (fun _ => hle)

/-- A bare inequality between distinct variables is not entailed, as soon as
the order is nontrivial. -/
theorem not_entails_sep (F : Constructor T d) (h : ¬ (⊤ : T) ≤ (⊥ : T)) :
    ¬ Entails F (Qsep (d := d)) := by
  intro hent
  exact h (hent (fun x => if x = 0 then ⊤ else ⊥) (by simp [Qsep, Satisfies]))

theorem not_entails_tb (F : Constructor T d) (h : ¬ (⊤ : T) ≤ (⊥ : T)) :
    ¬ Entails F (Qtb (d := d)) := by
  intro hent
  exact h (hent (fun _ => ⊥) (by simp [Qtb, Satisfies]))

end Semantics

/-! ## Both concrete tree orders are nontrivial -/

theorem finite_top_not_le_bot : ¬ (⊤ : FiniteSubtypeTrees.Tree d) ≤ (⊥ : FiniteSubtypeTrees.Tree d) := by
  intro h
  cases h

theorem absorbing_top_not_le_bot :
    ¬ (⊤ : AbsorbingSubtypeTrees.Tree d) ≤ (⊥ : AbsorbingSubtypeTrees.Tree d) := by
  intro h
  have := h []
  simp only [AbsorbingSubtypeTrees.top_label, AbsorbingSubtypeTrees.bot_label] at this
  exact absurd this (by decide)

/-! ## What the decision returns on the corresponding bit strings -/

theorem decide_refl_true (hd : 0 < d) :
    (decideFinite d (encQuery (rawOfQuery (Qrefl (d := d)))) hd).1 = some true :=
  (finite_correct Qrefl hd).mpr (entails_refl _)

theorem decide_trans_true (hd : 0 < d) :
    (decideFinite d (encQuery (rawOfQuery (Qtrans (d := d)))) hd).1 = some true :=
  (finite_correct Qtrans hd).mpr (entails_trans _)

theorem decide_node_true (hd : 0 < d) :
    (decideFinite d (encQuery (rawOfQuery (Qnode (d := d)))) hd).1 = some true :=
  (finite_correct Qnode hd).mpr (entails_node _)

theorem decide_sep_not_true (hd : 0 < d) :
    (decideFinite d (encQuery (rawOfQuery (Qsep (d := d)))) hd).1 ≠ some true := by
  intro h
  exact not_entails_sep _ finite_top_not_le_bot ((finite_correct Qsep hd).mp h)

theorem decide_tb_not_true (hd : 0 < d) :
    (decideFinite d (encQuery (rawOfQuery (Qtb (d := d)))) hd).1 ≠ some true := by
  intro h
  exact not_entails_tb _ finite_top_not_le_bot ((finite_correct Qtb hd).mp h)

/-! The same separation for the arbitrary-tree and regular-tree decision. -/

theorem decideAll_refl_true (hd : 0 < d) :
    (decideAll d (encQuery (rawOfQuery (Qrefl (d := d)))) hd).1 = some true :=
  (arbitrary_correct Qrefl hd).mpr (entails_refl _)

theorem decideAll_node_true (hd : 0 < d) :
    (decideAll d (encQuery (rawOfQuery (Qnode (d := d)))) hd).1 = some true :=
  (arbitrary_correct Qnode hd).mpr (entails_node _)

theorem decideAll_tb_not_true (hd : 0 < d) :
    (decideAll d (encQuery (rawOfQuery (Qtb (d := d)))) hd).1 ≠ some true := by
  intro h
  exact not_entails_tb _ absorbing_top_not_le_bot ((arbitrary_correct Qtb hd).mp h)

theorem decideAll_regular_tb_not_true (hd : 0 < d) :
    ¬ SubtypeTermSemantics.RegularEntails (Qtb (d := d)) := by
  intro h
  exact not_entails_tb _ absorbing_top_not_le_bot
    ((TermEntailmentDecision.regular_entails_iff_all Qtb hd).mp h)

/-- The decision is not constant: on two bit strings it returns different
answers, and both are the mathematically correct ones. -/
theorem decision_separates (hd : 0 < d) :
    (decideFinite d (encQuery (rawOfQuery (Qrefl (d := d)))) hd).1 = some true ∧
      (decideFinite d (encQuery (rawOfQuery (Qtb (d := d)))) hd).1 ≠ some true :=
  ⟨decide_refl_true hd,decide_tb_not_true hd⟩

end NSSE.CodedDecisionExamples
