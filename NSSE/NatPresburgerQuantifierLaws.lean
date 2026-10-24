import NSSE.NatPresburgerFiniteQuantifierElimination

/-!
# Logical laws for moving Presburger quantifiers

These laws distribute existential and universal quantifiers over their
matching Boolean connective and pull formulas independent of the last
variable outside the quantifier.
-/

namespace NSSE

namespace NatPresburger

theorem eval_existsQ_disj_iff
    (left right : NatPresburger (arity + 1))
    (valuation : Fin arity → Nat) :
    (.existsQ (.disj left right) :
      NatPresburger arity).Eval valuation ↔
      (.disj (.existsQ left) (.existsQ right) :
        NatPresburger arity).Eval valuation := by
  simp only [Eval]
  constructor
  · rintro ⟨bound, hleft | hright⟩
    · exact Or.inl ⟨bound, hleft⟩
    · exact Or.inr ⟨bound, hright⟩
  · rintro (⟨bound, hleft⟩ | ⟨bound, hright⟩)
    · exact ⟨bound, Or.inl hleft⟩
    · exact ⟨bound, Or.inr hright⟩

theorem eval_existsQ_conj_weaken_left_iff
    (independent : NatPresburger arity)
    (body : NatPresburger (arity + 1))
    (valuation : Fin arity → Nat) :
    (.existsQ
      (.conj independent.weakenFormula body) :
        NatPresburger arity).Eval valuation ↔
      (.conj independent (.existsQ body) :
        NatPresburger arity).Eval valuation := by
  simp only [Eval]
  constructor
  · rintro ⟨bound, hindependent, hbody⟩
    exact ⟨(independent.eval_weakenFormula_iff
      valuation bound).mp hindependent,
      ⟨bound, hbody⟩⟩
  · rintro ⟨hindependent, bound, hbody⟩
    exact ⟨bound,
      (independent.eval_weakenFormula_iff
        valuation bound).mpr hindependent,
      hbody⟩

theorem eval_existsQ_conj_weaken_right_iff
    (body : NatPresburger (arity + 1))
    (independent : NatPresburger arity)
    (valuation : Fin arity → Nat) :
    (.existsQ
      (.conj body independent.weakenFormula) :
        NatPresburger arity).Eval valuation ↔
      (.conj (.existsQ body) independent :
        NatPresburger arity).Eval valuation := by
  simpa [Eval, and_comm] using
    eval_existsQ_conj_weaken_left_iff
      independent body valuation

theorem standard_forallQ
    (formula : NatPresburger (arity + 1))
    (hstandard : formula.Standard) :
    formula.forallQ.Standard := by
  exact hstandard

theorem eval_forallQ_conj_iff
    (left right : NatPresburger (arity + 1))
    (valuation : Fin arity → Nat) :
    ((.conj left right :
      NatPresburger (arity + 1)).forallQ).Eval valuation ↔
      (.conj left.forallQ right.forallQ :
        NatPresburger arity).Eval valuation := by
  simp only [eval_forallQ_iff, Eval]
  constructor
  · intro hall
    exact ⟨fun bound => (hall bound).1,
      fun bound => (hall bound).2⟩
  · rintro ⟨hleft, hright⟩ bound
    exact ⟨hleft bound, hright bound⟩

theorem eval_forallQ_disj_weaken_left_iff
    (independent : NatPresburger arity)
    (body : NatPresburger (arity + 1))
    (valuation : Fin arity → Nat) :
    ((.disj independent.weakenFormula body :
      NatPresburger (arity + 1)).forallQ).Eval
        valuation ↔
      (.disj independent body.forallQ :
        NatPresburger arity).Eval valuation := by
  simp only [eval_forallQ_iff, Eval]
  constructor
  · intro hall
    by_cases hindependent : independent.Eval valuation
    · exact Or.inl hindependent
    · exact Or.inr (fun bound => by
        rcases hall bound with hweak | hbody
        · exact False.elim (hindependent
            ((independent.eval_weakenFormula_iff
              valuation bound).mp hweak))
        · exact hbody)
  · rintro (hindependent | hbody) bound
    · exact Or.inl
        ((independent.eval_weakenFormula_iff
          valuation bound).mpr hindependent)
    · exact Or.inr (hbody bound)

theorem eval_forallQ_disj_weaken_right_iff
    (body : NatPresburger (arity + 1))
    (independent : NatPresburger arity)
    (valuation : Fin arity → Nat) :
    ((.disj body independent.weakenFormula :
      NatPresburger (arity + 1)).forallQ).Eval
        valuation ↔
      (.disj body.forallQ independent :
        NatPresburger arity).Eval valuation := by
  simp only [eval_forallQ_iff, Eval]
  constructor
  · intro hall
    by_cases hindependent : independent.Eval valuation
    · exact Or.inr hindependent
    · exact Or.inl (fun bound => by
        rcases hall bound with hbody | hweak
        · exact hbody
        · exact False.elim (hindependent
            ((independent.eval_weakenFormula_iff
              valuation bound).mp hweak)))
  · rintro (hbody | hindependent) bound
    · exact Or.inl (hbody bound)
    · exact Or.inr
        ((independent.eval_weakenFormula_iff
          valuation bound).mpr hindependent)

end NatPresburger

end NSSE
