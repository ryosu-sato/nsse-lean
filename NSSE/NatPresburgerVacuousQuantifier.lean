import NSSE.NatPresburgerEqualityElimination

/-!
# Eliminating vacuous Presburger quantifiers

A formula may be weakened by adding one unused last variable.  Its
evaluation is independent of that variable, so both existential and
universal quantification over it can be eliminated.
-/

namespace NSSE

namespace NatPresburger

def weakenFormula
    (formula : NatPresburger arity) :
    NatPresburger (arity + 1) :=
  formula.reindex Fin.castSucc

theorem eval_weakenFormula_iff
    (formula : NatPresburger arity)
    (valuation : Fin arity → Nat)
    (bound : Nat) :
    formula.weakenFormula.Eval
        (extendValuation valuation bound) ↔
      formula.Eval valuation := by
  rw [weakenFormula, eval_reindex_iff]
  have hvaluation :
      (fun index =>
        extendValuation valuation bound index.castSucc) =
        valuation := by
    funext index
    simp
  rw [hvaluation]

theorem standard_weakenFormula
    (formula : NatPresburger arity)
    (hstandard : formula.Standard) :
    formula.weakenFormula.Standard := by
  exact formula.standard_substitute hstandard
    (fun index => .varExpr index.castSucc)

theorem eval_existsQ_weakenFormula_iff
    (formula : NatPresburger arity)
    (valuation : Fin arity → Nat) :
    (.existsQ formula.weakenFormula :
      NatPresburger arity).Eval valuation ↔
      formula.Eval valuation := by
  simp only [Eval]
  constructor
  · rintro ⟨bound, heval⟩
    exact (formula.eval_weakenFormula_iff
      valuation bound).mp heval
  · intro heval
    exact ⟨0,
      (formula.eval_weakenFormula_iff
        valuation 0).mpr heval⟩

def forallQ
    (formula : NatPresburger (arity + 1)) :
    NatPresburger arity :=
  .neg (.existsQ (.neg formula))

theorem eval_forallQ_iff
    (formula : NatPresburger (arity + 1))
    (valuation : Fin arity → Nat) :
    formula.forallQ.Eval valuation ↔
      ∀ bound,
        formula.Eval
          (extendValuation valuation bound) := by
  simp [forallQ, Eval]

theorem eval_forallQ_weakenFormula_iff
    (formula : NatPresburger arity)
    (valuation : Fin arity → Nat) :
    formula.weakenFormula.forallQ.Eval valuation ↔
      formula.Eval valuation := by
  rw [eval_forallQ_iff]
  constructor
  · intro hall
    exact (formula.eval_weakenFormula_iff
      valuation 0).mp (hall 0)
  · intro heval bound
    exact (formula.eval_weakenFormula_iff
      valuation bound).mpr heval

end NatPresburger

end NSSE
