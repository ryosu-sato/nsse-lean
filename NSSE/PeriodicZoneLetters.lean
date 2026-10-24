import NSSE.ParameterizedIntervalAgreement
import NSSE.PoweredStatePresburger

/-!
# Letter tables in a periodic zone

At an affine position inside repetitions of one fixed nonempty word, the
letter depends only on the position modulo the word length. The resulting
finite residue table is Presburger.
-/

namespace NSSE

universe u

def periodicLetter
    (word : Word α) (hword : word ≠ [])
    (position : Nat) : α :=
  word.get
    ⟨position % word.length,
      Nat.mod_lt _ (List.length_pos_iff.mpr hword)⟩

noncomputable def periodicLetterFormula
    (word : Word α)
    (expression : NatLinearExpr arity)
    (letter : α) :
    NatPresburger arity := by
  classical
  exact
    NatPresburger.disjoin <|
      (List.range word.length).filter
        (fun residue =>
          decide (word[residue]? = some letter)) |>.map
        (fun residue =>
          .congruent expression (.const residue)
            word.length)

theorem periodicLetterFormula_correct
    (word : Word α) (hword : word ≠ [])
    (expression : NatLinearExpr arity)
    (letter : α)
    (valuation : Fin arity → Nat) :
    (periodicLetterFormula word expression letter).Eval
        valuation ↔
      periodicLetter word hword
        (expression.Eval valuation) = letter := by
  classical
  unfold periodicLetterFormula
  rw [NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map, List.mem_filter,
      List.mem_range] at hformula
    obtain ⟨residue, ⟨hresidueRange, hletter⟩,
      rfl⟩ := hformula
    have hresidueMod :
        residue % word.length = residue :=
      Nat.mod_eq_of_lt hresidueRange
    have heq :
        expression.Eval valuation % word.length =
          residue := by
      simpa [NatPresburger.Eval,
        NatLinearExpr.eval_const, hresidueMod] using heval
    have hget :
        word[residue]? = some letter :=
      of_decide_eq_true hletter
    have hgetElem :
        word.get ⟨residue, hresidueRange⟩ = letter := by
      simpa [List.getElem?_eq_getElem hresidueRange] using hget
    unfold periodicLetter
    simpa [heq] using hgetElem
  · intro hletter
    let residue :=
      expression.Eval valuation % word.length
    have hresidueRange :
        residue < word.length :=
      Nat.mod_lt _
        (List.length_pos_iff.mpr hword)
    have hget :
        word[residue]? = some letter := by
      rw [List.getElem?_eq_getElem hresidueRange]
      unfold periodicLetter at hletter
      simpa [residue] using hletter
    refine ⟨.congruent expression (.const residue)
        word.length, ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨residue, ?_, rfl⟩
      apply List.mem_filter.mpr
      exact ⟨List.mem_range.mpr hresidueRange,
        decide_eq_true hget⟩
    · simp [NatPresburger.Eval,
        NatLinearExpr.eval_const, residue,
        Nat.mod_eq_of_lt hresidueRange]

/-- Equality of two affine positions in two fixed periodic zones is a
finite disjunction over their common letters. -/
noncomputable def periodicZonesEqualFormula
    [Fintype α]
    (leftWord rightWord : Word α)
    (leftExpression rightExpression :
      NatLinearExpr arity) :
    NatPresburger arity :=
  NatPresburger.disjoin <|
    Finset.univ.toList.map fun letter =>
      .conj
        (periodicLetterFormula leftWord
          leftExpression letter)
        (periodicLetterFormula rightWord
          rightExpression letter)

theorem periodicZonesEqualFormula_correct
    [Fintype α]
    (leftWord rightWord : Word α)
    (hleft : leftWord ≠ [])
    (hright : rightWord ≠ [])
    (leftExpression rightExpression :
      NatLinearExpr arity)
    (valuation : Fin arity → Nat) :
    (periodicZonesEqualFormula leftWord rightWord
        leftExpression rightExpression).Eval valuation ↔
      periodicLetter leftWord hleft
          (leftExpression.Eval valuation) =
        periodicLetter rightWord hright
          (rightExpression.Eval valuation) := by
  classical
  unfold periodicZonesEqualFormula
  rw [NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and] at hformula
    obtain ⟨letter, rfl⟩ := hformula
    exact
      ((periodicLetterFormula_correct leftWord hleft
        leftExpression letter valuation).1 heval.1).trans
      ((periodicLetterFormula_correct rightWord hright
        rightExpression letter valuation).1 heval.2).symm
  · intro heq
    let letter :=
      periodicLetter leftWord hleft
        (leftExpression.Eval valuation)
    refine ⟨.conj
        (periodicLetterFormula leftWord
          leftExpression letter)
        (periodicLetterFormula rightWord
          rightExpression letter), ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨letter, ?_, rfl⟩
      simp
    · constructor
      · exact
          (periodicLetterFormula_correct leftWord hleft
            leftExpression letter valuation).2 rfl
      · apply
          (periodicLetterFormula_correct rightWord hright
            rightExpression letter valuation).2
        exact heq.symm

noncomputable def periodicZonesPointPredicate
    [Fintype α]
    (leftWord rightWord : Word α)
    (hleft : leftWord ≠ [])
    (hright : rightWord ≠ [])
    (leftExpression rightExpression :
      NatLinearExpr (arity + 1)) :
    PresburgerPointPredicate arity where
  relation := fun valuation position =>
    periodicLetter leftWord hleft
        (leftExpression.Eval
          (NatPresburger.extendValuation valuation position)) =
      periodicLetter rightWord hright
        (rightExpression.Eval
          (NatPresburger.extendValuation valuation position))
  formula :=
    periodicZonesEqualFormula leftWord rightWord
      leftExpression rightExpression
  correct := by
    intro valuation position
    exact periodicZonesEqualFormula_correct
      leftWord rightWord hleft hright
      leftExpression rightExpression
      (NatPresburger.extendValuation valuation position)

/-- Equality throughout one phase region of two fixed periodic zones is
Presburger. -/
theorem periodicZoneInterval_presburger
    [Fintype α]
    (leftWord rightWord : Word α)
    (hleft : leftWord ≠ [])
    (hright : rightWord ≠ [])
    (leftExpression rightExpression :
      NatLinearExpr (arity + 1))
    (lower upper : NatLinearExpr arity) :
    ∃ formula : NatPresburger arity,
      ∀ valuation,
        formula.Eval valuation ↔
          (periodicZonesPointPredicate
            leftWord rightWord hleft hright
            leftExpression rightExpression).OnInterval
              lower upper valuation := by
  let point :=
    periodicZonesPointPredicate
      leftWord rightWord hleft hright
      leftExpression rightExpression
  exact ⟨point.intervalFormula lower upper,
    point.intervalFormula_correct lower upper⟩

end NSSE
