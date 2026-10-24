import NSSE.LinearZonePairInterval
import NSSE.PeriodicZoneLetters

/-!
# Letter tables relative to affine zone origins

Local coordinates are represented without subtraction.  In a fixed word,
offset `r` is expressed by `position = origin + r`.  In a periodic word,
residue `r` is expressed by
`position ≡ origin + r (mod word.length)`.
-/

namespace NSSE

noncomputable def fixedRelativeLetterFormula
    (word : Word α)
    (position origin : NatLinearExpr arity)
    (letter : α) :
    NatPresburger arity := by
  classical
  exact NatPresburger.disjoin <|
    (List.range word.length).filter
      (fun offset =>
        decide (word[offset]? = some letter)) |>.map
      (fun offset =>
        .equal position (.add origin (.const offset)))

def FixedRelativeLetterAt
    (word : Word α)
    (position origin : NatLinearExpr arity)
    (letter : α)
    (valuation : Fin arity → Nat) : Prop :=
  ∃ offset,
    offset < word.length ∧
    word[offset]? = some letter ∧
    position.Eval valuation =
      origin.Eval valuation + offset

theorem fixedRelativeLetterFormula_correct
    (word : Word α)
    (position origin : NatLinearExpr arity)
    (letter : α)
    (valuation : Fin arity → Nat) :
    (fixedRelativeLetterFormula word position origin
        letter).Eval valuation ↔
      FixedRelativeLetterAt word position origin
        letter valuation := by
  classical
  unfold fixedRelativeLetterFormula
  rw [NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map, List.mem_filter,
      List.mem_range] at hformula
    obtain ⟨offset, ⟨hoffset, hletter⟩, rfl⟩ :=
      hformula
    refine ⟨offset, hoffset, of_decide_eq_true hletter, ?_⟩
    simpa [NatPresburger.Eval,
      NatLinearExpr.eval_add,
      NatLinearExpr.eval_const] using heval
  · rintro ⟨offset, hoffset, hletter, heq⟩
    refine ⟨.equal position (.add origin (.const offset)),
      ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨offset, ?_, rfl⟩
      exact List.mem_filter.mpr
        ⟨List.mem_range.mpr hoffset, decide_eq_true hletter⟩
    · simpa [NatPresburger.Eval,
        NatLinearExpr.eval_add,
        NatLinearExpr.eval_const] using heq

noncomputable def periodicRelativeLetterFormula
    (word : Word α)
    (position origin : NatLinearExpr arity)
    (letter : α) :
    NatPresburger arity := by
  classical
  exact NatPresburger.disjoin <|
    (List.range word.length).filter
      (fun residue =>
        decide (word[residue]? = some letter)) |>.map
      (fun residue =>
        .congruent position
          (.add origin (.const residue)) word.length)

def PeriodicRelativeLetterAt
    (word : Word α)
    (position origin : NatLinearExpr arity)
    (letter : α)
    (valuation : Fin arity → Nat) : Prop :=
  ∃ residue,
    residue < word.length ∧
    word[residue]? = some letter ∧
    position.Eval valuation % word.length =
      (origin.Eval valuation + residue) % word.length

theorem periodicRelativeLetterFormula_correct
    (word : Word α)
    (position origin : NatLinearExpr arity)
    (letter : α)
    (valuation : Fin arity → Nat) :
    (periodicRelativeLetterFormula word position origin
        letter).Eval valuation ↔
      PeriodicRelativeLetterAt word position origin
        letter valuation := by
  classical
  unfold periodicRelativeLetterFormula
  rw [NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map, List.mem_filter,
      List.mem_range] at hformula
    obtain ⟨residue, ⟨hresidue, hletter⟩, rfl⟩ :=
      hformula
    refine ⟨residue, hresidue,
      of_decide_eq_true hletter, ?_⟩
    simpa [NatPresburger.Eval,
      NatLinearExpr.eval_add,
      NatLinearExpr.eval_const] using heval
  · rintro ⟨residue, hresidue, hletter, heq⟩
    refine ⟨.congruent position
        (.add origin (.const residue)) word.length,
      ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨residue, ?_, rfl⟩
      exact List.mem_filter.mpr
        ⟨List.mem_range.mpr hresidue,
          decide_eq_true hletter⟩
    · simpa [NatPresburger.Eval,
        NatLinearExpr.eval_add,
        NatLinearExpr.eval_const] using heq

end NSSE
