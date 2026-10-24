import NSSE.RelativeZoneLetters

/-!
# Letter formulas for concrete linear-family zones

Initial and separator zones use bounded fixed-word tables. Pump zones use
periodic residue tables. For a direct/shifted pair, equality is the finite
disjunction over a common alphabet letter in the translated coordinates.
-/

namespace NSSE

universe u

namespace LinearWordFamily

def zoneWord
    (family : LinearWordFamily α arity) :
    LinearFamilyZone arity → Word α
  | .initial => family.initial
  | .pump index => family.pump index
  | .separator index => family.separator index

def ZoneRelativeLetterAt
    (family : LinearWordFamily α arity)
    (zone : LinearFamilyZone arity)
    (position origin : NatLinearExpr variableCount)
    (letter : α)
    (valuation : Fin variableCount → Nat) : Prop :=
  match zone with
  | .pump _ =>
      PeriodicRelativeLetterAt (family.zoneWord zone)
        position origin letter valuation
  | _ =>
      FixedRelativeLetterAt (family.zoneWord zone)
        position origin letter valuation

noncomputable def zoneRelativeLetterFormula
    (family : LinearWordFamily α arity)
    (zone : LinearFamilyZone arity)
    (position origin : NatLinearExpr variableCount)
    (letter : α) :
    NatPresburger variableCount :=
  match zone with
  | .pump _ =>
      periodicRelativeLetterFormula (family.zoneWord zone)
        position origin letter
  | _ =>
      fixedRelativeLetterFormula (family.zoneWord zone)
        position origin letter

theorem zoneRelativeLetterFormula_correct
    (family : LinearWordFamily α arity)
    (zone : LinearFamilyZone arity)
    (position origin : NatLinearExpr variableCount)
    (letter : α)
    (valuation : Fin variableCount → Nat) :
    (family.zoneRelativeLetterFormula zone position origin
        letter).Eval valuation ↔
      family.ZoneRelativeLetterAt zone position origin
        letter valuation := by
  cases zone with
  | initial =>
      exact fixedRelativeLetterFormula_correct
        family.initial position origin letter valuation
  | pump index =>
      exact periodicRelativeLetterFormula_correct
        (family.pump index) position origin letter valuation
  | separator index =>
      exact fixedRelativeLetterFormula_correct
        (family.separator index) position origin letter valuation

noncomputable def zonePairLettersEqualFormula
    [Fintype α]
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity) :
    NatPresburger (arity + 1) :=
  NatPresburger.disjoin <|
    Finset.univ.toList.map fun letter =>
      .conj
        (family.zoneRelativeLetterFormula direct
          (.varExpr (Fin.last arity))
          (NatPresburger.weakenExpr
            (family.zoneStartExpression direct))
          letter)
        (family.zoneRelativeLetterFormula shifted
          (.add
            (.varExpr (Fin.last arity))
            (NatPresburger.weakenExpr minuend))
          (.add
            (NatPresburger.weakenExpr
              (family.zoneStartExpression shifted))
            (NatPresburger.weakenExpr subtrahend))
          letter)

theorem eval_zonePairLettersEqualFormula_iff
    [Fintype α]
    (family : LinearWordFamily α arity)
    (direct shifted : LinearFamilyZone arity)
    (minuend subtrahend : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (position : Nat) :
    (family.zonePairLettersEqualFormula direct shifted
        minuend subtrahend).Eval
          (NatPresburger.extendValuation parameters position) ↔
      ∃ letter : α,
        family.ZoneRelativeLetterAt direct
          (.varExpr (Fin.last arity))
          (NatPresburger.weakenExpr
            (family.zoneStartExpression direct))
          letter
          (NatPresburger.extendValuation parameters position) ∧
        family.ZoneRelativeLetterAt shifted
          (.add
            (.varExpr (Fin.last arity))
            (NatPresburger.weakenExpr minuend))
          (.add
            (NatPresburger.weakenExpr
              (family.zoneStartExpression shifted))
            (NatPresburger.weakenExpr subtrahend))
          letter
          (NatPresburger.extendValuation parameters position) := by
  classical
  unfold zonePairLettersEqualFormula
  rw [NatPresburger.eval_disjoin_iff]
  constructor
  · rintro ⟨formula, hformula, heval⟩
    simp only [List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and] at hformula
    obtain ⟨letter, rfl⟩ := hformula
    refine ⟨letter, ?_, ?_⟩
    · exact
        (family.zoneRelativeLetterFormula_correct
          direct _ _ letter _).1 heval.1
    · exact
        (family.zoneRelativeLetterFormula_correct
          shifted _ _ letter _).1 heval.2
  · rintro ⟨letter, hdirect, hshifted⟩
    refine ⟨.conj
        (family.zoneRelativeLetterFormula direct
          (.varExpr (Fin.last arity))
          (NatPresburger.weakenExpr
            (family.zoneStartExpression direct))
          letter)
        (family.zoneRelativeLetterFormula shifted
          (.add
            (.varExpr (Fin.last arity))
            (NatPresburger.weakenExpr minuend))
          (.add
            (NatPresburger.weakenExpr
              (family.zoneStartExpression shifted))
            (NatPresburger.weakenExpr subtrahend))
          letter), ?_, ?_⟩
    · apply List.mem_map.mpr
      refine ⟨letter, ?_, rfl⟩
      simp
    · constructor
      · exact
          (family.zoneRelativeLetterFormula_correct
            direct _ _ letter _).2 hdirect
      · exact
          (family.zoneRelativeLetterFormula_correct
            shifted _ _ letter _).2 hshifted

end LinearWordFamily

end NSSE
