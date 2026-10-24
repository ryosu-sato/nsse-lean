import NSSE.ComponentRoutesPresburger

/-!
# Family-zone letters with two additional Presburger coordinates

The family parameters occupy the first `arity` coordinates.  Two trailing
coordinates may represent addressed copy/gap data without changing the
generated word.
-/

namespace NSSE

universe u

namespace NatPresburger

def weakenExprTwo
    (expression : NatLinearExpr arity) :
    NatLinearExpr (arity + 2) :=
  weakenExpr (weakenExpr expression)

def extraTwoValuation
    (parameters : Fin arity → Nat)
    (first second : Nat) :
    Fin (arity + 2) → Nat :=
  extendValuation (extendValuation parameters first) second

@[simp] theorem eval_weakenExprTwo
    (expression : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (first second : Nat) :
    (weakenExprTwo expression).Eval
        (extendValuation
          (extendValuation parameters first) second) =
      expression.Eval parameters := by
  simp [weakenExprTwo]

@[simp] theorem eval_weakenExprTwo_extraTwoValuation
    (expression : NatLinearExpr arity)
    (parameters : Fin arity → Nat)
    (first second : Nat) :
    (weakenExprTwo expression).Eval
        (extraTwoValuation parameters first second) =
      expression.Eval parameters := by
  simp [extraTwoValuation]

end NatPresburger

namespace LinearWordFamily

theorem zoneEndPosition_le_word_length
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (zone : LinearFamilyZone arity) :
    family.zoneEndPosition parameters zone ≤
      (family.word parameters).length := by
  cases zone with
  | initial =>
      unfold word zoneEndPosition
      simp
  | pump index =>
      rw [family.word_eq_stagePrefix_decomposition parameters index]
      simp only [List.length_append, Word.power_length,
        zoneEndPosition, pumpEndPosition,
        family.stagePrefix_length]
      omega
  | separator index =>
      rw [family.word_eq_stagePrefix_decomposition parameters index]
      simp only [List.length_append, Word.power_length,
        zoneEndPosition, separatorEndPosition, pumpEndPosition,
        family.stagePrefix_length]
      omega

theorem zoneRelativeLetterAt_iff_word_getElem_of_local
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (zone : LinearFamilyZone arity)
    (position origin : NatLinearExpr variableCount)
    (valuation : Fin variableCount → Nat)
    (absolutePosition : Nat)
    (letter : α)
    (horigin :
      origin.Eval valuation ≤ position.Eval valuation)
    (hlocal :
      position.Eval valuation - origin.Eval valuation =
        absolutePosition -
          family.zoneStartPosition parameters zone)
    (hstart :
      family.zoneStartPosition parameters zone ≤
        absolutePosition)
    (hend :
      absolutePosition <
        family.zoneEndPosition parameters zone) :
    family.ZoneRelativeLetterAt zone position origin
        letter valuation ↔
      (family.word parameters)[absolutePosition]? =
        some letter := by
  have hconcrete :=
    family.zoneRelativeLetterAt_const_iff_word_getElem?
      hnonempty parameters zone absolutePosition letter hstart hend
  cases zone with
  | initial =>
      change
        FixedRelativeLetterAt family.initial position origin
            letter valuation ↔
          (family.word parameters)[absolutePosition]? = some letter
      rw [fixedRelativeLetterAt_iff_local
        family.initial position origin letter valuation horigin]
      change
        FixedRelativeLetterAt family.initial
            (.const absolutePosition) (.const 0)
            letter parameters ↔
          (family.word parameters)[absolutePosition]? =
            some letter at hconcrete
      rw [fixedRelativeLetterAt_iff_local
        family.initial (.const absolutePosition) (.const 0)
        letter parameters (by simp)] at hconcrete
      simp only [zoneStartPosition] at hlocal
      simpa [hlocal] using hconcrete
  | separator index =>
      change
        FixedRelativeLetterAt (family.separator index)
            position origin letter valuation ↔
          (family.word parameters)[absolutePosition]? = some letter
      rw [fixedRelativeLetterAt_iff_local
        (family.separator index) position origin
        letter valuation horigin]
      change
        FixedRelativeLetterAt (family.separator index)
            (.const absolutePosition)
            (.const
              (family.zoneStartPosition parameters
                (.separator index)))
            letter parameters ↔
          (family.word parameters)[absolutePosition]? =
            some letter at hconcrete
      rw [fixedRelativeLetterAt_iff_local
        (family.separator index)
        (.const absolutePosition)
        (.const
          (family.zoneStartPosition parameters
            (.separator index)))
        letter parameters (by simpa using hstart)] at hconcrete
      simpa [hlocal] using hconcrete
  | pump index =>
      change
        PeriodicRelativeLetterAt (family.pump index)
            position origin letter valuation ↔
          (family.word parameters)[absolutePosition]? = some letter
      rw [periodicRelativeLetterAt_iff_local
        (family.pump index) (hnonempty index)
        position origin letter valuation horigin]
      change
        PeriodicRelativeLetterAt (family.pump index)
            (.const absolutePosition)
            (.const
              (family.zoneStartPosition parameters (.pump index)))
            letter parameters ↔
          (family.word parameters)[absolutePosition]? =
            some letter at hconcrete
      rw [periodicRelativeLetterAt_iff_local
        (family.pump index) (hnonempty index)
        (.const absolutePosition)
        (.const
          (family.zoneStartPosition parameters (.pump index)))
        letter parameters (by simpa using hstart)] at hconcrete
      simpa [hlocal] using hconcrete

end LinearWordFamily

end NSSE
