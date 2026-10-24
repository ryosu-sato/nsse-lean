import NSSE.RelativeLetterSemantics

/-!
# Relative zone letters are the concrete family-word letters

On the half-open interval of a zone, its fixed or periodic relative
letter predicate is exactly lookup at the corresponding absolute
position in the generated linear-family word.
-/

namespace NSSE

universe u

namespace LinearWordFamily

theorem zoneRelativeLetterAt_const_iff_word_getElem?
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat)
    (zone : LinearFamilyZone arity)
    (position : Nat)
    (letter : α)
    (hstart :
      family.zoneStartPosition parameters zone ≤ position)
    (hend :
      position < family.zoneEndPosition parameters zone) :
    family.ZoneRelativeLetterAt zone
        (.const position)
        (.const (family.zoneStartPosition parameters zone))
        letter parameters ↔
      (family.word parameters)[position]? = some letter := by
  cases zone with
  | initial =>
      change
        FixedRelativeLetterAt family.initial
            (.const position) (.const 0)
            letter parameters ↔
          (family.word parameters)[position]? = some letter
      rw [fixedRelativeLetterAt_iff_local
        family.initial (.const position) (.const 0)
        letter parameters (by simp)]
      simp only [NatLinearExpr.eval_const,
        Nat.sub_zero]
      constructor
      · rintro ⟨hoffset, hletter⟩
        rw [family.word_getElem?_initial
          parameters position hoffset]
        exact hletter
      · intro hletter
        refine ⟨?_, ?_⟩
        · simpa [zoneEndPosition] using hend
        · rwa [family.word_getElem?_initial
            parameters position
            (by simpa [zoneEndPosition] using hend)] at hletter
  | separator index =>
      change
        FixedRelativeLetterAt (family.separator index)
            (.const position)
            (.const (family.pumpEndPosition parameters index))
            letter parameters ↔
          (family.word parameters)[position]? = some letter
      rw [fixedRelativeLetterAt_iff_local
        (family.separator index)
        (.const position)
        (.const (family.pumpEndPosition parameters index))
        letter parameters (by simpa [zoneStartPosition] using hstart)]
      simp only [NatLinearExpr.eval_const]
      let offset :=
        position - family.pumpEndPosition parameters index
      have hposition :
          family.pumpEndPosition parameters index + offset =
            position :=
        Nat.add_sub_of_le
          (by simpa [zoneStartPosition] using hstart)
      have hoffset :
          offset < (family.separator index).length := by
        have hend' :
            position <
              family.pumpEndPosition parameters index +
                (family.separator index).length := by
          simpa [zoneEndPosition, separatorEndPosition] using hend
        omega
      constructor
      · rintro ⟨hoffset', hletter⟩
        rw [← hposition,
          family.word_getElem?_separator
            parameters index offset hoffset]
        simpa [offset] using hletter
      · intro hletter
        refine ⟨by simpa [offset] using hoffset, ?_⟩
        rw [← hposition,
          family.word_getElem?_separator
            parameters index offset hoffset] at hletter
        simpa [offset] using hletter
  | pump index =>
      have hpump :
          family.pump index ≠ [] := hnonempty index
      change
        PeriodicRelativeLetterAt (family.pump index)
            (.const position)
            (.const (family.stageStartPosition parameters index))
            letter parameters ↔
          (family.word parameters)[position]? = some letter
      rw [periodicRelativeLetterAt_iff_local
        (family.pump index) hpump
        (.const position)
        (.const (family.stageStartPosition parameters index))
        letter parameters
        (by simpa [zoneStartPosition] using hstart)]
      simp only [NatLinearExpr.eval_const]
      let localOffset :=
        position - family.stageStartPosition parameters index
      let copy := localOffset / (family.pump index).length
      let offset := localOffset % (family.pump index).length
      have hlength :
          0 < (family.pump index).length :=
        family.pump_length_positive hnonempty index
      have hoffset :
          offset < (family.pump index).length :=
        Nat.mod_lt _ hlength
      have hlocal :
          copy * (family.pump index).length + offset =
            localOffset := by
        simpa [copy, offset, Nat.mul_comm] using
          Nat.div_add_mod localOffset
            (family.pump index).length
      have hposition :
          family.stageStartPosition parameters index +
              (copy * (family.pump index).length + offset) =
            position := by
        rw [hlocal]
        exact Nat.add_sub_of_le
          (by simpa [zoneStartPosition] using hstart)
      have hlocalEnd :
          localOffset <
            parameters index * (family.pump index).length := by
        have hend' :
            position <
              family.stageStartPosition parameters index +
                parameters index *
                  (family.pump index).length := by
          simpa [zoneEndPosition, pumpEndPosition] using hend
        omega
      have hcopy : copy < parameters index := by
        apply (Nat.div_lt_iff_lt_mul hlength).2
        simpa [copy, localOffset] using hlocalEnd
      constructor
      · intro hletter
        rw [← hposition,
          family.word_getElem?_pump parameters index
            copy offset hcopy hoffset]
        simpa [localOffset, offset] using hletter
      · intro hletter
        rw [← hposition,
          family.word_getElem?_pump parameters index
            copy offset hcopy hoffset] at hletter
        simpa [localOffset, offset] using hletter

end LinearWordFamily

end NSSE
