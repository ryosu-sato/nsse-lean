import NSSE.GeneralEmptyPumpNormalization

/-!
# Arity of general empty-pump normalization

The normalized family has exactly one coordinate for every nonempty pump
of the original family.  This records that normalization neither loses a
nonempty powered stage nor retains a vacuous coordinate.
-/

namespace NSSE

namespace LinearWordFamily

def nonemptyPumpCount
    (family : LinearWordFamily α arity) : Nat :=
  (List.finRange arity).countP
    (fun index => !(family.pump index).isEmpty)

@[simp] theorem nonemptyPumpCount_zero
    (family : LinearWordFamily α 0) :
    family.nonemptyPumpCount = 0 := by
  simp [nonemptyPumpCount]

theorem nonemptyPumpCount_succ_empty
    (family : LinearWordFamily α (arity + 1))
    (hempty : family.pump 0 = []) :
    family.nonemptyPumpCount =
      family.eraseFirstPump.nonemptyPumpCount := by
  simp [nonemptyPumpCount, eraseFirstPump,
    List.finRange_succ_eq_map, List.countP_map,
    Function.comp_def, hempty]

theorem nonemptyPumpCount_succ_nonempty
    (family : LinearWordFamily α (arity + 1))
    (hhead : family.pump 0 ≠ []) :
    family.nonemptyPumpCount =
      family.tailFamily.nonemptyPumpCount + 1 := by
  simp [nonemptyPumpCount, tailFamily,
    List.finRange_succ_eq_map, List.countP_map,
    Function.comp_def, hhead, Nat.add_comm]

theorem nonemptyPumpCount_le
    (family : LinearWordFamily α arity) :
    family.nonemptyPumpCount ≤ arity := by
  simpa [nonemptyPumpCount] using
    (List.countP_le_length
      (l := List.finRange arity)
      (p := fun index => !(family.pump index).isEmpty))

theorem nonemptyPumpCount_eq_zero_iff
    (family : LinearWordFamily α arity) :
    family.nonemptyPumpCount = 0 ↔
      ∀ index, family.pump index = [] := by
  simp [nonemptyPumpCount, List.countP_eq_zero,
    List.isEmpty_eq_false_iff]

theorem pumpsNonempty_iff_nonemptyPumpCount :
    (arity : Nat) →
      (family : LinearWordFamily α arity) →
        family.PumpsNonempty ↔
          family.nonemptyPumpCount = arity
  | 0, family => by
      constructor
      · intro _
        exact family.nonemptyPumpCount_zero
      · intro _
        intro index
        exact Fin.elim0 index
  | arity + 1, family => by
      by_cases hempty : family.pump 0 = []
      · constructor
        · intro hnonempty
          exact (hnonempty 0 hempty).elim
        · intro hcount
          rw [family.nonemptyPumpCount_succ_empty
            hempty] at hcount
          have hle :=
            family.eraseFirstPump.nonemptyPumpCount_le
          omega
      · rw [family.nonemptyPumpCount_succ_nonempty
          hempty]
        constructor
        · intro hnonempty
          have htail :
              family.tailFamily.PumpsNonempty := by
            intro index
            exact hnonempty index.succ
          rw [(pumpsNonempty_iff_nonemptyPumpCount
            arity family.tailFamily).mp htail]
        · intro hcount
          have htailCount :
              family.tailFamily.nonemptyPumpCount = arity := by
            omega
          have htail :
              family.tailFamily.PumpsNonempty :=
            (pumpsNonempty_iff_nonemptyPumpCount
              arity family.tailFamily).mpr htailCount
          intro index
          refine Fin.cases hempty (fun tailIndex => ?_) index
          exact htail tailIndex

theorem normalizeEmptyPumps_reducedArity :
    (arity : Nat) →
      (family : LinearWordFamily α arity) →
        (family.normalizeEmptyPumps arity).reducedArity =
          family.nonemptyPumpCount
  | 0, family => by
      simp [normalizeEmptyPumps,
        NonemptyPumpReduction.identity]
  | arity + 1, family => by
      by_cases hempty : family.pump 0 = []
      · rw [family.nonemptyPumpCount_succ_empty hempty]
        simp [normalizeEmptyPumps, hempty,
          liftEraseFirstPumpReduction,
          normalizeEmptyPumps_reducedArity arity
            family.eraseFirstPump]
      · rw [family.nonemptyPumpCount_succ_nonempty hempty]
        simp [normalizeEmptyPumps, hempty,
          retainHeadReduction,
          normalizeEmptyPumps_reducedArity arity
            family.tailFamily]

theorem normalizeEmptyPumps_reducedArity_le
    (family : LinearWordFamily α arity) :
    (family.normalizeEmptyPumps arity).reducedArity ≤ arity := by
  rw [normalizeEmptyPumps_reducedArity]
  exact family.nonemptyPumpCount_le

theorem normalizeEmptyPumps_reducedArity_eq
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty) :
    (family.normalizeEmptyPumps arity).reducedArity =
      arity := by
  rw [normalizeEmptyPumps_reducedArity]
  exact (pumpsNonempty_iff_nonemptyPumpCount
    arity family).mp hnonempty

theorem normalizeEmptyPumps_preserves_arity_iff
    (family : LinearWordFamily α arity) :
    (family.normalizeEmptyPumps arity).reducedArity =
        arity ↔
      family.PumpsNonempty := by
  rw [normalizeEmptyPumps_reducedArity]
  exact (pumpsNonempty_iff_nonemptyPumpCount
    arity family).symm

theorem normalizeEmptyPumps_reducedArity_eq_zero_iff
    (family : LinearWordFamily α arity) :
    (family.normalizeEmptyPumps arity).reducedArity = 0 ↔
      ∀ index, family.pump index = [] := by
  rw [normalizeEmptyPumps_reducedArity,
    family.nonemptyPumpCount_eq_zero_iff]

theorem normalizeEmptyPumps_reducedArity_lt_iff
    (family : LinearWordFamily α arity) :
    (family.normalizeEmptyPumps arity).reducedArity < arity ↔
      ∃ index, family.pump index = [] := by
  classical
  constructor
  · intro hlt
    have hnot : ¬family.PumpsNonempty := by
      intro hnonempty
      have heq :=
        family.normalizeEmptyPumps_reducedArity_eq
          hnonempty
      omega
    simp only [PumpsNonempty] at hnot
    push_neg at hnot
    exact hnot
  · rintro ⟨index, hempty⟩
    have hne :
        (family.normalizeEmptyPumps arity).reducedArity ≠
          arity := by
      intro heq
      have hnonempty :=
        family.normalizeEmptyPumps_preserves_arity_iff.mp
          heq
      exact hnonempty index hempty
    exact Nat.lt_of_le_of_ne
      family.normalizeEmptyPumps_reducedArity_le hne

end LinearWordFamily

end NSSE
