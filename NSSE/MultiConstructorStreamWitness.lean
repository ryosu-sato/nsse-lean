import NSSE.MultiConstructorOrientedStream

/-! Original unpinned isolation on an infinite Good path realizes a finite
U-witness at that exact positive frontier, with no supplied terminal assignment. -/
namespace NSSE.MultiConstructorStreamWitness
open MultiConstructorTokens MultiConstructorBranch MultiConstructorUnifiedWords MultiConstructorUnifiedBranch
open MultiConstructorStreamTrace MultiConstructorStreamGrid MultiConstructorGoodStream MultiConstructorGoodCommon
open P0ProperMachine P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem lower_witness (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (m : Nat) (hm : 0 < m)
    (hp : lowerPins C.input (rawRow C.input C.left C.right z m).2 = ∅)
    (hi : ¬P0PeriodicIsolation.Incident (annotation C.input C.left C.right z) m) :
    Witness C.input C.left C.right (prefixWord z m) := by
  apply MultiConstructorExtremeWitness.lower_witness C.input C.left C.right (prefixWord z m)
    (selectedHeads C (prefixWord z m)) (headAt C (prefixWord z m) m) (common_prefix C z hg m hm)
  · simpa only [prefix_length,prefix_row C.input C.left C.right z m m le_rfl] using hp
  · intro h
    exact hi ((lower_incident_spells C.input C.left C.right (prefixWord z m) z (spells_prefix z m)
      m (by simp)).mpr (by simpa only [prefix_length] using h))

theorem upper_witness (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (m : Nat) (hm : 0 < m)
    (hp : upperPins C.input (rawRow C.input C.left C.right z m).1 = ∅)
    (hi : ¬∃ j, j ≤ m ∧ GeneralCopyGrid.Active (annotation C.input C.left C.right z) m j m) :
    Witness C.input C.left C.right (prefixWord z m) := by
  apply MultiConstructorExtremeWitness.upper_witness C.input C.left C.right (prefixWord z m)
    (selectedHeads C (prefixWord z m)) (headAt C (prefixWord z m) m) (common_prefix C z hg m hm)
  · simpa only [prefix_length,prefix_row C.input C.left C.right z m m le_rfl] using hp
  · intro h
    exact hi ((upper_incident_spells C.input C.left C.right (prefixWord z m) z (spells_prefix z m)
      m (by simp)).mpr (by simpa only [prefix_length] using h))

end NSSE.MultiConstructorStreamWitness
