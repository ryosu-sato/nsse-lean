import NSSE.MultiConstructorStreamGrid

/-! Infinite Good branch runs carry the actual original raw token stream.
Their positive finite prefixes supply Common assignments for realization. -/
namespace NSSE.MultiConstructorGoodStream
open MultiConstructorBranch MultiConstructorBranchLocal MultiConstructorUnifiedBranch
open MultiConstructorUnifiedWords MultiConstructorStreamTrace MultiConstructorGoodCommon
open MultiConstructorCommonWord MultiConstructorProperTrace
open P0ProperMachine P0ProperWords P0DZVirtualTrace P0DZFirstClash
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem good_prefix (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (m : Nat) :
    GoodWord (P0DZProperMachine.machine (branch C D)) (prefixWord z m) :=
  (goodWord_prefix _ z m).mpr (hg m)

theorem run_state (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (k : Nat) :
    run (P0DZProperMachine.machine (branch C D)) z k =
      some (walk C (branch C D).initial (prefixWord z k)) := by
  have hc := ((P0DZProperMachine.good_iff (branch C D) (prefixWord z k)).mp (good_prefix C z hg k)).1
  rw [← state_eq_run _ (prefixWord z k) z (spells_prefix z k) k (by simp),
    P0DZProperMachine.state_exact,proper_eq_state _ _ hc,state_walk C _ hc]
  rw [List.take_of_length_le (by simp)]

theorem walk_raw_prefix (C : Parameters arity n) (z : Nat → Fin D) (k : Nat) :
    (walk C (branch C D).initial (prefixWord z k)).1 = rawRow C.input C.left C.right z k := by
  rw [walk_raw]
  have h := prefix_row C.input C.left C.right z k k le_rfl
  simpa only [row,List.take_of_length_le (by simp : (prefixWord z k).length ≤ k)] using h

theorem run_raw (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (k : Nat) :
    (run (P0DZProperMachine.machine (branch C D)) z k).map Prod.fst =
      some (rawRow C.input C.left C.right z k) := by
  rw [run_state C z hg k]
  exact congrArg some (walk_raw_prefix C z k)

theorem common_prefix (C : Parameters arity n) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (m : Nat) (hm : 0 < m) :
    Common C.input C.left C.right (prefixWord z m) (selectedHeads C (prefixWord z m))
      (headAt C (prefixWord z m) m) := by
  have hw : prefixWord z m ≠ [] := List.length_pos_iff.mp (by simpa only [prefix_length] using hm)
  simpa only [prefix_length] using good_common C (prefixWord z m) hw (good_prefix C z hg m)

end NSSE.MultiConstructorGoodStream
