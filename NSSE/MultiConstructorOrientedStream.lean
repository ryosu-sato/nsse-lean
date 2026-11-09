import NSSE.MultiConstructorGoodStream

/-! Oriented machine births along a Good run are precisely original
stream births in the chosen X/Y order, including equal origins. -/
namespace NSSE.MultiConstructorOrientedStream
open MultiConstructorBranch MultiConstructorBranchLocal MultiConstructorGoodStream
open MultiConstructorStreamTrace MultiConstructorOrientedMachine
open P0ProperMachine P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem birth_exact (C : Parameters arity n) (side : Bool) (z : Nat → Fin D)
    (hg : Good (P0DZProperMachine.machine (branch C D)) z) (a b : Nat) :
    (oriented C D side).birth (run (oriented C D side) z a) (run (oriented C D side) z b) ↔
      if side then GeneralCopyGrid.Born (annotation C.input C.left C.right z) a b
      else GeneralCopyGrid.Born (annotation C.input C.left C.right z) b a := by
  rw [run_eq,run_eq,run_state C z hg a,run_state C z hg b]
  cases side <;> simp only [oriented,forward,Bool.false_eq_true,if_false,if_true]
  · rw [branch_birth]
    change (∃ v ∈ (walk C (branch C D).initial (prefixWord z b)).1.1,
      v ∈ (walk C (branch C D).initial (prefixWord z a)).1.2) ↔ _
    rw [walk_raw_prefix,walk_raw_prefix]
    rfl
  · rw [branch_birth]
    change (∃ v ∈ (walk C (branch C D).initial (prefixWord z a)).1.1,
      v ∈ (walk C (branch C D).initial (prefixWord z b)).1.2) ↔ _
    rw [walk_raw_prefix,walk_raw_prefix]
    rfl

end NSSE.MultiConstructorOrientedStream
