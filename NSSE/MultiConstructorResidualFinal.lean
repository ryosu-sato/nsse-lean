import NSSE.MultiConstructorPeriodicWitness
import NSSE.P0ResidualExistence

/-! The residual's final-state test is the actual chosen-side token
emptiness bit. Good lasso states project that finite test to the original stream. -/
namespace NSSE.MultiConstructorResidualFinal
open MultiConstructorBranch MultiConstructorRawTrace MultiConstructorStreamTrace
open MultiConstructorGoodStream MultiConstructorOrientedMachine
open P0ProperMachine P0ProperWords P0PeriodicInspectionDecision
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D r : Nat}

def emptyRow (side : Bool) (s : Row n) : Prop := if side then s.2 = ∅ else s.1 = ∅

def emptySide (side : Bool) : Option (State n) → Prop
  | none => False
  | some q => emptyRow side q.1

def finalDecision (n : Nat) (side : Bool) : DecidablePred (@emptySide n side) := by
  intro q
  cases side <;> cases q <;> dsimp only [emptySide,emptyRow] <;> infer_instance

theorem lasso_phases (C : Parameters arity n) (w : List (Fin D))
    (hr : 0 < r) (cycle : Fin r → Fin D) :
    P0PeriodicIsolation.LettersPeriodic (annotation C.input C.left C.right (lasso w hr cycle)) w.length r := by
  apply PeriodicCopyHeadNormalization.phase_of_shift
  intro a ha
  change lasso w hr cycle (a+r) = lasso w hr cycle a
  rw [lasso,dif_neg (by omega),lasso,dif_neg (by omega)]
  congr 1
  apply Fin.ext
  simp only [P0PeriodicDriver.phase]
  rw [show a+r-w.length = (a-w.length)+r by omega]
  simp only [Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]

theorem final_raw (C : Parameters arity n) (side : Bool) (w : List (Fin D)) (z : Nat → Fin D)
    (hz : Spells z w) (hg : Good (P0DZProperMachine.machine (branch C D)) z)
    (hf : emptySide side (state (oriented C D side) w w.length)) :
    emptyRow side (rawRow C.input C.left C.right z w.length) := by
  rw [state_eq_run _ w z hz w.length le_rfl,run_eq,run_state C z hg w.length] at hf
  change emptyRow side (MultiConstructorBranchLocal.walk C (branch C D).initial (prefixWord z w.length)).1 at hf
  rwa [walk_raw_prefix] at hf

theorem realize (C : Parameters arity n) (side : Bool) (w : List (Fin D))
    (hr : 0 < r) (cycle : Fin r → Fin D)
    (hg : Good (oriented C D side) (lasso w hr cycle))
    (hf : emptySide side (state (oriented C D side) w w.length))
    (hn : ¬P0PeriodicMonitorInvariant.Permanent (oriented C D side) (lasso w hr cycle) w.length) :
    MultiConstructorUnifiedWords.Witness C.input C.left C.right
      (prefixWord (lasso w hr cycle) (2*w.length+r)) := by
  have hbase := (good_iff C side _).mp hg
  have he := final_raw C side w _ (P0PeriodicBlocks.lasso_spells w hr cycle) hbase hf
  cases side
  · exact MultiConstructorPeriodicWitness.upper_at_bound C _ hbase w.length r hr (lasso_phases C w hr cycle) he hn
  · exact MultiConstructorPeriodicWitness.lower_at_bound C _ hbase w.length r hr (lasso_phases C w hr cycle) he hn

end NSSE.MultiConstructorResidualFinal
