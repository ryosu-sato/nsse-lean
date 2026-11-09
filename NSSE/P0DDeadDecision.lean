import NSSE.P0DDeadReader
import Mathlib.Data.Fintype.Option

/-! Executable checking of a supplied finite reader word. This does not
yet decide existence of any accepted word without a proved length bound. -/
namespace NSSE.P0DDeadDecision
open P0DDeadReader P0MarkerComparison P0ProperWords
variable {Q A H : Type*}

def bornCheck (J : Reader Q A H) (bd : DecidableRel J.birth) (w : List A) (a b : Nat) : Bool :=
  match trace J w a,trace J w b with
  | some q,some t => @decide (J.birth q t) (bd q t)
  | _,_ => false

theorem bornCheck_correct (J : Reader Q A H) (bd : DecidableRel J.birth)
    (w : List A) (a b : Nat) : bornCheck J bd w a b = true ↔ bornAt J w a b := by
  unfold bornCheck bornAt
  cases ha : trace J w a <;> cases hb : trace J w b <;> simp

def acceptedDecision [DecidableEq Q] [DecidableEq A] [DecidableEq H]
    (J : Reader Q A H) (bd : DecidableRel J.birth) (w : List A) : Decidable (Accepted J w) := by
  letI : DecidableRel (bornAt J w) := fun a b =>
    decidable_of_iff (bornCheck J bd w a b = true) (bornCheck_correct J bd w a b)
  unfold Accepted Complete Safe WordMatch
  refine @instDecidableAnd _ _ ?_ ?_
  · infer_instance
  · refine @Nat.decidableBallLE w.length _ ?_
    intro a _
    refine @Nat.decidableBallLE w.length _ ?_
    intro b _
    refine @Nat.decidableBallLE w.length _ ?_
    intro l _
    infer_instance

def inspect [DecidableEq Q] [DecidableEq A] [DecidableEq H]
    (J : Reader Q A H) (bd : DecidableRel J.birth) (w : List A) : Bool :=
  @decide (Accepted J w) (acceptedDecision J bd w)

theorem inspect_correct [DecidableEq Q] [DecidableEq A] [DecidableEq H]
    (J : Reader Q A H) (bd : DecidableRel J.birth) (w : List A) :
    inspect J bd w = true ↔ Accepted J w := by
  unfold inspect
  simp only [decide_eq_true_eq]

end NSSE.P0DDeadDecision
