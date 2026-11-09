import NSSE.P0CutSafety
import NSSE.P0DDeadDecision

/-! Executable finite certificates for the old-word entry condition and
state-loop equalities. Passing certifies safety of the actual cut word;
failure is not asserted to be necessary for unsafety. -/
namespace NSSE.P0CutDecision
open P0DDeadReader P0ProperWords P0WordCuts P0CutComparison P0CutSafety
variable {Q A H : Type*} {w : List A} {n : Nat}

def compatibleDecision [DecidableEq A] [DecidableEq H] (w : List A)
    (left right : Nat → H) (a b : Nat) : Decidable (Compatible w left right a b) := by
  unfold Compatible WordMatch
  infer_instance

def entryDecision [DecidableEq A] [DecidableEq H] (C : Cut w n) (left right : Nat → H) :
    Decidable (Entry C left right) := by
  letI := compatibleDecision w left right
  unfold Entry Seam
  refine @Nat.decidableBallLE n _ ?_
  intro a _
  refine @Nat.decidableBallLE n _ ?_
  intro b _
  infer_instance

def loopsDecision [DecidableEq Q] (C : Cut w n) (J : Reader Q A H) : Decidable (C.Loops J) := by
  unfold Cut.Loops
  infer_instance

def checkEntry [DecidableEq A] [DecidableEq H] (C : Cut w n) (left right : Nat → H) : Bool :=
  @decide (Entry C left right) (entryDecision C left right)

theorem checkEntry_correct [DecidableEq A] [DecidableEq H] (C : Cut w n) (left right : Nat → H) :
    checkEntry C left right = true ↔ Entry C left right := by
  unfold checkEntry
  simp only [decide_eq_true_eq]

def verify [DecidableEq Q] [DecidableEq A] [DecidableEq H] (C : Cut w n)
    (J : Reader Q A H) (bd : DecidableRel J.birth) : Bool :=
  P0DDeadDecision.inspect J bd w && decide (J.endX ≠ J.endY) &&
    @decide (C.Loops J) (loopsDecision C J) && checkEntry C (leftAt J w) (rightAt J w)

theorem verify_sound [DecidableEq Q] [DecidableEq A] [DecidableEq H] (C : Cut w n)
    (J : Reader Q A H) (bd : DecidableRel J.birth) (hv : verify C J bd = true) :
    Accepted J C.word := by
  simp only [verify,Bool.and_eq_true,decide_eq_true_eq,checkEntry_correct,
    P0DDeadDecision.inspect_correct] at hv
  exact accepted_cut C J hv.1.1.2 hv.1.1.1 hv.1.2 hv.2

end NSSE.P0CutDecision
