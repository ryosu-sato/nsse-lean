import NSSE.P0DZTrace

/-! Exact finite checking for full D/Z branches, including all four rails,
terminal state IDs and cross-rail diagonal births. No length bound or
general existence decision is claimed here. -/
namespace NSSE.P0DZDecision
open P0DZBranch P0ProperWords
variable {Q Z A H : Type*}

abbrev BirthDecision (J : Branch Q Z A H) := ∀ q s r t, Decidable (J.birth q s r t)

def bornCheck (J : Branch Q Z A H) (bd : BirthDecision J) (w : List A)
    (a : Nat) (s : Bool) (b : Nat) (t : Bool) : Bool :=
  match stateAt J w a,stateAt J w b with
  | some q,some r => @decide (J.birth q s r t) (bd q s r t)
  | _,_ => false

theorem bornCheck_correct (J : Branch Q Z A H) (bd : BirthDecision J) (w : List A)
    (a : Nat) (s : Bool) (b : Nat) (t : Bool) :
    bornCheck J bd w a s b t = true ↔ bornAt J w a s b t := by
  unfold bornCheck bornAt
  cases ha : stateAt J w a <;> cases hb : stateAt J w b <;> simp

def compatibleDecision [DecidableEq A] [DecidableEq H] (J : Branch Q Z A H) (w : List A)
    (a : Nat) (s : Bool) (b : Nat) (t : Bool) : Decidable (Compatible J w a s b t) := by
  unfold Compatible WordMatch
  infer_instance

def acceptedDecision [DecidableEq A] [DecidableEq H] (J : Branch Q Z A H)
    (bd : BirthDecision J) (w : List A) : Decidable (Accepted J w) := by
  letI (a : Nat) (s : Bool) (b : Nat) (t : Bool) : Decidable (bornAt J w a s b t) :=
    decidable_of_iff (bornCheck J bd w a s b t = true) (bornCheck_correct J bd w a s b t)
  letI := compatibleDecision J w
  unfold Accepted Complete Safe
  refine @instDecidableAnd _ _ ?_ ?_
  · infer_instance
  · refine @Nat.decidableBallLE w.length _ ?_
    intro a _
    refine @Nat.decidableBallLE w.length _ ?_
    intro b _
    infer_instance

def inspect [DecidableEq A] [DecidableEq H] (J : Branch Q Z A H)
    (bd : BirthDecision J) (w : List A) : Bool :=
  @decide (Accepted J w) (acceptedDecision J bd w)

theorem inspect_correct [DecidableEq A] [DecidableEq H] (J : Branch Q Z A H)
    (bd : BirthDecision J) (w : List A) : inspect J bd w = true ↔ Accepted J w := by
  unfold inspect
  simp only [decide_eq_true_eq]

end NSSE.P0DZDecision
