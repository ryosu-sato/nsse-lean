import NSSE.MultiVarianceSelectorHead

/-! Total signed frame transitions and deterministic reset-selector steps.
Out-of-arity letters are inert here and rejected by the branch guard.
A reset replaces the entire selector frame, including its own sign. -/
namespace NSSE.MultiVarianceSelectorStep
open MultiConstructorConstraints (Constraints)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceSelectorHead
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

def step (phi : Constraints arity n) (F : Frame n) (h : H) (i : Nat) : Frame n :=
  if hi : i < arity h then physicalMove pol phi F h ⟨i,hi⟩ else F

theorem step_valid (phi : Constraints arity n) (F : Frame n) (h : H) (i : Fin (arity h)) :
    step pol phi F h i.val = physicalMove pol phi F h i := by
  simp only [step,i.isLt,dif_pos]

theorem step_invalid (phi : Constraints arity n) (F : Frame n) (h : H) (i : Nat)
    (hi : ¬i < arity h) : step pol phi F h i=F := by rw [step,dif_neg hi]

theorem step_empty (phi : Constraints arity n) (F : Frame n) (he : Empty F) (h : H) (i : Nat) :
    Empty (step pol phi F h i) := by
  unfold step
  split
  · exact unpinned_move_empty pol phi F h _ (empty_pins phi F he)
  · exact he

def next (phi : Constraints arity n) (reset : Frame n) (fallback : H) (F : Frame n) (i : Nat) : Frame n :=
  let t := step pol phi F (choose phi F fallback) i
  @ite _ (Empty t) (emptyDecision t) reset t

theorem next_reset (phi : Constraints arity n) (reset : Frame n) (fallback : H) (F : Frame n) (i : Nat)
    (he : Empty (step pol phi F (choose phi F fallback) i)) : next pol phi reset fallback F i=reset := by
  unfold next
  exact if_pos he

theorem next_raw (phi : Constraints arity n) (reset : Frame n) (fallback : H) (F : Frame n) (i : Nat)
    (he : ¬Empty (step pol phi F (choose phi F fallback) i)) :
    next pol phi reset fallback F i=step pol phi F (choose phi F fallback) i := by
  unfold next
  exact if_neg he

theorem empty_next (phi : Constraints arity n) (reset : Frame n) (fallback : H) (F : Frame n) (i : Nat)
    (he : Empty F) : next pol phi reset fallback F i=reset :=
  next_reset pol phi reset fallback F i (step_empty pol phi F he _ i)

theorem reset_sign (phi : Constraints arity n) (reset : Frame n) (fallback : H) (F : Frame n) (i : Nat)
    (he : Empty (step pol phi F (choose phi F fallback) i)) :
    (next pol phi reset fallback F i).sign=reset.sign := congrArg Frame.sign (next_reset pol phi reset fallback F i he)

theorem nonempty_forces_head (phi : Constraints arity n) (F : Frame n) (fallback h : H) (i : Fin (arity h))
    (hr : Ready phi F h) (hn : ¬Empty (physicalMove pol phi F h i)) : choose phi F fallback=h :=
  choose_forced phi F fallback h hr (move_nonempty_pins pol phi F h i hn)

end NSSE.MultiVarianceSelectorStep
