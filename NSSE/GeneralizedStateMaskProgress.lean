import NSSE.LabelledGeneralizedStateCompleteness
import Lean.Elab.Tactic.Omega

/-!
# Finite progress measure for generalized-state masks

The sum of guarded and forbidden true bits is bounded by the two fixed mask
lengths.  Every proper monotone mask refinement strictly increases this
rank, so a same-scale refinement sequence cannot grow forever.
-/

namespace NSSE

universe u

def generalizedMaskRank (state : GeneralizedState Tag) : Nat :=
  boolRank state.guarded + boolRank state.forbidden

theorem generalizedMaskRank_le
    {state : GeneralizedState Tag}
    (hvalid : state.Valid atomCount queryCount) :
    generalizedMaskRank state ≤ atomCount + queryCount := by
  unfold generalizedMaskRank
  have hguarded := boolRank_le_length state.guarded
  have hforbidden := boolRank_le_length state.forbidden
  calc
    boolRank state.guarded + boolRank state.forbidden ≤
        state.guarded.length + state.forbidden.length :=
      Nat.add_le_add hguarded hforbidden
    _ = atomCount + queryCount := by
      rw [hvalid.1, hvalid.2]

theorem generalizedMaskRank_mono
    {parent child : GeneralizedState Tag}
    (hguarded : MaskLe parent.guarded child.guarded)
    (hforbidden : MaskLe parent.forbidden child.forbidden) :
    generalizedMaskRank parent ≤ generalizedMaskRank child := by
  unfold generalizedMaskRank
  exact Nat.add_le_add hguarded.rank_le hforbidden.rank_le

theorem generalizedMaskRank_lt_of_masks_ne
    {parent child : GeneralizedState Tag}
    (hguarded : MaskLe parent.guarded child.guarded)
    (hforbidden : MaskLe parent.forbidden child.forbidden)
    (hne :
      parent.guarded ≠ child.guarded ∨
        parent.forbidden ≠ child.forbidden) :
    generalizedMaskRank parent < generalizedMaskRank child := by
  unfold generalizedMaskRank
  rcases hne with hguardedNe | hforbiddenNe
  · have hstrict := hguarded.rank_lt_of_ne hguardedNe
    have hle := hforbidden.rank_le
    omega
  · have hle := hguarded.rank_le
    have hstrict := hforbidden.rank_lt_of_ne hforbiddenNe
    omega

theorem labelledChildState_rank_mono
    (labels : TransitionMaskLabels Tag)
    (parent child : Tag)
    (guarded forbidden : List Bool) :
    generalizedMaskRank
        (GeneralizedState.mk parent guarded forbidden) ≤
      generalizedMaskRank
        (labelledChildState labels parent guarded forbidden child) := by
  apply generalizedMaskRank_mono
  · exact maskLe_markMany _ _
  · exact maskLe_markMany _ _

theorem labelledChildState_rank_lt_of_masks_ne
    (labels : TransitionMaskLabels Tag)
    (parent child : Tag)
    (guarded forbidden : List Bool)
    (hne :
      guarded ≠
          labelledGuardedUpdate labels parent child guarded ∨
        forbidden ≠
          labelledForbiddenUpdate labels parent child forbidden) :
    generalizedMaskRank
        (GeneralizedState.mk parent guarded forbidden) <
      generalizedMaskRank
        (labelledChildState labels parent guarded forbidden child) := by
  apply generalizedMaskRank_lt_of_masks_ne
  · exact maskLe_markMany _ _
  · exact maskLe_markMany _ _
  · exact hne

theorem masks_eq_of_monotone_rank_eq
    {parent child : GeneralizedState Tag}
    (hguarded : MaskLe parent.guarded child.guarded)
    (hforbidden : MaskLe parent.forbidden child.forbidden)
    (hrank :
      generalizedMaskRank parent = generalizedMaskRank child) :
    parent.guarded = child.guarded ∧
      parent.forbidden = child.forbidden := by
  constructor
  · apply hguarded.eq_of_rank_eq
    unfold generalizedMaskRank at hrank
    have hguardedLe := hguarded.rank_le
    have hforbiddenLe := hforbidden.rank_le
    omega
  · apply hforbidden.eq_of_rank_eq
    unfold generalizedMaskRank at hrank
    have hguardedLe := hguarded.rank_le
    have hforbiddenLe := hforbidden.rank_le
    omega

theorem labelled_masks_eq_of_follow_and_rank_eq
    (labels : TransitionMaskLabels Tag)
    (parent child : GeneralizedState Tag)
    (hfollow :
      allStateMasksFollow
          (labelledGuardedUpdate labels)
          (labelledForbiddenUpdate labels)
          parent [child] = true)
    (hrank :
      generalizedMaskRank parent = generalizedMaskRank child) :
    parent.guarded = child.guarded ∧
      parent.forbidden = child.forbidden := by
  rw [allStateMasksFollow_correct] at hfollow
  obtain ⟨hguardedEq, hforbiddenEq⟩ := hfollow child (by simp)
  apply masks_eq_of_monotone_rank_eq
  · rw [hguardedEq]
    exact maskLe_markMany _ _
  · rw [hforbiddenEq]
    exact maskLe_markMany _ _
  · exact hrank

theorem no_strict_refinement_at_max_rank
    {parent child : GeneralizedState Tag}
    (hvalid : parent.Valid atomCount queryCount)
    (hguarded : MaskLe parent.guarded child.guarded)
    (hforbidden : MaskLe parent.forbidden child.forbidden)
    (hmax :
      generalizedMaskRank parent = atomCount + queryCount) :
    parent.guarded = child.guarded ∧
      parent.forbidden = child.forbidden := by
  have hparentBound := generalizedMaskRank_le hvalid
  have hmono := generalizedMaskRank_mono hguarded hforbidden
  have hchildLengths :
      child.guarded.length = atomCount ∧
        child.forbidden.length = queryCount := by
    constructor
    · rw [← hguarded.length_eq, hvalid.1]
    · rw [← hforbidden.length_eq, hvalid.2]
  have hchildBound :=
    generalizedMaskRank_le hchildLengths
  have hrank :
      generalizedMaskRank parent = generalizedMaskRank child := by
    omega
  constructor
  · apply hguarded.eq_of_rank_eq
    unfold generalizedMaskRank at hrank
    have hforbiddenLe := hforbidden.rank_le
    have hguardedLe := hguarded.rank_le
    omega
  · apply hforbidden.eq_of_rank_eq
    unfold generalizedMaskRank at hrank
    have hforbiddenLe := hforbidden.rank_le
    have hguardedLe := hguarded.rank_le
    omega

def remainingMaskCapacity
    (atomCount queryCount : Nat)
    (state : GeneralizedState Tag) : Nat :=
  atomCount + queryCount - generalizedMaskRank state

theorem remainingMaskCapacity_lt_of_strict_refinement
    {parent child : GeneralizedState Tag}
    (hparentValid : parent.Valid atomCount queryCount)
    (hchildValid : child.Valid atomCount queryCount)
    (hguarded : MaskLe parent.guarded child.guarded)
    (hforbidden : MaskLe parent.forbidden child.forbidden)
    (hne :
      parent.guarded ≠ child.guarded ∨
        parent.forbidden ≠ child.forbidden) :
    remainingMaskCapacity atomCount queryCount child <
      remainingMaskCapacity atomCount queryCount parent := by
  have hstrict :=
    generalizedMaskRank_lt_of_masks_ne
      hguarded hforbidden hne
  have hparentBound := generalizedMaskRank_le hparentValid
  have hchildBound := generalizedMaskRank_le hchildValid
  unfold remainingMaskCapacity
  omega

theorem remainingCapacity_lt_of_forbidden_emission_false
    (labels : TransitionMaskLabels Tag)
    {atomCount queryCount : Nat}
    (parent child :
      ValidGeneralizedState Tag atomCount queryCount)
    (hfollow :
      allStateMasksFollow
          (labelledGuardedUpdate labels)
          (labelledForbiddenUpdate labels)
          parent.1 [child.1] = true)
    (index : Nat)
    (hemitted :
      index ∈ labels.forbidden parent.1.tag child.1.tag)
    (hbound : index < parent.1.forbidden.length)
    (hfalse :
      maskBit parent.1.forbidden index = false) :
    remainingMaskCapacity atomCount queryCount child.1 <
      remainingMaskCapacity atomCount queryCount parent.1 := by
  rw [allStateMasksFollow_correct] at hfollow
  obtain ⟨hguardedEq, hforbiddenEq⟩ :=
    hfollow child.1 (by simp)
  have hguarded :
      MaskLe parent.1.guarded child.1.guarded := by
    rw [hguardedEq]
    exact maskLe_markMany _ _
  have hforbidden :
      MaskLe parent.1.forbidden child.1.forbidden := by
    rw [hforbiddenEq]
    exact maskLe_markMany _ _
  have hmarked :
      maskBit child.1.forbidden index = true :=
    labelledFollow_marks_forbidden
      labels parent.1 child.1
      (by
        rw [allStateMasksFollow_correct]
        intro found hfound
        simpa using hfollow found hfound)
      index hemitted hbound
  have hne :
      parent.1.guarded ≠ child.1.guarded ∨
        parent.1.forbidden ≠ child.1.forbidden := by
    right
    intro heq
    rw [← heq, hfalse] at hmarked
    contradiction
  exact remainingMaskCapacity_lt_of_strict_refinement
    parent.2 child.2 hguarded hforbidden hne

end NSSE
