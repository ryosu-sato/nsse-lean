import NSSE.LabelledGeneralizedStateRules
import NSSE.CanonicalForbiddenTransitionLabels

/-!
# Saturation by a finite sequence of emitted mask indices

Each transition emits a finite batch of indices.  Sequentially marking all
batches preserves earlier true bits and makes every in-range emitted bit
true.  This gives an exact finite coverage criterion for terminal masks.
-/

namespace NSSE

def markBatches : List (List Nat) → List Bool → List Bool
  | [], mask => mask
  | batch :: batches, mask =>
      markBatches batches (markMany batch mask)

theorem maskLe_markBatches
    (batches : List (List Nat)) (mask : List Bool) :
    MaskLe mask (markBatches batches mask) := by
  induction batches generalizing mask with
  | nil =>
      exact MaskLe.refl mask
  | cons batch batches ih =>
      exact (maskLe_markMany batch mask).trans
        (ih (markMany batch mask))

theorem markBatches_length
    (batches : List (List Nat)) (mask : List Bool) :
    (markBatches batches mask).length = mask.length := by
  exact (maskLe_markBatches batches mask).length_eq.symm

theorem maskBit_markBatches_of_initial
    (batches : List (List Nat)) (mask : List Bool)
    (index : Nat) (hbit : maskBit mask index = true) :
    maskBit (markBatches batches mask) index = true :=
  (maskLe_markBatches batches mask).maskBit_true index hbit

theorem maskBit_markBatches_of_emitted
    (batches : List (List Nat)) (mask : List Bool)
    (index : Nat)
    (hemitted :
      ∃ batch ∈ batches, index ∈ batch)
    (hbound : index < mask.length) :
    maskBit (markBatches batches mask) index = true := by
  induction batches generalizing mask with
  | nil =>
      simp at hemitted
  | cons batch batches ih =>
      obtain ⟨found, hfound, hindex⟩ := hemitted
      simp only [List.mem_cons] at hfound
      rcases hfound with rfl | htail
      · exact maskBit_markBatches_of_initial
          batches (markMany found mask) index
          (maskBit_markMany_of_mem
            found mask index hindex hbound)
      · apply ih (markMany batch mask) ⟨found, htail, hindex⟩
        rw [markMany_length]
        exact hbound

def RequirementsCovered
    (initial : List Bool)
    (batches : List (List Nat))
    (required : List Nat) : Prop :=
  ∀ index ∈ required,
    maskBit initial index = true ∨
      ∃ batch ∈ batches, index ∈ batch

theorem requirementsCovered_replicate_false_iff
    (count : Nat) (batches : List (List Nat))
    (required : List Nat) :
    RequirementsCovered (List.replicate count false)
        batches required ↔
      ∀ index ∈ required,
        ∃ batch ∈ batches, index ∈ batch := by
  constructor
  · intro hcovered index hindex
    rcases hcovered index hindex with hinitial | hemitted
    · rw [maskBit_replicate_false] at hinitial
      contradiction
    · exact hemitted
  · intro hemitted index hindex
    exact Or.inr (hemitted index hindex)

theorem allIndicesMarked_markBatches
    (initial : List Bool)
    (batches : List (List Nat))
    (required : List Nat)
    (hcovered :
      RequirementsCovered initial batches required)
    (hbounded :
      ∀ index ∈ required, index < initial.length) :
    allIndicesMarked required (markBatches batches initial) = true := by
  rw [allIndicesMarked_correct]
  intro index hindex
  rcases hcovered index hindex with hinitial | hemitted
  · exact maskBit_markBatches_of_initial
      batches initial index hinitial
  · exact maskBit_markBatches_of_emitted
      batches initial index hemitted (hbounded index hindex)

theorem requiredMasksTerminal_of_covered
    (requirement : TerminalMaskRequirement Tag)
    (atomCount queryCount : Nat)
    (tag : Tag)
    (initialGuarded initialForbidden : List Bool)
    (guardedBatches forbiddenBatches : List (List Nat))
    (hguardedLength : initialGuarded.length = atomCount)
    (hforbiddenLength : initialForbidden.length = queryCount)
    (hguardedCovered :
      RequirementsCovered initialGuarded guardedBatches
        (requirement.guarded tag))
    (hforbiddenCovered :
      RequirementsCovered initialForbidden forbiddenBatches
        (requirement.forbidden tag))
    (hguardedBounded :
      ∀ index ∈ requirement.guarded tag,
        index < initialGuarded.length)
    (hforbiddenBounded :
      ∀ index ∈ requirement.forbidden tag,
        index < initialForbidden.length) :
    let finalState :
        ValidGeneralizedState Tag atomCount queryCount :=
      ⟨{
          tag := tag
          guarded := markBatches guardedBatches initialGuarded
          forbidden := markBatches forbiddenBatches initialForbidden
        },
        by
          constructor
          · rw [markBatches_length, hguardedLength]
          · rw [markBatches_length, hforbiddenLength]⟩
    requiredMasksTerminal requirement atomCount queryCount
      finalState = true := by
  dsimp only
  simp only [requiredMasksTerminal, Bool.and_eq_true]
  exact ⟨
    allIndicesMarked_markBatches
      initialGuarded guardedBatches (requirement.guarded tag)
      hguardedCovered hguardedBounded,
    allIndicesMarked_markBatches
      initialForbidden forbiddenBatches (requirement.forbidden tag)
      hforbiddenCovered hforbiddenBounded⟩

theorem allCanonicalForbiddenTerminal_of_covered
    [DecidableEq Query]
    (queries : Enumeration Query)
    (guardedRequired : Tag → List Nat)
    (atomCount : Nat)
    (tag : Tag)
    (initialGuarded initialForbidden : List Bool)
    (guardedBatches forbiddenBatches : List (List Nat))
    (hguardedLength : initialGuarded.length = atomCount)
    (hforbiddenLength :
      initialForbidden.length = queries.values.length)
    (hguardedCovered :
      RequirementsCovered initialGuarded guardedBatches
        (guardedRequired tag))
    (hforbiddenCovered :
      RequirementsCovered initialForbidden forbiddenBatches
        (allCanonicalQueryIndices queries))
    (hguardedBounded :
      ∀ index ∈ guardedRequired tag,
        index < initialGuarded.length) :
    let finalState :
        ValidGeneralizedState Tag atomCount queries.values.length :=
      ⟨{
          tag := tag
          guarded := markBatches guardedBatches initialGuarded
          forbidden := markBatches forbiddenBatches initialForbidden
        },
        by
          constructor
          · rw [markBatches_length, hguardedLength]
          · rw [markBatches_length, hforbiddenLength]⟩
    requiredMasksTerminal
      (allCanonicalForbiddenRequirement queries guardedRequired)
      atomCount queries.values.length finalState = true := by
  apply requiredMasksTerminal_of_covered
    (allCanonicalForbiddenRequirement queries guardedRequired)
    atomCount queries.values.length tag
    initialGuarded initialForbidden
    guardedBatches forbiddenBatches
    hguardedLength hforbiddenLength
    hguardedCovered hforbiddenCovered hguardedBounded
  intro index hindex
  rw [hforbiddenLength]
  exact allCanonicalQueryIndices_bounded queries index hindex

end NSSE
