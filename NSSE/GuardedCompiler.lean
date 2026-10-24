import NSSE.GuardedSquare
import NSSE.EventStream
import NSSE.TaggedCompiler

/-!
# Executable guarded-square and stream outcomes

Concrete compiler-facing classifications for two cases in Section 7:
same-payload insertion holonomy and finite restoration-event streams.
-/

namespace NSSE

universe u

inductive CutPlacement
  | beforeSource
  | betweenCuts
  | afterTarget
deriving DecidableEq

def classifyCutPlacement (slot j t : Nat) : CutPlacement :=
  if slot ≤ j then .beforeSource
  else if slot ≤ t then .betweenCuts
  else .afterTarget

theorem classifyCutPlacement_before_iff
    (slot j t : Nat) (_hjt : j < t) :
    classifyCutPlacement slot j t = .beforeSource ↔ slot ≤ j := by
  unfold classifyCutPlacement
  by_cases hsource : slot ≤ j
  · simp [hsource]
  · by_cases htarget : slot ≤ t <;>
      simp [hsource, htarget]

theorem classifyCutPlacement_between_iff
    (slot j t : Nat) (_hjt : j < t) :
    classifyCutPlacement slot j t = .betweenCuts ↔
      j < slot ∧ slot ≤ t := by
  unfold classifyCutPlacement
  by_cases hsource : slot ≤ j
  · simp [hsource]
    omega
  · by_cases htarget : slot ≤ t
    · simp [hsource, htarget]
      omega
    · simp [hsource, htarget]

theorem classifyCutPlacement_after_iff
    (slot j t : Nat) (hjt : j < t) :
    classifyCutPlacement slot j t = .afterTarget ↔ t < slot := by
  unfold classifyCutPlacement
  by_cases hsource : slot ≤ j
  · simp [hsource]
    omega
  · by_cases htarget : slot ≤ t
    · simp [hsource, htarget]
    · simp [hsource, htarget]
      omega

theorem cutPlacement_exhaustive (slot j t : Nat) (_hjt : j < t) :
    slot ≤ j ∨ (j < slot ∧ slot ≤ t) ∨ t < slot := by
  omega

def cutPlacementEnumeration : Enumeration CutPlacement where
  values := [.beforeSource, .betweenCuts, .afterTarget]
  complete := by
    intro placement
    cases placement <;> simp

namespace Word

inductive InsertionSquareOutcome
    (A T B X : Word α) : Prop where
  | periodic
      (root : Word α) (m n : Nat)
      (primitive : root.IsPrimitive)
      (payloadPositive : 0 < m)
      (payloadPower : X = power root m)
      (middlePower : T = power root n) :
      InsertionSquareOutcome A T B X
  | mismatch
      (different :
        insertAt (A ++ T ++ B) X A.length ≠
          insertAt (A ++ T ++ B) X
            (A.length + T.length)) :
      InsertionSquareOutcome A T B X

/--
Every guarded same-payload insertion square is classified exactly as a
primitive-root periodic terminal or a concrete failed edge.
-/
theorem classify_insertion_square
    (A T B X : Word α) (hX : X ≠ []) :
    InsertionSquareOutcome A T B X := by
  by_cases heq :
      insertAt (A ++ T ++ B) X A.length =
        insertAt (A ++ T ++ B) X (A.length + T.length)
  · obtain ⟨root, m, n, hprimitive, hm, hXpower, hTpower⟩ :=
      (insertion_holonomy_iff_common_primitive A T B X hX).1 heq
    exact .periodic root m n hprimitive hm hXpower hTpower
  · exact .mismatch heq

theorem periodic_outcome_gives_flat
    {A T B X : Word α} {root : Word α} {m n : Nat}
    (hprimitive : root.IsPrimitive) (hm : 0 < m)
    (hX : X = power root m) (hT : T = power root n) :
    insertAt (A ++ T ++ B) X A.length =
      insertAt (A ++ T ++ B) X (A.length + T.length) := by
  apply (insertion_holonomy_iff_common_primitive A T B X ?_).2
  · exact ⟨root, m, n, hprimitive, hm, hX, hT⟩
  · intro hnil
    have hroot : root ≠ [] := by
      intro hroot
      apply hprimitive
      exact ⟨[], 2, by omega, by simp [hroot]⟩
    have hlength := congrArg List.length hX
    rw [hnil, power_length] at hlength
    have hrootLength : 0 < root.length :=
      List.length_pos_iff.mpr hroot
    have hproduct : 0 < m * root.length :=
      Nat.mul_pos hm hrootLength
    simp at hlength
    omega

/-- The two genuinely disjoint restoration orders are the flat branch. -/
theorem disjoint_square_flat
    (A T B X Y : Word α) :
    insertAt (insertAt (A ++ T ++ B) X A.length)
        Y (A.length + X.length + T.length) =
      insertAt (insertAt (A ++ T ++ B) Y
        (A.length + T.length)) X A.length :=
  disjoint_insertions_commute A T B X Y

end Word

inductive GuardedStreamOutcome [DecidableEq γ]
    (left right : List γ) : Type u where
  | identity (same : left = right) :
      GuardedStreamOutcome left right
  | firstMismatch (divergence : StreamDivergence left right) :
      GuardedStreamOutcome left right

def classifyGuardedStream [DecidableEq γ]
    (left right : List γ) : GuardedStreamOutcome left right :=
  if same : left = right then
    .identity same
  else
    .firstMismatch ((streamDivergence_iff_ne left right).2 same)

theorem guardedStream_identity_iff
    [DecidableEq γ] {left right : List γ} :
    (∃ h, classifyGuardedStream left right =
      GuardedStreamOutcome.identity h) ↔ left = right := by
  constructor
  · rintro ⟨h, _⟩
    exact h
  · intro h
    subst right
    exact ⟨rfl, by simp [classifyGuardedStream]⟩

theorem guardedStream_mismatch_iff
    [DecidableEq γ] {left right : List γ} :
    (∃ h, classifyGuardedStream left right =
      GuardedStreamOutcome.firstMismatch h) ↔ left ≠ right := by
  constructor
  · rintro ⟨h, _⟩
    exact h.ne
  · intro hne
    refine ⟨(streamDivergence_iff_ne left right).2 hne, ?_⟩
    simp [classifyGuardedStream, hne]

end NSSE
