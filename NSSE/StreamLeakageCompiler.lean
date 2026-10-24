import NSSE.AutomataSOA
import NSSE.GuardedCompiler
import NSSE.CompilerSemantics

/-!
# Executable recognition of the before-source leakage branch

The finite event-stream semantics in `AutomataSOA` is converted here to
an exact Boolean test.  This is one concrete compiler branch: accepting
the test certifies that the restored top word is covered and hence is
not an SOA avoider.
-/

namespace NSSE

universe u vc vl vr

def checkBeforeSourceLoops
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR) (left : DFA α QL) :
    List (InsertionEvent α) → Word α → Nat → Nat → Bool
  | [], _, _, _ => true
  | event :: events, w, j, t =>
      decide (event.slot ≤ j) &&
      (decide
          (I.candidate.runFrom
              (I.candidate.run (w.take event.slot)) event.payload =
            I.candidate.run (w.take event.slot)) &&
        (decide
            (left.runFrom
                (left.run (w.take event.slot)) event.payload =
              left.run (w.take event.slot)) &&
          checkBeforeSourceLoops I left events (event.apply w)
            (j + event.payload.length) (t + event.payload.length)))

theorem checkBeforeSourceLoops_correct
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR) (left : DFA α QL)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat) :
    checkBeforeSourceLoops I left events w j t = true ↔
      AutomataSOAInstance.BeforeSourceLoopStream
        I left events w j t := by
  induction events generalizing w j t with
  | nil =>
      constructor
      · intro _
        exact .nil w j t
      · intro _
        rfl
  | cons event events ih =>
      simp only [checkBeforeSourceLoops, Bool.and_eq_true,
        decide_eq_true_eq, ih]
      constructor
      · rintro ⟨hslot, hcandidateLoop, hleftLoop, htail⟩
        exact .cons event hslot hcandidateLoop hleftLoop htail
      · intro hstream
        cases hstream with
        | cons _ hslot hcandidateLoop hleftLoop htail =>
            exact ⟨hslot, hcandidateLoop, hleftLoop, htail⟩

/--
Compiler-facing soundness of the executable branch: a successful stream
test, together with the selected bottom occurrence, rules out avoidance
of the restored word.
-/
theorem checkBeforeSourceLoops_true_contradicts_avoider
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hcheck : checkBeforeSourceLoops I left events w j t = true)
    (hjt : j < t) (ht : t < w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t) :
    ¬ I.toSOA.Avoider (InsertionEvent.applyStream events w) := by
  exact
    AutomataSOAInstance.applyStream_beforeSourceLoops_contradicts_avoider
    I left right hrow events w j t
    ((checkBeforeSourceLoops_correct I left events w j t).1 hcheck)
    hjt ht hcandidate hleft hright hoccurs

/-- Executable acceptance test for the final-state predicate of a DFA. -/
structure DFAFinalTest (A : DFA α Q) where
  test : Q → Bool
  correct : ∀ q, test q = true ↔ A.accept q

theorem DFAFinalTest.false_correct
    {α : Type u} {Q : Type vc} {A : DFA α Q}
    (finalTest : DFAFinalTest A) (q : Q) :
    finalTest.test q = false ↔ ¬ A.accept q := by
  cases htest : finalTest.test q with
  | false =>
      constructor
      · intro _ haccept
        have htrue := (finalTest.correct q).2 haccept
        rw [htest] at htrue
        contradiction
      · intro _
        rfl
  | true =>
      constructor
      · intro hfalse
        cases hfalse
      · intro hnot
        exact False.elim (hnot ((finalTest.correct q).1 htest))

/--
All response data needed when an insertion lies strictly after the source
cut and weakly before the target cut.
-/
structure BetweenCutsCertificate
    (I : AutomataSOAInstance α QC QL QR) (right : DFA α QR)
    (w payload : Word α) (slot j t : Nat) : Prop where
  source_lt_slot : j < slot
  slot_le_target : slot ≤ t
  target_lt_length : t < w.length
  candidateLoop :
    I.candidate.runFrom
        (I.candidate.run (w.take slot)) payload =
      I.candidate.run (w.take slot)
  rightResponse :
    right.Accepts
      (Word.factor (Word.insertAt w payload slot) j
        ((t + payload.length) - j))
  occurrenceResponse :
    OccursSuffixAt (Word.insertAt w payload slot)
      j (t + payload.length)

def checkBetweenCuts
    [DecidableEq α] [DecidableEq QC]
    (I : AutomataSOAInstance α QC QL QR) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (w payload : Word α) (slot j t : Nat) : Bool :=
  let restored := Word.insertAt w payload slot
  decide (j < slot) &&
    (decide (slot ≤ t) &&
      (decide (t < w.length) &&
        (decide
            (I.candidate.runFrom
                (I.candidate.run (w.take slot)) payload =
              I.candidate.run (w.take slot)) &&
          (rightFinal.test
              (right.run
                (Word.factor restored j
                  ((t + payload.length) - j))) &&
            decide
              (Word.factor restored j
                  (restored.length - (t + payload.length)) =
                Word.factor restored (t + payload.length)
                  (restored.length - (t + payload.length)))))))

theorem checkBetweenCuts_correct
    [DecidableEq α] [DecidableEq QC]
    (I : AutomataSOAInstance α QC QL QR) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (w payload : Word α) (slot j t : Nat) :
    checkBetweenCuts I right rightFinal w payload slot j t = true ↔
      BetweenCutsCertificate I right w payload slot j t := by
  simp only [checkBetweenCuts, Bool.and_eq_true, decide_eq_true_eq,
    rightFinal.correct, OccursSuffixAt]
  constructor
  · rintro ⟨hjslot, hslott, ht, hloop, hright, hoccurs⟩
    exact ⟨hjslot, hslott, ht, hloop, hright, hoccurs⟩
  · rintro ⟨hjslot, hslott, ht, hloop, hright, hoccurs⟩
    exact ⟨hjslot, hslott, ht, hloop, hright, hoccurs⟩

theorem checkBetweenCuts_true_contradicts_avoider
    [DecidableEq α] [DecidableEq QC]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (hrow : (left, right) ∈ I.rows)
    (w payload : Word α) (slot j t : Nat)
    (hcheck :
      checkBetweenCuts I right rightFinal w payload slot j t = true)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j)) :
    ¬ I.toSOA.Avoider (Word.insertAt w payload slot) := by
  have hcert :=
    (checkBetweenCuts_correct
      I right rightFinal w payload slot j t).1 hcheck
  exact
    AutomataSOAInstance.insertAt_between_response_contradicts_avoider
      I left right hrow w payload slot j t
      hcert.source_lt_slot hcert.slot_le_target
      hcert.target_lt_length hcandidate hleft hcert.candidateLoop
      hcert.rightResponse hcert.occurrenceResponse

structure AfterTargetCertificate
    (I : AutomataSOAInstance α QC QL QR)
    (w payload : Word α) (slot j t : Nat) : Prop where
  source_lt_target : j < t
  target_lt_slot : t < slot
  slot_le_length : slot ≤ w.length
  candidateLoop :
    I.candidate.runFrom
        (I.candidate.run (w.take slot)) payload =
      I.candidate.run (w.take slot)
  occurrenceResponse :
    OccursSuffixAt (Word.insertAt w payload slot) j t

def checkAfterTarget
    [DecidableEq α] [DecidableEq QC]
    (I : AutomataSOAInstance α QC QL QR)
    (w payload : Word α) (slot j t : Nat) : Bool :=
  let restored := Word.insertAt w payload slot
  decide (j < t) &&
    (decide (t < slot) &&
      (decide (slot ≤ w.length) &&
        (decide
            (I.candidate.runFrom
                (I.candidate.run (w.take slot)) payload =
              I.candidate.run (w.take slot)) &&
          decide
            (Word.factor restored j (restored.length - t) =
              Word.factor restored t (restored.length - t)))))

theorem checkAfterTarget_correct
    [DecidableEq α] [DecidableEq QC]
    (I : AutomataSOAInstance α QC QL QR)
    (w payload : Word α) (slot j t : Nat) :
    checkAfterTarget I w payload slot j t = true ↔
      AfterTargetCertificate I w payload slot j t := by
  simp only [checkAfterTarget, Bool.and_eq_true, decide_eq_true_eq,
    OccursSuffixAt]
  constructor
  · rintro ⟨hjt, htslot, hslot, hloop, hoccurs⟩
    exact ⟨hjt, htslot, hslot, hloop, hoccurs⟩
  · rintro ⟨hjt, htslot, hslot, hloop, hoccurs⟩
    exact ⟨hjt, htslot, hslot, hloop, hoccurs⟩

theorem checkAfterTarget_true_contradicts_avoider
    [DecidableEq α] [DecidableEq QC]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w payload : Word α) (slot j t : Nat)
    (hcheck : checkAfterTarget I w payload slot j t = true)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j))) :
    ¬ I.toSOA.Avoider (Word.insertAt w payload slot) := by
  have hcert :=
    (checkAfterTarget_correct I w payload slot j t).1 hcheck
  exact
    AutomataSOAInstance.insertAt_after_response_contradicts_avoider
      I left right hrow w payload slot j t
      hcert.source_lt_target hcert.target_lt_slot hcert.slot_le_length
      hcandidate hleft hright hcert.candidateLoop
      hcert.occurrenceResponse

/--
Executable first-event dispatcher for all three placements relative to a
selected witness.  Each branch invokes its exact response checker.
-/
def checkFirstEventLeakage
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) : Bool :=
  match classifyCutPlacement event.slot j t with
  | .beforeSource =>
      checkBeforeSourceLoops I left [event] w j t
  | .betweenCuts =>
      checkBetweenCuts I right rightFinal
        w event.payload event.slot j t
  | .afterTarget =>
      checkAfterTarget I w event.payload event.slot j t

/--
Unified soundness of the finite first-event compiler branch.  A successful
Boolean outcome in any placement class transports or reconstructs the
selected row witness and therefore excludes the restored word.
-/
theorem checkFirstEventLeakage_true_contradicts_avoider
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (hrow : (left, right) ∈ I.rows)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hcheck :
      checkFirstEventLeakage I left right rightFinal
        event w j t = true)
    (hjt : j < t) (ht : t < w.length)
    (hcandidate : I.toSOA.candidate w)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t) :
    ¬ I.toSOA.Avoider (event.apply w) := by
  unfold checkFirstEventLeakage at hcheck
  cases hplacement : classifyCutPlacement event.slot j t with
  | beforeSource =>
      simp [hplacement] at hcheck
      have hnot :=
        checkBeforeSourceLoops_true_contradicts_avoider
          I left right hrow [event] w j t hcheck hjt ht
          hcandidate hleft hright hoccurs
      simpa [InsertionEvent.applyStream, InsertionEvent.apply] using hnot
  | betweenCuts =>
      simp [hplacement] at hcheck
      exact checkBetweenCuts_true_contradicts_avoider
        I left right rightFinal hrow
        w event.payload event.slot j t hcheck hcandidate hleft
  | afterTarget =>
      simp [hplacement] at hcheck
      exact checkAfterTarget_true_contradicts_avoider
        I left right hrow w event.payload event.slot j t hcheck
        hcandidate hleft hright

/--
Finite exhaustive result of processing one restoration event.  Besides
the successful leakage certificate, every failed atomic guard has its
own constructor, so no Boolean failure is silently discarded.
-/
inductive FirstEventOutcome
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) : Prop where
  | leakage
      (success :
        checkFirstEventLeakage I left right rightFinal
          event w j t = true) :
      FirstEventOutcome I left right rightFinal event w j t
  | candidateLoopFailed
      (failed :
        I.candidate.runFrom
            (I.candidate.run (w.take event.slot)) event.payload ≠
          I.candidate.run (w.take event.slot)) :
      FirstEventOutcome I left right rightFinal event w j t
  | beforeLeftLoopFailed
      (placement :
        classifyCutPlacement event.slot j t = .beforeSource)
      (failed :
        left.runFrom
            (left.run (w.take event.slot)) event.payload ≠
          left.run (w.take event.slot)) :
      FirstEventOutcome I left right rightFinal event w j t
  | betweenRightRejected
      (placement :
        classifyCutPlacement event.slot j t = .betweenCuts)
      (failed :
        ¬ right.Accepts
          (Word.factor (event.apply w) j
            ((t + event.payload.length) - j))) :
      FirstEventOutcome I left right rightFinal event w j t
  | betweenOccurrenceMismatch
      (placement :
        classifyCutPlacement event.slot j t = .betweenCuts)
      (failed :
        ¬ OccursSuffixAt (event.apply w)
          j (t + event.payload.length)) :
      FirstEventOutcome I left right rightFinal event w j t
  | afterInvalidSlot
      (placement :
        classifyCutPlacement event.slot j t = .afterTarget)
      (failed : ¬ event.slot ≤ w.length) :
      FirstEventOutcome I left right rightFinal event w j t
  | afterOccurrenceMismatch
      (placement :
        classifyCutPlacement event.slot j t = .afterTarget)
      (failed :
        ¬ OccursSuffixAt (event.apply w) j t) :
      FirstEventOutcome I left right rightFinal event w j t

/--
Completeness of the first-event dispatcher relative to one selected
bottom witness geometry: every event either yields leakage or one exact
failed atomic guard.
-/
theorem firstEventOutcome_exhaustive
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length) :
    FirstEventOutcome I left right rightFinal event w j t := by
  by_cases hcandidateLoop :
      I.candidate.runFrom
          (I.candidate.run (w.take event.slot)) event.payload =
        I.candidate.run (w.take event.slot)
  · cases hplacement :
        classifyCutPlacement event.slot j t with
    | beforeSource =>
        have hslot :
            event.slot ≤ j :=
          (classifyCutPlacement_before_iff
            event.slot j t hjt).1 hplacement
        by_cases hleftLoop :
            left.runFrom
                (left.run (w.take event.slot)) event.payload =
              left.run (w.take event.slot)
        · apply FirstEventOutcome.leakage
          unfold checkFirstEventLeakage
          rw [hplacement]
          apply (checkBeforeSourceLoops_correct
            I left [event] w j t).2
          exact .cons event hslot hcandidateLoop hleftLoop
            (.nil (event.apply w)
              (j + event.payload.length)
              (t + event.payload.length))
        · exact .beforeLeftLoopFailed hplacement hleftLoop
    | betweenCuts =>
        have hbetween :
            j < event.slot ∧ event.slot ≤ t :=
          (classifyCutPlacement_between_iff
            event.slot j t hjt).1 hplacement
        let restored := event.apply w
        let rightFactor :=
          Word.factor restored j
            ((t + event.payload.length) - j)
        by_cases hright : right.Accepts rightFactor
        · by_cases hoccurs :
            OccursSuffixAt restored j (t + event.payload.length)
          · apply FirstEventOutcome.leakage
            unfold checkFirstEventLeakage
            rw [hplacement]
            apply (checkBetweenCuts_correct
              I right rightFinal w event.payload
                event.slot j t).2
            exact ⟨hbetween.1, hbetween.2, ht,
              hcandidateLoop, hright, hoccurs⟩
          · exact .betweenOccurrenceMismatch hplacement hoccurs
        · exact .betweenRightRejected hplacement hright
    | afterTarget =>
        have hafter : t < event.slot :=
          (classifyCutPlacement_after_iff
            event.slot j t hjt).1 hplacement
        by_cases hslot : event.slot ≤ w.length
        · by_cases hoccurs :
            OccursSuffixAt (event.apply w) j t
          · apply FirstEventOutcome.leakage
            unfold checkFirstEventLeakage
            rw [hplacement]
            apply (checkAfterTarget_correct
              I w event.payload event.slot j t).2
            exact ⟨hjt, hafter, hslot, hcandidateLoop, hoccurs⟩
          · exact .afterOccurrenceMismatch hplacement hoccurs
        · exact .afterInvalidSlot hplacement hslot
  · exact .candidateLoopFailed hcandidateLoop

/-- The non-leakage terminals retained by the first-event compiler. -/
inductive FirstEventFailure
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) : Prop where
  | candidateLoop
      (failed :
        I.candidate.runFrom
            (I.candidate.run (w.take event.slot)) event.payload ≠
          I.candidate.run (w.take event.slot)) :
      FirstEventFailure I left right event w j t
  | beforeLeftLoop
      (placement :
        classifyCutPlacement event.slot j t = .beforeSource)
      (failed :
        left.runFrom
            (left.run (w.take event.slot)) event.payload ≠
          left.run (w.take event.slot)) :
      FirstEventFailure I left right event w j t
  | betweenRight
      (placement :
        classifyCutPlacement event.slot j t = .betweenCuts)
      (failed :
        ¬ right.Accepts
          (Word.factor (event.apply w) j
            ((t + event.payload.length) - j))) :
      FirstEventFailure I left right event w j t
  | betweenOccurrence
      (placement :
        classifyCutPlacement event.slot j t = .betweenCuts)
      (failed :
        ¬ OccursSuffixAt (event.apply w)
          j (t + event.payload.length)) :
      FirstEventFailure I left right event w j t
  | afterSlot
      (placement :
        classifyCutPlacement event.slot j t = .afterTarget)
      (failed : ¬ event.slot ≤ w.length) :
      FirstEventFailure I left right event w j t
  | afterOccurrence
      (placement :
        classifyCutPlacement event.slot j t = .afterTarget)
      (failed :
        ¬ OccursSuffixAt (event.apply w) j t) :
      FirstEventFailure I left right event w j t

/--
Compiler-facing totality: one event always produces either the successful
Boolean leakage certificate or one finite failure terminal.
-/
theorem firstEvent_success_or_failure
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length) :
    checkFirstEventLeakage I left right rightFinal
        event w j t = true ∨
      FirstEventFailure I left right event w j t := by
  have houtcome :=
    firstEventOutcome_exhaustive
      I left right rightFinal event w j t hjt ht
  cases houtcome with
  | leakage success => exact Or.inl success
  | candidateLoopFailed failed =>
      exact Or.inr (.candidateLoop failed)
  | beforeLeftLoopFailed placement failed =>
      exact Or.inr (.beforeLeftLoop placement failed)
  | betweenRightRejected placement failed =>
      exact Or.inr (.betweenRight placement failed)
  | betweenOccurrenceMismatch placement failed =>
      exact Or.inr (.betweenOccurrence placement failed)
  | afterInvalidSlot placement failed =>
      exact Or.inr (.afterSlot placement failed)
  | afterOccurrenceMismatch placement failed =>
      exact Or.inr (.afterOccurrence placement failed)

theorem firstEventFailure_not_success
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hfailure : FirstEventFailure I left right event w j t) :
    checkFirstEventLeakage I left right rightFinal
        event w j t ≠ true := by
  intro hsuccess
  cases hfailure with
  | candidateLoop failed =>
      unfold checkFirstEventLeakage at hsuccess
      cases hplacement :
          classifyCutPlacement event.slot j t with
      | beforeSource =>
          rw [hplacement] at hsuccess
          have hstream :=
            (checkBeforeSourceLoops_correct
              I left [event] w j t).1 hsuccess
          cases hstream with
          | cons _ _ hloop _ _ => exact failed hloop
      | betweenCuts =>
          rw [hplacement] at hsuccess
          have hcert :=
            (checkBetweenCuts_correct I right rightFinal
              w event.payload event.slot j t).1 hsuccess
          exact failed hcert.candidateLoop
      | afterTarget =>
          rw [hplacement] at hsuccess
          have hcert :=
            (checkAfterTarget_correct I
              w event.payload event.slot j t).1 hsuccess
          exact failed hcert.candidateLoop
  | beforeLeftLoop placement failed =>
      unfold checkFirstEventLeakage at hsuccess
      rw [placement] at hsuccess
      have hstream :=
        (checkBeforeSourceLoops_correct
          I left [event] w j t).1 hsuccess
      cases hstream with
      | cons _ _ _ hloop _ => exact failed hloop
  | betweenRight placement failed =>
      unfold checkFirstEventLeakage at hsuccess
      rw [placement] at hsuccess
      have hcert :=
        (checkBetweenCuts_correct I right rightFinal
          w event.payload event.slot j t).1 hsuccess
      exact failed hcert.rightResponse
  | betweenOccurrence placement failed =>
      unfold checkFirstEventLeakage at hsuccess
      rw [placement] at hsuccess
      have hcert :=
        (checkBetweenCuts_correct I right rightFinal
          w event.payload event.slot j t).1 hsuccess
      exact failed hcert.occurrenceResponse
  | afterSlot placement failed =>
      unfold checkFirstEventLeakage at hsuccess
      rw [placement] at hsuccess
      have hcert :=
        (checkAfterTarget_correct I
          w event.payload event.slot j t).1 hsuccess
      exact failed hcert.slot_le_length
  | afterOccurrence placement failed =>
      unfold checkFirstEventLeakage at hsuccess
      rw [placement] at hsuccess
      have hcert :=
        (checkAfterTarget_correct I
          w event.payload event.slot j t).1 hsuccess
      exact failed hcert.occurrenceResponse

theorem firstEvent_check_false_iff_failure
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length) :
    checkFirstEventLeakage I left right rightFinal event w j t = false ↔
      FirstEventFailure I left right event w j t := by
  constructor
  · intro hfalse
    rcases firstEvent_success_or_failure
        I left right rightFinal event w j t hjt ht with
      hsuccess | hfailure
    · rw [hfalse] at hsuccess
      contradiction
    · exact hfailure
  · intro hfailure
    have hntrue :=
      firstEventFailure_not_success
        I left right rightFinal event w j t hfailure
    cases hvalue :
        checkFirstEventLeakage I left right rightFinal event w j t
    · rfl
    · exact False.elim (hntrue hvalue)

inductive FirstEventFailureKind
  | candidateLoop
  | beforeLeftLoop
  | betweenRight
  | betweenOccurrence
  | afterSlot
  | afterOccurrence
deriving DecidableEq

def firstEventFailureKindEnumeration :
    Enumeration FirstEventFailureKind where
  values := [.candidateLoop, .beforeLeftLoop, .betweenRight,
    .betweenOccurrence, .afterSlot, .afterOccurrence]
  complete := by
    intro kind
    cases kind <;> simp

namespace FirstEventFailure

inductive HasKind :
    FirstEventFailure I left right event w j t →
      FirstEventFailureKind → Prop where
  | candidateLoop (failed) :
      HasKind (.candidateLoop failed) .candidateLoop
  | beforeLeftLoop (placement) (failed) :
      HasKind (.beforeLeftLoop placement failed) .beforeLeftLoop
  | betweenRight (placement) (failed) :
      HasKind (.betweenRight placement failed) .betweenRight
  | betweenOccurrence (placement) (failed) :
      HasKind (.betweenOccurrence placement failed) .betweenOccurrence
  | afterSlot (placement) (failed) :
      HasKind (.afterSlot placement failed) .afterSlot
  | afterOccurrence (placement) (failed) :
      HasKind (.afterOccurrence placement failed) .afterOccurrence

theorem exists_enumerated_kind
    (failure : FirstEventFailure I left right event w j t) :
    ∃ kind ∈ firstEventFailureKindEnumeration.values,
      HasKind failure kind := by
  cases failure with
  | candidateLoop failed =>
      exact ⟨.candidateLoop, by simp [firstEventFailureKindEnumeration],
        .candidateLoop failed⟩
  | beforeLeftLoop placement failed =>
      exact ⟨.beforeLeftLoop, by simp [firstEventFailureKindEnumeration],
        .beforeLeftLoop placement failed⟩
  | betweenRight placement failed =>
      exact ⟨.betweenRight, by simp [firstEventFailureKindEnumeration],
        .betweenRight placement failed⟩
  | betweenOccurrence placement failed =>
      exact ⟨.betweenOccurrence,
        by simp [firstEventFailureKindEnumeration],
        .betweenOccurrence placement failed⟩
  | afterSlot placement failed =>
      exact ⟨.afterSlot, by simp [firstEventFailureKindEnumeration],
        .afterSlot placement failed⟩
  | afterOccurrence placement failed =>
      exact ⟨.afterOccurrence,
        by simp [firstEventFailureKindEnumeration],
        .afterOccurrence placement failed⟩

end FirstEventFailure

/--
Failures discharged entirely by finite arithmetic/DFA control, without a
word-equation terminal.
-/
inductive FirstEventFiniteGuard
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) : Prop where
  | candidateLoop
      (failed :
        I.candidate.runFrom
            (I.candidate.run (w.take event.slot)) event.payload ≠
          I.candidate.run (w.take event.slot)) :
      FirstEventFiniteGuard I left right event w j t
  | beforeLeftLoop
      (placement :
        classifyCutPlacement event.slot j t = .beforeSource)
      (failed :
        left.runFrom
            (left.run (w.take event.slot)) event.payload ≠
          left.run (w.take event.slot)) :
      FirstEventFiniteGuard I left right event w j t
  | betweenRight
      (placement :
        classifyCutPlacement event.slot j t = .betweenCuts)
      (failed :
        ¬ right.Accepts
          (Word.factor (event.apply w) j
            ((t + event.payload.length) - j))) :
      FirstEventFiniteGuard I left right event w j t
  | afterSlot
      (placement :
        classifyCutPlacement event.slot j t = .afterTarget)
      (failed : ¬ event.slot ≤ w.length) :
      FirstEventFiniteGuard I left right event w j t

/--
Literal word-equation failures.  These are the two first-event terminals
that belong to the PWE/disequality solver rather than finite DFA control.
-/
inductive FirstEventPWE
    (event : InsertionEvent α) (w : Word α) (j t : Nat) : Prop where
  | betweenOccurrence
      (placement :
        classifyCutPlacement event.slot j t = .betweenCuts)
      (failed :
        ¬ OccursSuffixAt (event.apply w)
          j (t + event.payload.length)) :
      FirstEventPWE event w j t
  | afterOccurrence
      (placement :
        classifyCutPlacement event.slot j t = .afterTarget)
      (failed :
        ¬ OccursSuffixAt (event.apply w) j t) :
      FirstEventPWE event w j t

inductive FirstEventReducedTerminal
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) : Prop where
  | finiteGuard :
      FirstEventFiniteGuard I left right event w j t →
      FirstEventReducedTerminal I left right event w j t
  | pwe :
      FirstEventPWE event w j t →
      FirstEventReducedTerminal I left right event w j t

def FirstEventFailure.reduce
    (failure : FirstEventFailure I left right event w j t) :
    FirstEventReducedTerminal I left right event w j t :=
  match failure with
  | .candidateLoop failed =>
      .finiteGuard (.candidateLoop failed)
  | .beforeLeftLoop placement failed =>
      .finiteGuard (.beforeLeftLoop placement failed)
  | .betweenRight placement failed =>
      .finiteGuard (.betweenRight placement failed)
  | .betweenOccurrence placement failed =>
      .pwe (.betweenOccurrence placement failed)
  | .afterSlot placement failed =>
      .finiteGuard (.afterSlot placement failed)
  | .afterOccurrence placement failed =>
      .pwe (.afterOccurrence placement failed)

def FirstEventReducedTerminal.realize
    (terminal :
      FirstEventReducedTerminal I left right event w j t) :
    FirstEventFailure I left right event w j t :=
  match terminal with
  | .finiteGuard (.candidateLoop failed) =>
      .candidateLoop failed
  | .finiteGuard (.beforeLeftLoop placement failed) =>
      .beforeLeftLoop placement failed
  | .finiteGuard (.betweenRight placement failed) =>
      .betweenRight placement failed
  | .finiteGuard (.afterSlot placement failed) =>
      .afterSlot placement failed
  | .pwe (.betweenOccurrence placement failed) =>
      .betweenOccurrence placement failed
  | .pwe (.afterOccurrence placement failed) =>
      .afterOccurrence placement failed

theorem firstEventFailure_iff_reducedTerminal
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    FirstEventFailure I left right event w j t ↔
      FirstEventReducedTerminal I left right event w j t :=
  ⟨FirstEventFailure.reduce, FirstEventReducedTerminal.realize⟩

/-- A literal suffix-copy disequality presented as a PWE query. -/
structure SuffixDisequalityQuery (α : Type u) where
  word : Word α
  source : Nat
  target : Nat

def suffixDisequalitySolver [DecidableEq α] :
    ExactSolver (SuffixDisequalityQuery α) where
  formula := fun query =>
    Word.factor query.word query.source
        (query.word.length - query.target) ≠
      Word.factor query.word query.target
        (query.word.length - query.target)
  decide := fun query =>
    !(decide
      (Word.factor query.word query.source
          (query.word.length - query.target) =
        Word.factor query.word query.target
          (query.word.length - query.target)))
  correct := by
    intro query
    simp

def betweenOccurrenceQuery
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    SuffixDisequalityQuery α where
  word := event.apply w
  source := j
  target := t + event.payload.length

def afterOccurrenceQuery
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    SuffixDisequalityQuery α where
  word := event.apply w
  source := j
  target := t

namespace FirstEventPWE

inductive Encodes
    {α : Type u} {event : InsertionEvent α}
    {w : Word α} {j t : Nat} :
    FirstEventPWE event w j t →
      SuffixDisequalityQuery α → Prop where
  | between (placement) (failed) :
      Encodes (.betweenOccurrence placement failed)
        (betweenOccurrenceQuery event w j t)
  | after (placement) (failed) :
      Encodes (.afterOccurrence placement failed)
        (afterOccurrenceQuery event w j t)

theorem exists_exact_solved_query
    [DecidableEq α]
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (terminal : FirstEventPWE event w j t) :
    ∃ query,
      Encodes terminal query ∧
      (suffixDisequalitySolver (α := α)).decide query = true := by
  cases terminal with
  | betweenOccurrence placement failed =>
      refine ⟨betweenOccurrenceQuery event w j t,
        .between placement failed, ?_⟩
      apply
        ((suffixDisequalitySolver (α := α)).correct
          (betweenOccurrenceQuery event w j t)).2
      simpa [suffixDisequalitySolver, betweenOccurrenceQuery,
        OccursSuffixAt] using failed
  | afterOccurrence placement failed =>
      refine ⟨afterOccurrenceQuery event w j t,
        .after placement failed, ?_⟩
      apply
        ((suffixDisequalitySolver (α := α)).correct
          (afterOccurrenceQuery event w j t)).2
      simpa [suffixDisequalitySolver, afterOccurrenceQuery,
        OccursSuffixAt] using failed

end FirstEventPWE

inductive FirstEventFiniteGuardQuery
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) where
  | candidateLoop
  | beforeLeftLoop
  | betweenRight
  | afterSlot

def finiteGuardFormula
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    FirstEventFiniteGuardQuery I left right event w j t → Prop
  | .candidateLoop =>
      I.candidate.runFrom
          (I.candidate.run (w.take event.slot)) event.payload ≠
        I.candidate.run (w.take event.slot)
  | .beforeLeftLoop =>
      classifyCutPlacement event.slot j t = .beforeSource ∧
      left.runFrom
          (left.run (w.take event.slot)) event.payload ≠
        left.run (w.take event.slot)
  | .betweenRight =>
      classifyCutPlacement event.slot j t = .betweenCuts ∧
      ¬ right.Accepts
        (Word.factor (event.apply w) j
          ((t + event.payload.length) - j))
  | .afterSlot =>
      classifyCutPlacement event.slot j t = .afterTarget ∧
      ¬ event.slot ≤ w.length

def finiteGuardSolver
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    ExactSolver
      (FirstEventFiniteGuardQuery I left right event w j t) where
  formula := finiteGuardFormula I left right event w j t
  decide
    | .candidateLoop =>
        decide
          (I.candidate.runFrom
              (I.candidate.run (w.take event.slot)) event.payload ≠
            I.candidate.run (w.take event.slot))
    | .beforeLeftLoop =>
        decide
            (classifyCutPlacement event.slot j t = .beforeSource) &&
          decide
            (left.runFrom
                (left.run (w.take event.slot)) event.payload ≠
              left.run (w.take event.slot))
    | .betweenRight =>
        decide
            (classifyCutPlacement event.slot j t = .betweenCuts) &&
          !(rightFinal.test
            (right.run
              (Word.factor (event.apply w) j
                ((t + event.payload.length) - j))))
    | .afterSlot =>
        decide
            (classifyCutPlacement event.slot j t = .afterTarget) &&
          decide (¬ event.slot ≤ w.length)
  correct := by
    intro query
    cases query with
    | candidateLoop => simp [finiteGuardFormula]
    | beforeLeftLoop => simp [finiteGuardFormula]
    | betweenRight =>
        simp [finiteGuardFormula, rightFinal.false_correct, DFA.Accepts]
    | afterSlot => simp [finiteGuardFormula]

namespace FirstEventFiniteGuard

inductive Encodes
    {α : Type u} {QC : Type vc} {QL : Type vl} {QR : Type vr}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat} :
    FirstEventFiniteGuard I left right event w j t →
      FirstEventFiniteGuardQuery I left right event w j t → Prop where
  | candidateLoop (failed) :
      Encodes (.candidateLoop failed) .candidateLoop
  | beforeLeftLoop (placement) (failed) :
      Encodes (.beforeLeftLoop placement failed) .beforeLeftLoop
  | betweenRight (placement) (failed) :
      Encodes (.betweenRight placement failed) .betweenRight
  | afterSlot (placement) (failed) :
      Encodes (.afterSlot placement failed) .afterSlot

theorem exists_exact_solved_query
    [DecidableEq QC] [DecidableEq QL]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    (rightFinal : DFAFinalTest right)
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (terminal : FirstEventFiniteGuard I left right event w j t) :
    ∃ query,
      Encodes terminal query ∧
      (finiteGuardSolver I left right rightFinal
        event w j t).decide query = true := by
  cases terminal with
  | candidateLoop failed =>
      refine ⟨.candidateLoop, .candidateLoop failed, ?_⟩
      apply
        ((finiteGuardSolver I left right rightFinal
          event w j t).correct .candidateLoop).2
      exact failed
  | beforeLeftLoop placement failed =>
      refine ⟨.beforeLeftLoop,
        .beforeLeftLoop placement failed, ?_⟩
      apply
        ((finiteGuardSolver I left right rightFinal
          event w j t).correct .beforeLeftLoop).2
      exact ⟨placement, failed⟩
  | betweenRight placement failed =>
      refine ⟨.betweenRight, .betweenRight placement failed, ?_⟩
      apply
        ((finiteGuardSolver I left right rightFinal
          event w j t).correct .betweenRight).2
      exact ⟨placement, failed⟩
  | afterSlot placement failed =>
      refine ⟨.afterSlot, .afterSlot placement failed, ?_⟩
      apply
        ((finiteGuardSolver I left right rightFinal
          event w j t).correct .afterSlot).2
      exact ⟨placement, failed⟩

end FirstEventFiniteGuard

inductive FirstEventTerminalQuery
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) where
  | finiteGuard :
      FirstEventFiniteGuardQuery I left right event w j t →
      FirstEventTerminalQuery I left right event w j t
  | pwe :
      SuffixDisequalityQuery α →
      FirstEventTerminalQuery I left right event w j t

def firstEventTerminalSolver
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    ExactSolver (FirstEventTerminalQuery I left right event w j t) where
  formula
    | .finiteGuard query =>
        (finiteGuardSolver I left right rightFinal
          event w j t).formula query
    | .pwe query =>
        (suffixDisequalitySolver (α := α)).formula query
  decide
    | .finiteGuard query =>
        (finiteGuardSolver I left right rightFinal
          event w j t).decide query
    | .pwe query =>
        (suffixDisequalitySolver (α := α)).decide query
  correct := by
    intro query
    cases query with
    | finiteGuard query =>
        exact (finiteGuardSolver I left right rightFinal
          event w j t).correct query
    | pwe query =>
        exact (suffixDisequalitySolver (α := α)).correct query

inductive FirstEventReducedTerminal.Encodes
    {α : Type u} {QC : Type vc} {QL : Type vl} {QR : Type vr}
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat} :
    FirstEventReducedTerminal I left right event w j t →
      FirstEventTerminalQuery I left right event w j t → Prop where
  | finiteGuard
      {terminal : FirstEventFiniteGuard I left right event w j t}
      {query : FirstEventFiniteGuardQuery
        I left right event w j t}
      (encodes : FirstEventFiniteGuard.Encodes terminal query) :
      FirstEventReducedTerminal.Encodes (.finiteGuard terminal)
        (.finiteGuard query)
  | pwe
      {terminal : FirstEventPWE event w j t}
      {query : SuffixDisequalityQuery α}
      (encodes : FirstEventPWE.Encodes terminal query) :
      FirstEventReducedTerminal.Encodes (.pwe terminal) (.pwe query)

theorem FirstEventReducedTerminal.exists_exact_solved_query
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    (rightFinal : DFAFinalTest right)
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    (terminal :
      FirstEventReducedTerminal I left right event w j t) :
    ∃ query,
      FirstEventReducedTerminal.Encodes terminal query ∧
      (firstEventTerminalSolver I left right rightFinal
        event w j t).decide query = true := by
  cases terminal with
  | finiteGuard finiteTerminal =>
      obtain ⟨query, hencodes, hsolved⟩ :=
        FirstEventFiniteGuard.exists_exact_solved_query
          rightFinal finiteTerminal
      exact ⟨.finiteGuard query, .finiteGuard hencodes, hsolved⟩
  | pwe pweTerminal =>
      obtain ⟨query, hencodes, hsolved⟩ :=
        FirstEventPWE.exists_exact_solved_query pweTerminal
      exact ⟨.pwe query, .pwe hencodes, hsolved⟩

/--
End-to-end completeness of the false branch: Boolean failure of the
leakage checker yields a concrete query accepted by one unified exact
terminal solver.
-/
theorem firstEvent_check_false_has_solved_terminal
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length)
    (hfalse :
      checkFirstEventLeakage I left right rightFinal
        event w j t = false) :
    ∃ query,
      (firstEventTerminalSolver I left right rightFinal
        event w j t).decide query = true := by
  have hfailure :=
    (firstEvent_check_false_iff_failure
      I left right rightFinal event w j t hjt ht).1 hfalse
  obtain ⟨query, _, hsolved⟩ :=
    FirstEventReducedTerminal.exists_exact_solved_query
      rightFinal hfailure.reduce
  exact ⟨query, hsolved⟩

def exactSolverTerminal
    (solver : ExactSolver Input) (_state : Unit) (input : Input) : Prop :=
  solver.decide input = true

def noCompilerCompose
    (_rule : CompilerRule Unit) (_children : List Input)
    (_input : Input) : Prop :=
  False

/--
An exact solver is itself a zero-child compiler: its accepted inputs are
precisely its terminal derivations and precisely its semantic formulas.
-/
theorem exactSolver_derives_iff_formula
    (solver : ExactSolver Input) (input : Input) :
    CompilerDerives (exactSolverTerminal solver)
        (noCompilerCompose (Input := Input)) () input ↔
      solver.formula input := by
  constructor
  · intro hderive
    exact CompilerDerives.sound
      (Semantic := fun _ witness => solver.formula witness)
      (fun {state witness} hterminal =>
        (solver.correct witness).1 hterminal)
      (fun {rule witnesses witness} _ hcompose =>
        False.elim hcompose)
      hderive
  · intro hformula
    exact .terminal ((solver.correct input).2 hformula)

/--
The failed first-event branch now produces a literal finite compiler
derivation, not merely an accepted Boolean query.
-/
theorem firstEvent_check_false_derives_terminal
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length)
    (hfalse :
      checkFirstEventLeakage I left right rightFinal
        event w j t = false) :
    ∃ query,
      CompilerDerives
        (exactSolverTerminal
          (firstEventTerminalSolver I left right rightFinal
            event w j t))
        (noCompilerCompose
          (Input :=
            FirstEventTerminalQuery I left right event w j t))
        () query := by
  obtain ⟨query, hsolved⟩ :=
    firstEvent_check_false_has_solved_terminal
      I left right rightFinal event w j t hjt ht hfalse
  exact ⟨query, .terminal hsolved⟩

end NSSE
