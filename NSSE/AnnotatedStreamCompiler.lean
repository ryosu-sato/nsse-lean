import NSSE.EventStreamCompiler
import NSSE.StreamLeakageCompiler

/-!
# Restoration compiler with classified head responses

The structural stream compiler is decorated here with the exact
first-event result.  Every unary rule records either successful leakage
or the reduced finite-guard/PWE failure terminal for its head event.
-/

namespace NSSE

universe u vc vl vr

def HeadResponse
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) : Prop :=
  checkFirstEventLeakage I left right rightFinal event w j t = true ∨
    FirstEventReducedTerminal I left right event w j t

theorem headResponse_total
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length) :
    HeadResponse I left right rightFinal event w j t := by
  rcases firstEvent_success_or_failure
      I left right rightFinal event w j t hjt ht with
    hsuccess | hfailure
  · exact Or.inl hsuccess
  · exact Or.inr hfailure.reduce

inductive AnnotatedRestorationCompose
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right) :
    CompilerRule Unit → List (RestorationProblem α) →
      RestorationProblem α → Prop where
  | step
      (event : InsertionEvent α) (events : List (InsertionEvent α))
      (w : Word α) (j t : Nat)
      (slot_le_length : event.slot ≤ w.length)
      (source_lt_target : j < t)
      (target_lt_length : t < w.length)
      (response :
        HeadResponse I left right rightFinal event w j t) :
      AnnotatedRestorationCompose I left right rightFinal
        restorationRule
        [restorationTail event events w j t]
        ⟨event :: events, w, j, t⟩

def annotatedRestorationCompiler
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right) :
    LocalCompilerSemantics Unit (RestorationProblem α) where
  Semantic := fun _ problem => RestorationWellFormed problem
  Terminal := RestorationTerminal
  Compose := AnnotatedRestorationCompose I left right rightFinal
  size := fun problem => problem.events.length
  terminal_sound := by
    intro state problem hterminal
    exact hterminal.2
  rule_sound := by
    intro rule witnesses problem hchildren hcompose
    cases hcompose with
    | step event events w j t hslot hjt ht response =>
        cases hchildren with
        | cons htail hrest =>
            cases hrest
            exact .cons event events w j t hslot hjt ht htail
  extract := by
    intro state problem hsemantic
    cases hsemantic with
    | nil w j t hjt ht =>
        exact Or.inl ⟨rfl, .nil w j t hjt ht⟩
    | cons event events w j t hslot hjt ht htail =>
        apply Or.inr
        refine ⟨restorationRule,
          [((), restorationTail event events w j t)],
          rfl, rfl, ?_, ?_, ?_⟩
        · intro child hmem
          simp only [List.mem_cons, List.mem_singleton] at hmem
          rcases hmem with rfl | hfalse
          · exact htail
          · contradiction
        · intro child hmem
          simp only [List.mem_cons, List.mem_singleton] at hmem
          rcases hmem with rfl | hfalse
          · simp [restorationTail]
          · contradiction
        · exact .step event events w j t hslot hjt ht
            (headResponse_total I left right rightFinal
              event w j t hjt ht)

theorem annotatedRestoration_derives_iff_wellFormed
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (problem : RestorationProblem α) :
    CompilerDerives RestorationTerminal
        (AnnotatedRestorationCompose I left right rightFinal)
        () problem ↔
      RestorationWellFormed problem := by
  constructor
  · exact
      (annotatedRestorationCompiler I left right rightFinal
        ).realize_derivation
  · exact
      (annotatedRestorationCompiler I left right rightFinal
        ).extract_derivation

theorem validStream_annotated_derives
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hvalid : ValidRestorationStream events w)
    (hjt : j < t) (ht : t < w.length) :
    CompilerDerives RestorationTerminal
      (AnnotatedRestorationCompose I left right rightFinal)
      () ⟨events, w, j, t⟩ := by
  apply (annotatedRestorationCompiler I left right rightFinal
    ).extract_derivation
  exact restorationWellFormed_of_validStream
    events w j t hvalid hjt ht

structure SelectedRowWitness
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (w : Word α) (j t : Nat) : Prop where
  source_lt_target : j < t
  target_lt_length : t < w.length
  candidate : I.toSOA.candidate w
  leftAccepts : left.Accepts (w.take j)
  rightAccepts : right.Accepts (Word.factor w j (t - j))
  occurrence : OccursSuffixAt w j t

/--
A successful head check transports the same selected row witness to the
exact word and cuts stored in the structural tail problem.
-/
theorem selectedRowWitness_advance_of_success
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hwitness : SelectedRowWitness I left right w j t)
    (hsuccess :
      checkFirstEventLeakage I left right rightFinal
        event w j t = true) :
    SelectedRowWitness I left right (event.apply w)
      (advanceSource event j t) (advanceTarget event j t) := by
  have hjt : j < t := hwitness.source_lt_target
  have ht : t < w.length := hwitness.target_lt_length
  cases hplacement :
      classifyCutPlacement event.slot j t with
  | beforeSource =>
      simp only [advanceSource, advanceTarget, hplacement]
      unfold checkFirstEventLeakage at hsuccess
      rw [hplacement] at hsuccess
      have hstream :=
        (checkBeforeSourceLoops_correct
          I left [event] w j t).1 hsuccess
      cases hstream with
      | cons _ hslot hcandidateLoop hleftLoop tail =>
          have hslotLength : event.slot ≤ w.length := by
            omega
          have hlength :
              (event.apply w).length =
                w.length + event.payload.length :=
            Word.insertAt_length w event.payload hslotLength
          refine ⟨by omega, by omega,
            ?_, ?_, ?_, ?_⟩
          · exact I.candidate.accepts_insertAt_of_loop
              w event.payload event.slot hcandidateLoop
              hwitness.candidate
          · simpa [advanceSource, hplacement] using
              left.accepts_take_insertAt_before_of_loop
                w event.payload event.slot j hslot
                (by omega) hleftLoop hwitness.leftAccepts
          · have hdiff :
                (t + event.payload.length) -
                    (j + event.payload.length) = t - j := by
              omega
            rw [hdiff]
            simp only [InsertionEvent.apply]
            rw [Word.factor_insertAt_before
              w event.payload event.slot j (t - j)
              hslot (by omega)]
            exact hwitness.rightAccepts
          · simpa [advanceSource, advanceTarget, hplacement,
              InsertionEvent.apply] using
              Word.occursSuffixAt_insertAt_before
                w event.payload event.slot j t hslot
                hwitness.source_lt_target
                hwitness.target_lt_length hwitness.occurrence
  | betweenCuts =>
      simp only [advanceSource, advanceTarget, hplacement]
      unfold checkFirstEventLeakage at hsuccess
      rw [hplacement] at hsuccess
      have hcert :=
        (checkBetweenCuts_correct I right rightFinal
          w event.payload event.slot j t).1 hsuccess
      have hslotLength : event.slot ≤ w.length :=
        Nat.le_trans hcert.slot_le_target
          (Nat.le_of_lt hcert.target_lt_length)
      have hlength :
          (event.apply w).length =
            w.length + event.payload.length :=
        Word.insertAt_length w event.payload hslotLength
      refine ⟨by omega, by omega,
        ?_, ?_, ?_, ?_⟩
      · exact I.candidate.accepts_insertAt_of_loop
          w event.payload event.slot hcert.candidateLoop
          hwitness.candidate
      · simpa [InsertionEvent.apply] using
          (show left.Accepts
              ((Word.insertAt w event.payload event.slot).take j) by
            rw [Word.take_insertAt_after
              w event.payload event.slot j
              (Nat.le_of_lt hcert.source_lt_slot) hslotLength]
            exact hwitness.leftAccepts)
      · simpa [InsertionEvent.apply] using hcert.rightResponse
      · simpa [InsertionEvent.apply] using hcert.occurrenceResponse
  | afterTarget =>
      simp only [advanceSource, advanceTarget, hplacement]
      unfold checkFirstEventLeakage at hsuccess
      rw [hplacement] at hsuccess
      have hcert :=
        (checkAfterTarget_correct I
          w event.payload event.slot j t).1 hsuccess
      have htslot : t < event.slot := hcert.target_lt_slot
      have hlength :
          (event.apply w).length =
            w.length + event.payload.length :=
        Word.insertAt_length w event.payload hcert.slot_le_length
      refine ⟨hjt, by omega,
        ?_, ?_, ?_, ?_⟩
      · exact I.candidate.accepts_insertAt_of_loop
          w event.payload event.slot hcert.candidateLoop
          hwitness.candidate
      · simpa [InsertionEvent.apply] using
          (show left.Accepts
              ((Word.insertAt w event.payload event.slot).take j) by
            rw [Word.take_insertAt_after
              w event.payload event.slot j
              (Nat.le_trans (Nat.le_of_lt hjt)
                (Nat.le_of_lt htslot))
              hcert.slot_le_length]
            exact hwitness.leftAccepts)
      · simpa [InsertionEvent.apply] using
          (show right.Accepts
              (Word.factor
                (Word.insertAt w event.payload event.slot)
                j (t - j)) by
            rw [Word.factor_insertAt_after
              w event.payload event.slot j (t - j)
              (by omega) hcert.slot_le_length]
            exact hwitness.rightAccepts)
      · simpa [InsertionEvent.apply] using hcert.occurrenceResponse

inductive SuccessfulResponseStream
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right) :
    List (InsertionEvent α) → Word α → Nat → Nat → Prop where
  | nil (w : Word α) (j t : Nat) :
      SuccessfulResponseStream I left right rightFinal [] w j t
  | cons
      (event : InsertionEvent α) (events : List (InsertionEvent α))
      (w : Word α) (j t : Nat)
      (success :
        checkFirstEventLeakage I left right rightFinal
          event w j t = true)
      (tail :
        SuccessfulResponseStream I left right rightFinal events
          (event.apply w)
          (advanceSource event j t)
          (advanceTarget event j t)) :
      SuccessfulResponseStream I left right rightFinal
        (event :: events) w j t

theorem selectedRowWitness_applyStream_of_successes
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hstream :
      SuccessfulResponseStream I left right rightFinal events w j t)
    (hwitness : SelectedRowWitness I left right w j t) :
    ∃ finalSource finalTarget,
      SelectedRowWitness I left right
        (InsertionEvent.applyStream events w)
        finalSource finalTarget := by
  induction hstream with
  | nil w j t =>
      exact ⟨j, t, hwitness⟩
  | cons event events w j t hsuccess tail ih =>
      have hnext :=
        selectedRowWitness_advance_of_success
          I left right rightFinal event w j t hwitness hsuccess
      simpa [InsertionEvent.applyStream] using ih hnext

theorem selectedRowWitness_contradicts_avoider
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (hrow : (left, right) ∈ I.rows)
    (w : Word α) (j t : Nat)
    (hwitness : SelectedRowWitness I left right w j t) :
    ¬ I.toSOA.Avoider w := by
  intro havoider
  apply havoider.2
  refine ⟨CapComponent.ofDFA left right, ?_, ?_⟩
  · simp only [AutomataSOAInstance.toSOA, List.mem_map]
    exact ⟨(left, right), hrow, rfl⟩
  · exact ⟨j, t, hwitness.source_lt_target,
      hwitness.target_lt_length, hwitness.leftAccepts,
      hwitness.rightAccepts, hwitness.occurrence⟩

theorem successfulResponseStream_contradicts_avoider
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (hrow : (left, right) ∈ I.rows)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hstream :
      SuccessfulResponseStream I left right rightFinal events w j t)
    (hwitness : SelectedRowWitness I left right w j t) :
    ¬ I.toSOA.Avoider (InsertionEvent.applyStream events w) := by
  obtain ⟨finalSource, finalTarget, hfinal⟩ :=
    selectedRowWitness_applyStream_of_successes
      I left right rightFinal events w j t hstream hwitness
  exact selectedRowWitness_contradicts_avoider
    I left right hrow _ finalSource finalTarget hfinal

inductive ClassifiedResponseStream
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right) :
    List (InsertionEvent α) → Word α → Nat → Nat → Prop where
  | done (w : Word α) (j t : Nat) :
      ClassifiedResponseStream I left right rightFinal [] w j t
  | failed
      (event : InsertionEvent α) (events : List (InsertionEvent α))
      (w : Word α) (j t : Nat)
      (terminal :
        FirstEventReducedTerminal I left right event w j t) :
      ClassifiedResponseStream I left right rightFinal
        (event :: events) w j t
  | next
      (event : InsertionEvent α) (events : List (InsertionEvent α))
      (w : Word α) (j t : Nat)
      (success :
        checkFirstEventLeakage I left right rightFinal
          event w j t = true)
      (tail :
        ClassifiedResponseStream I left right rightFinal events
          (event.apply w)
          (advanceSource event j t)
          (advanceTarget event j t)) :
      ClassifiedResponseStream I left right rightFinal
        (event :: events) w j t

theorem classifiedResponseStream_total
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hvalid : ValidRestorationStream events w)
    (hjt : j < t) (ht : t < w.length) :
    ClassifiedResponseStream I left right rightFinal events w j t := by
  induction hvalid generalizing j t with
  | nil w =>
      exact .done w j t
  | cons event events w hslot tail ih =>
      rcases headResponse_total I left right rightFinal
          event w j t hjt ht with
        hsuccess | hterminal
      · exact .next event events w j t hsuccess
          (ih
            (advanceSource event j t)
            (advanceTarget event j t)
            (advanceSource_lt_advanceTarget event j t hjt)
            (advanceTarget_lt_apply_length
              event w j t hslot ht))
      · exact .failed event events w j t hterminal

structure SolvedResponseTerminal
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right) where
  event : InsertionEvent α
  word : Word α
  source : Nat
  target : Nat
  query :
    FirstEventTerminalQuery I left right event word source target
  derives :
    CompilerDerives
      (exactSolverTerminal
        (firstEventTerminalSolver I left right rightFinal
          event word source target))
      (noCompilerCompose
        (Input :=
          FirstEventTerminalQuery I left right event word source target))
      () query

theorem classifiedResponseStream_semantics
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (hrow : (left, right) ∈ I.rows)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hclassified :
      ClassifiedResponseStream I left right rightFinal events w j t)
    (hwitness : SelectedRowWitness I left right w j t) :
    (¬ I.toSOA.Avoider (InsertionEvent.applyStream events w)) ∨
      Nonempty (SolvedResponseTerminal I left right rightFinal) := by
  induction hclassified with
  | done w j t =>
      exact Or.inl
        (selectedRowWitness_contradicts_avoider
          I left right hrow w j t hwitness)
  | failed event events w j t terminal =>
      obtain ⟨query, _, hsolved⟩ :=
        FirstEventReducedTerminal.exists_exact_solved_query
          rightFinal terminal
      exact Or.inr
        ⟨⟨event, w, j, t, query, .terminal hsolved⟩⟩
  | next event events w j t success tail ih =>
      have hnext :=
        selectedRowWitness_advance_of_success
          I left right rightFinal event w j t hwitness success
      simpa [InsertionEvent.applyStream] using ih hnext

theorem validStream_nonavoider_or_solvedTerminal
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (hrow : (left, right) ∈ I.rows)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hvalid : ValidRestorationStream events w)
    (hwitness : SelectedRowWitness I left right w j t) :
    (¬ I.toSOA.Avoider (InsertionEvent.applyStream events w)) ∨
      Nonempty (SolvedResponseTerminal I left right rightFinal) := by
  apply classifiedResponseStream_semantics
    I left right rightFinal hrow events w j t
  · exact classifiedResponseStream_total
      I left right rightFinal events w j t hvalid
        hwitness.source_lt_target hwitness.target_lt_length
  · exact hwitness

/--
Semantic head rule.  With one selected row witness, processing the next
event either proves the restored word non-avoiding or produces an exact
zero-child terminal derivation for the failed response.
-/
theorem classifiedHead_nonavoider_or_terminal
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (hrow : (left, right) ∈ I.rows)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hwitness : SelectedRowWitness I left right w j t) :
    (¬ I.toSOA.Avoider (event.apply w)) ∨
      ∃ query,
        CompilerDerives
          (exactSolverTerminal
            (firstEventTerminalSolver I left right rightFinal
              event w j t))
          (noCompilerCompose
            (Input :=
              FirstEventTerminalQuery I left right event w j t))
          () query := by
  rcases firstEvent_success_or_failure I left right rightFinal
      event w j t hwitness.source_lt_target
        hwitness.target_lt_length with
    hsuccess | hfailure
  · exact Or.inl
      (checkFirstEventLeakage_true_contradicts_avoider
        I left right rightFinal hrow event w j t hsuccess
        hwitness.source_lt_target hwitness.target_lt_length
        hwitness.candidate hwitness.leftAccepts hwitness.rightAccepts
        hwitness.occurrence)
  · obtain ⟨query, _, hsolved⟩ :=
      FirstEventReducedTerminal.exists_exact_solved_query
        rightFinal hfailure.reduce
    exact Or.inr ⟨query, .terminal hsolved⟩

end NSSE
