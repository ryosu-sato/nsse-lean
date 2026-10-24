import NSSE.AutomataMinimalLongContraction
import NSSE.AnnotatedStreamCompiler
import NSSE.FiniteFirstEventHorn
import NSSE.RankedAttachmentResponseDispatcher
import NSSE.CanonicalRankedStructuralRegistry
import NSSE.RankedProfiledResponseCompiler

/-!
# Row witnesses carried by candidate-aligned contractions

The indexed query in an attached contraction is unpacked back into the
concrete pair of row automata and its selected cut witness.  This is the
input expected by the finite first-event response compiler.
-/

namespace NSSE

def relevantFirstEventPWEQuery
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    Bool → SuffixDisequalityQuery α
  | false => betweenOccurrenceQuery event w j t
  | true => afterOccurrenceQuery event w j t

def decideRelevantFirstEventPWE
    [DecidableEq α]
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (pweId : Bool) : Bool :=
  (suffixDisequalitySolver (α := α)).decide
    (relevantFirstEventPWEQuery event w j t pweId)

theorem GlobalDispositionDerives.finiteGuard_or_pwe
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t)
    (hderive :
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition) :
    (∃ query : FirstEventFiniteGuardQuery I left right event w j t,
      disposition = .inl (boundedResponseTag query) ∧
      (finiteGuardSolver I left right rightFinal
        event w j t).decide query = true) ∨
    ∃ terminal : ResponsePWETerminal α,
      disposition = .inr terminal ∧
      decideResponsePWETerminal terminal = true := by
  obtain ⟨responseClass, hclass⟩ :=
    globalDispositionDerives_hasClass
      I left right rightFinal event w j t disposition hderive
  have hsolved :
      GlobalDispositionSolved I left right rightFinal
        event w j t disposition :=
    (globalDispositionSolved_iff_derives
      I left right rightFinal event w j t disposition).2 hderive
  cases hclass with
  | bounded query =>
      exact Or.inl ⟨query, rfl, hsolved⟩
  | pwe terminal =>
      exact Or.inr ⟨terminal, rfl, hsolved⟩

theorem GlobalDispositionDerives.relevant_finiteGuard_or_pweId
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t)
    (hmem :
      disposition ∈
        relevantGlobalDispositions I left right event w j t)
    (hderive :
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition) :
    (∃ query : FirstEventFiniteGuardQuery I left right event w j t,
      disposition = .inl (boundedResponseTag query) ∧
      (finiteGuardSolver I left right rightFinal
        event w j t).decide query = true) ∨
    ∃ pweId : Bool,
      disposition =
        .inr (responsePWETerminal
          (relevantFirstEventPWEQuery event w j t pweId)) ∧
      decideRelevantFirstEventPWE event w j t pweId = true := by
  rcases hderive.finiteGuard_or_pwe
      I left right rightFinal event w j t with
    hguard | ⟨terminal, rfl, hterminal⟩
  · exact Or.inl hguard
  · simp [relevantGlobalDispositions, relevantFirstEventQueries,
      globalDisposition] at hmem
    rcases hmem with h | h
    · subst terminal
      exact Or.inr ⟨false, rfl, hterminal⟩
    · subst terminal
      exact Or.inr ⟨true, rfl, hterminal⟩

theorem GlobalDispositionDerives.relevantRankedAtomic_derives
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (localEnabled :
      Ctl → Cut → SideRank height →
        FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            Bool)
          QClass →
        Bool)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t)
    (hmem :
      disposition ∈
        relevantGlobalDispositions I left right event w j t)
    (hderive :
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition) :
    (∃ query : FirstEventFiniteGuardQuery I left right event w j t,
      disposition = .inl (boundedResponseTag query) ∧
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event w j t height localEnabled
        (decideRelevantFirstEventPWE event w j t)
        ctl cut ori macros wires loops canonicalBoolEnumeration
        quotient).TaggedDerives
          (.bounded control cutValue (.inl query))) ∨
    ∃ pweId : Bool,
      disposition =
        .inr (responsePWETerminal
          (relevantFirstEventPWEQuery event w j t pweId)) ∧
      (rankedFullyComposedRuleSystem summaryOf
        I left right rightFinal event w j t height localEnabled
        (decideRelevantFirstEventPWE event w j t)
        ctl cut ori macros wires loops canonicalBoolEnumeration
        quotient).TaggedDerives
          (.bounded control cutValue (.inr pweId)) := by
  rcases hderive.relevant_finiteGuard_or_pweId
      I left right rightFinal event w j t disposition hmem with
    ⟨query, hdisposition, hterminal⟩ |
      ⟨pweId, hdisposition, hterminal⟩
  · exact Or.inl ⟨query, hdisposition,
      rankedFullyComposed_guardAtom_derives summaryOf
        I left right rightFinal event w j t height localEnabled
        (decideRelevantFirstEventPWE event w j t)
        ctl cut ori macros wires loops canonicalBoolEnumeration
        quotient control cutValue query hterminal⟩
  · exact Or.inr ⟨pweId, hdisposition,
      rankedFullyComposed_localAtom_derives summaryOf
        I left right rightFinal event w j t height localEnabled
        (decideRelevantFirstEventPWE event w j t)
        ctl cut ori macros wires loops canonicalBoolEnumeration
        quotient control cutValue pweId hterminal⟩

theorem GlobalDispositionDerives.relevantRankedExhaustiveSide_derives
    [DecidableEq α]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QC] [DecidableEq QL] [DecidableEq QClass]
    (summaryOf : LoopId → LoopSummary Wire)
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t height : Nat)
    (roots : List (RankedInitialSideRoot height Ctl Cut))
    (tags :
      Enumeration
        (FiniteLoopCompilerTag Ctl Cut Ori (SideRank height)
          Macro Wire LoopId
          (UnifiedAtomicId
            (FirstEventFiniteGuardQuery I left right event w j t)
            Bool)
          QClass))
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (root : RankedInitialSideRoot height Ctl Cut)
    (hroot : root ∈ roots)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t)
    (hmem :
      disposition ∈
        relevantGlobalDispositions I left right event w j t)
    (hderive :
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition) :
    (rankedFullyComposedRuleSystem summaryOf
      I left right rightFinal event w j t height
      (attachmentResponseTableEnabled
        (exhaustiveRankedResponseEdges roots tags))
      (decideRelevantFirstEventPWE event w j t)
      ctl cut ori macros wires loops canonicalBoolEnumeration
      quotient).TaggedDerives
        (.side root.control root.cut root.rank) := by
  rcases hderive.relevantRankedAtomic_derives summaryOf
      I left right rightFinal event w j t height
      (attachmentResponseTableEnabled
        (exhaustiveRankedResponseEdges roots tags))
      ctl cut ori macros wires loops quotient
      root.control root.cut disposition hmem with
    ⟨query, _, hchild⟩ | ⟨pweId, _, hchild⟩
  · exact rankedFullyComposed_exhaustive_side_derives summaryOf
      I left right rightFinal event w j t height roots tags
      (decideRelevantFirstEventPWE event w j t)
      ctl cut ori macros wires loops canonicalBoolEnumeration
      quotient root hroot
      (.bounded root.control root.cut (.inl query)) hchild
  · exact rankedFullyComposed_exhaustive_side_derives summaryOf
      I left right rightFinal event w j t height roots tags
      (decideRelevantFirstEventPWE event w j t)
      ctl cut ori macros wires loops canonicalBoolEnumeration
      quotient root hroot
      (.bounded root.control root.cut (.inr pweId)) hchild

def CandidateAlignedAttachedContraction.rightRestorationEvent
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word) :
    InsertionEvent α where
  slot :=
    contraction.attachment.left.length +
      (contraction.attachment.toIntervalWordAttachment
        |>.orderedAttachment).rightSlot
  payload := contraction.attachment.payload

theorem CandidateAlignedAttachedContraction.rightRestorationEvent_apply
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word) :
    contraction.rightRestorationEvent.apply contraction.shorter =
      word := by
  let ordered :=
    contraction.attachment.toIntervalWordAttachment.orderedAttachment
  have hupper :
      contraction.attachment.upper =
        contraction.attachment.left ++ ordered.base ++
          contraction.attachment.right := by
    change
      contraction.attachment.left ++
          FactorTree.forestYield contraction.attachment.forest ++
          contraction.attachment.right =
        contraction.attachment.left ++ ordered.base ++
          contraction.attachment.right
    rw [show ordered.base =
        FactorTree.forestYield contraction.attachment.forest by
      exact contraction.attachment.parentWord_eq_forestYield]
  rw [← contraction.upper_eq, hupper]
  unfold CandidateAlignedAttachedContraction.rightRestorationEvent
    InsertionEvent.apply
  change
    Word.insertAt
        (contraction.attachment.left ++ ordered.base ++
          contraction.attachment.right)
        contraction.attachment.payload
        (contraction.attachment.left.length + ordered.rightSlot) =
      word
  rw [Word.insertAt_append_middle
    contraction.attachment.left ordered.base
    contraction.attachment.right contraction.attachment.payload
    ordered.rightSlot ordered.right_le_length]
  exact contraction.rightInsertion_eq_word

theorem CandidateAlignedAttachedContraction.rightRestorationEvent_valid
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word) :
    ValidRestorationStream
      [contraction.rightRestorationEvent] contraction.shorter := by
  apply ValidRestorationStream.cons
  · have hslot :=
      (contraction.attachment.toIntervalWordAttachment
        |>.orderedAttachment).right_le_length
    have hupper := contraction.upper_eq
    have hbase :=
      contraction.attachment.parentWord_eq_forestYield
    have hbaseLength :
        (contraction.attachment.toIntervalWordAttachment
          |>.orderedAttachment).base.length =
          (FactorTree.forestYield
            contraction.attachment.forest).length :=
      congrArg List.length hbase
    rw [hbaseLength] at hslot
    simp only [CandidateAlignedAttachedContraction.rightRestorationEvent]
    rw [← hupper]
    simp [ForestWordAttachment.upper] at hslot ⊢
    omega
  · exact .nil _

theorem CandidateAlignedAttachedContraction.exists_selectedRowWitness
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word) :
    ∃ left : DFA α QL, ∃ right : DFA α QR,
      (left, right) ∈ I.rows ∧
      ∃ j t,
        SelectedRowWitness I left right contraction.shorter j t := by
  have hrowMem :
      I.toSOA.rows[contraction.index] ∈ I.toSOA.rows :=
    List.getElem_mem contraction.index.isLt
  change
    I.toSOA.rows[contraction.index] ∈
      I.rows.map (fun row =>
        CapComponent.ofDFA row.1 row.2) at hrowMem
  obtain ⟨row, hrow, hrowEq⟩ :=
    List.mem_map.mp hrowMem
  rcases row with ⟨left, right⟩
  have hcovers :
      SOAInstance.RowCovers
        (CapComponent.ofDFA left right) contraction.shorter := by
    have hquery := contraction.query
    unfold SOAInstance.IndexedRootQuery at hquery
    rw [hrowEq]
    exact hquery
  obtain ⟨j, t, hjt, ht, hleft, hright, hoccurs⟩ :=
    (SOAInstance.rowCovers_iff_cuts
      (CapComponent.ofDFA left right) contraction.shorter).1 hcovers
  refine ⟨left, right, hrow, j, t, ?_⟩
  exact {
    source_lt_target := hjt
    target_lt_length := ht
    candidate := contraction.candidate
    leftAccepts := hleft
    rightAccepts := hright
    occurrence := hoccurs
  }

theorem CandidateAlignedAttachedContraction.exists_globalFiniteResponse
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word)
    (hminimal : I.toSOA.LengthMinimalAvoider word)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right) :
    ∃ left : DFA α QL, ∃ right : DFA α QR,
      (left, right) ∈ I.rows ∧
      ∃ j t,
        SelectedRowWitness I left right contraction.shorter j t ∧
        ∃ (failedEvent : InsertionEvent α)
            (failedWord : Word α)
            (failedSource failedTarget : Nat),
          HornDerives
            (hornFamilyCompiler
              (relevantGlobalResponseFamilies
                I left right (rightFinalOf right)
                failedEvent failedWord failedSource failedTarget)) 1 := by
  obtain ⟨left, right, hrow, j, t, hwitness⟩ :=
    contraction.exists_selectedRowWitness
  refine ⟨left, right, hrow, j, t, hwitness, ?_⟩
  rcases validStream_nonavoider_or_global_finite_root
      I left right (rightFinalOf right) hrow
      [contraction.rightRestorationEvent]
      contraction.shorter j t
      contraction.rightRestorationEvent_valid hwitness with
    hnot | hresponse
  · exact False.elim
      (hnot (by
        simpa [InsertionEvent.applyStream,
          contraction.rightRestorationEvent_apply] using hminimal.1))
  · exact hresponse

theorem CandidateAlignedAttachedContraction.exists_profiledResponseId
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word)
    (hminimal : I.toSOA.LengthMinimalAvoider word)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right) :
    ∃ left : DFA α QL, ∃ right : DFA α QR,
      (left, right) ∈ I.rows ∧
      ∃ j t,
        SelectedRowWitness I left right contraction.shorter j t ∧
        ∃ (failedEvent : InsertionEvent α)
            (failedWord : Word α)
            (failedSource failedTarget : Nat)
            (responseId : FirstEventResponseId),
          decideFirstEventResponseId
            I left right (rightFinalOf right)
            failedEvent failedWord failedSource failedTarget
            responseId = true := by
  obtain ⟨left, right, hrow, j, t, hwitness,
      failedEvent, failedWord, failedSource, failedTarget, hroot⟩ :=
    contraction.exists_globalFiniteResponse hminimal rightFinalOf
  obtain ⟨responseId, hresponse⟩ :=
    (relevantGlobalResponseRoot_derives_iff_responseId
      I left right (rightFinalOf right)
      failedEvent failedWord failedSource failedTarget).1 hroot
  exact ⟨left, right, hrow, j, t, hwitness,
    failedEvent, failedWord, failedSource, failedTarget,
    responseId, hresponse⟩

theorem CandidateAlignedAttachedContraction.exists_profiledTerminal
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word)
    (hminimal : I.toSOA.LengthMinimalAvoider word)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right) :
    ∃ left : DFA α QL, ∃ right : DFA α QR,
      (left, right) ∈ I.rows ∧
      ∃ j t,
        SelectedRowWitness I left right contraction.shorter j t ∧
        ∃ response : ProfiledFirstEventResponse,
          profiledFirstEventResponseTerminal response = true := by
  obtain ⟨left, right, hrow, j, t, hwitness,
      failedEvent, failedWord, failedSource, failedTarget,
      responseId, hresponse⟩ :=
    contraction.exists_profiledResponseId hminimal rightFinalOf
  refine ⟨left, right, hrow, j, t, hwitness,
    profiledFirstEventResponse
      I left right (rightFinalOf right)
      failedEvent failedWord failedSource failedTarget responseId, ?_⟩
  simpa using hresponse

theorem CandidateAlignedAttachedContraction.exists_solvedGlobalDisposition
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word)
    (hminimal : I.toSOA.LengthMinimalAvoider word)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right) :
    ∃ left : DFA α QL, ∃ right : DFA α QR,
      (left, right) ∈ I.rows ∧
      ∃ j t,
        SelectedRowWitness I left right contraction.shorter j t ∧
        ∃ (failedEvent : InsertionEvent α)
            (failedWord : Word α)
            (failedSource failedTarget : Nat)
            (disposition :
              FirstEventGlobalDisposition I left right
                failedEvent failedWord failedSource failedTarget),
          disposition ∈
            relevantGlobalDispositions I left right
              failedEvent failedWord failedSource failedTarget ∧
          GlobalDispositionDerives
            I left right (rightFinalOf right)
            failedEvent failedWord failedSource failedTarget
            disposition := by
  obtain ⟨left, right, hrow, j, t, hwitness,
      failedEvent, failedWord, failedSource, failedTarget, hroot⟩ :=
    contraction.exists_globalFiniteResponse hminimal rightFinalOf
  obtain ⟨disposition, hmem, hderive⟩ :=
    (relevantGlobalResponseRoot_derives_iff
      I left right (rightFinalOf right)
      failedEvent failedWord failedSource failedTarget).1 hroot
  exact ⟨left, right, hrow, j, t, hwitness,
    failedEvent, failedWord, failedSource, failedTarget,
    disposition, hmem, hderive⟩

theorem CandidateAlignedAttachedContraction.exists_rankedSideResponse
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq LoopId]
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word)
    (hminimal : I.toSOA.LengthMinimalAvoider word)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right)
    (summaryOf : LoopId → LoopSummary Wire)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId)
    (predicates : List UnaryArithmeticPredicate)
    (quotient : Enumeration (EuclideanSymbol predicates.length))
    (control : Ctl) (cutValue : Cut) (height : Nat) :
    ∃ left : DFA α QL, ∃ right : DFA α QR,
      (left, right) ∈ I.rows ∧
      ∃ j t,
        SelectedRowWitness I left right contraction.shorter j t ∧
        ∃ (failedEvent : InsertionEvent α)
            (failedWord : Word α)
            (failedSource failedTarget : Nat)
            (disposition :
              FirstEventGlobalDisposition I left right
                failedEvent failedWord failedSource failedTarget),
          disposition ∈
            relevantGlobalDispositions I left right
              failedEvent failedWord failedSource failedTarget ∧
          GlobalDispositionDerives
            I left right (rightFinalOf right)
            failedEvent failedWord failedSource failedTarget
            disposition ∧
          let roots := allRankedInitialSideRoots ctl cut height
          let tags := allRankedCompilerTags
            ctl cut orientation macros wires loops
            (finiteGuardQueryEnumeration I left right
              failedEvent failedWord failedSource failedTarget)
            canonicalBoolEnumeration quotient height
          let edges := exhaustiveRankedResponseEdges roots tags
          let system :=
            rankedFullyComposedRuleSystem summaryOf
              I left right (rightFinalOf right)
              failedEvent failedWord failedSource failedTarget height
              (attachmentResponseTableEnabled edges)
              (decideRelevantFirstEventPWE
                failedEvent failedWord failedSource failedTarget)
              ctl cut orientation macros wires loops
              canonicalBoolEnumeration quotient
          ∃ root ∈ roots,
            system.TaggedDerives
              (.side root.control root.cut root.rank) := by
  obtain ⟨left, right, hrow, j, t, hwitness,
      failedEvent, failedWord, failedSource, failedTarget,
      disposition, hmem, hderive⟩ :=
    contraction.exists_solvedGlobalDisposition hminimal rightFinalOf
  refine ⟨left, right, hrow, j, t, hwitness,
    failedEvent, failedWord, failedSource, failedTarget,
    disposition, hmem, hderive, ?_⟩
  dsimp only
  let roots := allRankedInitialSideRoots ctl cut height
  let tags := allRankedCompilerTags
    ctl cut orientation macros wires loops
    (finiteGuardQueryEnumeration I left right
      failedEvent failedWord failedSource failedTarget)
    canonicalBoolEnumeration quotient height
  let root : RankedInitialSideRoot height Ctl Cut :=
    {
      control := control
      cut := cutValue
      rank := SideRank.zero height
    }
  have hroot : root ∈ roots :=
    mem_allRankedInitialSideRoots ctl cut height root
  refine ⟨root, hroot, ?_⟩
  exact hderive.relevantRankedExhaustiveSide_derives summaryOf
    I left right (rightFinalOf right)
    failedEvent failedWord failedSource failedTarget height
    roots tags ctl cut orientation macros wires loops quotient
    root hroot disposition hmem

theorem CandidateAlignedAttachedContraction.exists_fixedProfiledSideResponse
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    {I : AutomataSOAInstance α QC QL QR}
    {word : Word α}
    (contraction :
      CandidateAlignedAttachedContraction I word)
    (hminimal : I.toSOA.LengthMinimalAvoider word)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right)
    (summaryOf : LoopId → LoopSummary Wire)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (height : Nat) :
    let roots := allRankedInitialSideRoots ctl cut height
    let tags := allRankedProfiledResponseTags
      ctl cut ori macros wires loops quotient height
    let edges := exhaustiveProfiledResponseEdges roots tags
    let system := rankedProfiledResponseRuleSystem summaryOf height
      (attachmentResponseTableEnabled edges)
      ctl cut ori macros wires loops quotient
    ∃ left : DFA α QL, ∃ right : DFA α QR,
      (left, right) ∈ I.rows ∧
      ∃ j t,
        SelectedRowWitness I left right contraction.shorter j t ∧
        ∃ (failedEvent : InsertionEvent α)
            (failedWord : Word α)
            (failedSource failedTarget : Nat)
            (responseId : FirstEventResponseId),
          decideFirstEventResponseId
            I left right (rightFinalOf right)
            failedEvent failedWord failedSource failedTarget
            responseId = true ∧
          ∃ root ∈ roots,
            system.TaggedDerives
              (.side root.control root.cut root.rank) := by
  dsimp only
  let roots := allRankedInitialSideRoots ctl cut height
  let tags := allRankedProfiledResponseTags
    ctl cut ori macros wires loops quotient height
  obtain ⟨left, right, hrow, j, t, hwitness,
      failedEvent, failedWord, failedSource, failedTarget,
      responseId, hresponse⟩ :=
    contraction.exists_profiledResponseId hminimal rightFinalOf
  let root : RankedInitialSideRoot height Ctl Cut :=
    {
      control := control
      cut := cutValue
      rank := SideRank.zero height
    }
  have hroot : root ∈ roots :=
    mem_allRankedInitialSideRoots ctl cut height root
  refine ⟨left, right, hrow, j, t, hwitness,
    failedEvent, failedWord, failedSource, failedTarget,
    responseId, hresponse, root, hroot, ?_⟩
  apply rankedProfiledResponse_exhaustive_side_derives
    summaryOf height roots tags ctl cut ori macros wires loops
    quotient root hroot
    (profiledFirstEventResponse
      I left right (rightFinalOf right)
      failedEvent failedWord failedSource failedTarget responseId)
  simpa using hresponse

theorem AutomataSOAInstance.exists_uniform_long_globalFiniteResponse
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (candidateStates : Enumeration QC)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right) :
    ∃ heightBound,
      ∀ word,
        I.toSOA.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ contraction :
            CandidateAlignedAttachedContraction I word,
          ∃ left : DFA α QL, ∃ right : DFA α QR,
            (left, right) ∈ I.rows ∧
            ∃ j t,
              SelectedRowWitness
                  I left right contraction.shorter j t ∧
              ∃ (failedEvent : InsertionEvent α)
                  (failedWord : Word α)
                  (failedSource failedTarget : Nat),
                HornDerives
                  (hornFamilyCompiler
                    (relevantGlobalResponseFamilies
                      I left right (rightFinalOf right)
                      failedEvent failedWord
                      failedSource failedTarget)) 1 := by
  obtain ⟨heightBound, extract⟩ :=
    I.exists_uniform_long_attachedContraction candidateStates
  refine ⟨heightBound, ?_⟩
  intro word hminimal hlong
  obtain ⟨contraction⟩ := extract word hminimal hlong
  exact ⟨contraction,
    contraction.exists_globalFiniteResponse hminimal rightFinalOf⟩

theorem AutomataSOAInstance.exists_uniform_long_profiledTerminal
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (candidateStates : Enumeration QC)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right) :
    ∃ heightBound,
      ∀ word,
        I.toSOA.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ contraction :
            CandidateAlignedAttachedContraction I word,
          ∃ left : DFA α QL, ∃ right : DFA α QR,
            (left, right) ∈ I.rows ∧
            ∃ j t,
              SelectedRowWitness
                  I left right contraction.shorter j t ∧
              ∃ response : ProfiledFirstEventResponse,
                profiledFirstEventResponseTerminal response = true := by
  obtain ⟨heightBound, extract⟩ :=
    I.exists_uniform_long_attachedContraction candidateStates
  refine ⟨heightBound, ?_⟩
  intro word hminimal hlong
  obtain ⟨contraction⟩ := extract word hminimal hlong
  exact ⟨contraction,
    contraction.exists_profiledTerminal hminimal rightFinalOf⟩

theorem AutomataSOAInstance.exists_uniform_long_rankedSideResponse
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Macro]
    [DecidableEq Wire] [DecidableEq LoopId]
    (I : AutomataSOAInstance α QC QL QR)
    (candidateStates : Enumeration QC)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right)
    (summaryOf : LoopId → LoopSummary Wire)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (orientation : Enumeration Orientation)
    (macros : Enumeration Macro) (wires : Enumeration Wire)
    (loops : Enumeration LoopId)
    (predicates : List UnaryArithmeticPredicate)
    (quotient : Enumeration (EuclideanSymbol predicates.length))
    (control : Ctl) (cutValue : Cut) (rankHeight : Nat) :
    ∃ heightBound,
      ∀ word,
        I.toSOA.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ contraction :
            CandidateAlignedAttachedContraction I word,
          ∃ left : DFA α QL, ∃ right : DFA α QR,
            (left, right) ∈ I.rows ∧
            ∃ j t,
              SelectedRowWitness
                  I left right contraction.shorter j t ∧
              ∃ (failedEvent : InsertionEvent α)
                  (failedWord : Word α)
                  (failedSource failedTarget : Nat)
                  (disposition :
                    FirstEventGlobalDisposition I left right
                      failedEvent failedWord
                      failedSource failedTarget),
                disposition ∈
                  relevantGlobalDispositions I left right
                    failedEvent failedWord
                    failedSource failedTarget ∧
                GlobalDispositionDerives
                  I left right (rightFinalOf right)
                  failedEvent failedWord
                  failedSource failedTarget disposition ∧
                let roots :=
                  allRankedInitialSideRoots ctl cut rankHeight
                let tags := allRankedCompilerTags
                  ctl cut orientation macros wires loops
                  (finiteGuardQueryEnumeration I left right
                    failedEvent failedWord
                    failedSource failedTarget)
                  canonicalBoolEnumeration quotient rankHeight
                let edges :=
                  exhaustiveRankedResponseEdges roots tags
                let system :=
                  rankedFullyComposedRuleSystem summaryOf
                    I left right (rightFinalOf right)
                    failedEvent failedWord
                    failedSource failedTarget rankHeight
                    (attachmentResponseTableEnabled edges)
                    (decideRelevantFirstEventPWE
                      failedEvent failedWord
                      failedSource failedTarget)
                    ctl cut orientation macros wires loops
                    canonicalBoolEnumeration quotient
                ∃ root ∈ roots,
                  system.TaggedDerives
                    (.side root.control root.cut root.rank) := by
  obtain ⟨heightBound, extract⟩ :=
    I.exists_uniform_long_attachedContraction candidateStates
  refine ⟨heightBound, ?_⟩
  intro word hminimal hlong
  obtain ⟨contraction⟩ := extract word hminimal hlong
  exact ⟨contraction,
    contraction.exists_rankedSideResponse hminimal rightFinalOf
      summaryOf ctl cut orientation macros wires loops
      predicates quotient control cutValue rankHeight⟩

theorem AutomataSOAInstance.exists_uniform_long_fixedProfiledSideResponse
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    [DecidableEq Ctl] [DecidableEq Cut] [DecidableEq Ori]
    [DecidableEq Macro] [DecidableEq Wire] [DecidableEq LoopId]
    [DecidableEq QClass]
    (I : AutomataSOAInstance α QC QL QR)
    (candidateStates : Enumeration QC)
    (rightFinalOf :
      ∀ right : DFA α QR, DFAFinalTest right)
    (summaryOf : LoopId → LoopSummary Wire)
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (macros : Enumeration Macro)
    (wires : Enumeration Wire) (loops : Enumeration LoopId)
    (quotient : Enumeration QClass)
    (control : Ctl) (cutValue : Cut) (rankHeight : Nat) :
    let roots := allRankedInitialSideRoots ctl cut rankHeight
    let tags := allRankedProfiledResponseTags
      ctl cut ori macros wires loops quotient rankHeight
    let edges := exhaustiveProfiledResponseEdges roots tags
    let system := rankedProfiledResponseRuleSystem summaryOf rankHeight
      (attachmentResponseTableEnabled edges)
      ctl cut ori macros wires loops quotient
    ∃ heightBound,
      ∀ word,
        I.toSOA.LengthMinimalAvoider word →
        2 ^ heightBound < word.length →
        ∃ contraction :
            CandidateAlignedAttachedContraction I word,
          ∃ left : DFA α QL, ∃ right : DFA α QR,
            (left, right) ∈ I.rows ∧
            ∃ j t,
              SelectedRowWitness
                  I left right contraction.shorter j t ∧
              ∃ (failedEvent : InsertionEvent α)
                  (failedWord : Word α)
                  (failedSource failedTarget : Nat)
                  (responseId : FirstEventResponseId),
                decideFirstEventResponseId
                  I left right (rightFinalOf right)
                  failedEvent failedWord failedSource failedTarget
                  responseId = true ∧
                ∃ root ∈ roots,
                  system.TaggedDerives
                    (.side root.control root.cut root.rank) := by
  dsimp only
  obtain ⟨heightBound, extract⟩ :=
    I.exists_uniform_long_attachedContraction candidateStates
  refine ⟨heightBound, ?_⟩
  intro word hminimal hlong
  obtain ⟨contraction⟩ := extract word hminimal hlong
  exact ⟨contraction,
    contraction.exists_fixedProfiledSideResponse
      hminimal rightFinalOf summaryOf
      ctl cut ori macros wires loops quotient
      control cutValue rankHeight⟩

end NSSE
