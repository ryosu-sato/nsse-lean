import NSSE.ConcreteSolverFamilies
import NSSE.EuclideanProfile
import NSSE.ResponseHorn
import NSSE.ResponseMask

/-!
# The six finite first-event Horn alternatives

Although `FirstEventTerminalQuery` can store an arbitrary PWE query, the
exact first-event failure partition emits only four finite guards and
two literal suffix queries.  They are assembled here into one concrete
finite Horn-family compiler.
-/

namespace NSSE

universe u vc vl vr

inductive FirstEventResponseId where
  | candidateLoop
  | beforeLeftLoop
  | betweenRight
  | afterSlot
  | betweenOccurrence
  | afterOccurrence
deriving DecidableEq

def firstEventResponseIdEnumeration :
    Enumeration FirstEventResponseId where
  values :=
    [.candidateLoop, .beforeLeftLoop, .betweenRight, .afterSlot,
      .betweenOccurrence, .afterOccurrence]
  complete := by
    intro responseId
    cases responseId <;> simp

def firstEventQueryOfResponseId
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    FirstEventResponseId →
      FirstEventTerminalQuery I left right event w j t
  | .candidateLoop => .finiteGuard .candidateLoop
  | .beforeLeftLoop => .finiteGuard .beforeLeftLoop
  | .betweenRight => .finiteGuard .betweenRight
  | .afterSlot => .finiteGuard .afterSlot
  | .betweenOccurrence => .pwe (betweenOccurrenceQuery event w j t)
  | .afterOccurrence => .pwe (afterOccurrenceQuery event w j t)

def decideFirstEventResponseId
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (responseId : FirstEventResponseId) : Bool :=
  (firstEventTerminalSolver I left right rightFinal event w j t).decide
    (firstEventQueryOfResponseId I left right event w j t responseId)

def FirstEventResponseId.index : FirstEventResponseId → Nat
  | .candidateLoop => 0
  | .beforeLeftLoop => 1
  | .betweenRight => 2
  | .afterSlot => 3
  | .betweenOccurrence => 4
  | .afterOccurrence => 5

theorem FirstEventResponseId.index_lt_six
    (responseId : FirstEventResponseId) :
    responseId.index < 6 := by
  cases responseId <;> decide

def FirstEventResponseId.profileValue
    (profile : TruthVector 6)
    (responseId : FirstEventResponseId) : Bool :=
  profile.bits[responseId.index]'(by
    simpa [profile.length_eq] using responseId.index_lt_six)

def firstEventResponseProfile
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    TruthVector 6 where
  bits :=
    [decideFirstEventResponseId I left right rightFinal
      event w j t .candidateLoop,
     decideFirstEventResponseId I left right rightFinal
      event w j t .beforeLeftLoop,
     decideFirstEventResponseId I left right rightFinal
      event w j t .betweenRight,
     decideFirstEventResponseId I left right rightFinal
      event w j t .afterSlot,
     decideFirstEventResponseId I left right rightFinal
      event w j t .betweenOccurrence,
     decideFirstEventResponseId I left right rightFinal
      event w j t .afterOccurrence]
  length_eq := rfl

@[simp] theorem firstEventResponseProfile_value
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (responseId : FirstEventResponseId) :
    responseId.profileValue
        (firstEventResponseProfile
          I left right rightFinal event w j t) =
      decideFirstEventResponseId I left right rightFinal
        event w j t responseId := by
  cases responseId <;>
    rfl

abbrev ProfiledFirstEventResponse :=
  TruthVector 6 × FirstEventResponseId

def profiledFirstEventResponseEnumeration :
    Enumeration ProfiledFirstEventResponse :=
  (TruthVector.enumeration 6).product firstEventResponseIdEnumeration

def profiledFirstEventResponseTerminal
    (response : ProfiledFirstEventResponse) : Bool :=
  response.2.profileValue response.1

def profiledFirstEventResponse
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (responseId : FirstEventResponseId) :
    ProfiledFirstEventResponse :=
  (firstEventResponseProfile I left right rightFinal event w j t,
    responseId)

@[simp] theorem profiledFirstEventResponse_terminal
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (responseId : FirstEventResponseId) :
    profiledFirstEventResponseTerminal
        (profiledFirstEventResponse
          I left right rightFinal event w j t responseId) =
      decideFirstEventResponseId I left right rightFinal
        event w j t responseId :=
  firstEventResponseProfile_value
    I left right rightFinal event w j t responseId

def relevantFirstEventQueries
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    List (FirstEventTerminalQuery I left right event w j t) :=
  [.finiteGuard .candidateLoop,
   .finiteGuard .beforeLeftLoop,
   .finiteGuard .betweenRight,
   .finiteGuard .afterSlot,
   .pwe (betweenOccurrenceQuery event w j t),
   .pwe (afterOccurrenceQuery event w j t)]

theorem relevantFirstEventQueries_eq_responseIds
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    relevantFirstEventQueries I left right event w j t =
      firstEventResponseIdEnumeration.values.map
        (firstEventQueryOfResponseId I left right event w j t) :=
  rfl

theorem mem_relevantFirstEventQueries_iff_responseId
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (query : FirstEventTerminalQuery I left right event w j t) :
    query ∈ relevantFirstEventQueries I left right event w j t ↔
      ∃ responseId,
        query =
          firstEventQueryOfResponseId
            I left right event w j t responseId := by
  rw [relevantFirstEventQueries_eq_responseIds]
  simp only [List.mem_map]
  constructor
  · rintro ⟨responseId, _, rfl⟩
    exact ⟨responseId, rfl⟩
  · rintro ⟨responseId, rfl⟩
    exact ⟨responseId,
      firstEventResponseIdEnumeration.complete responseId, rfl⟩

@[simp] theorem relevantFirstEventQueries_length
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    (relevantFirstEventQueries I left right event w j t).length = 6 :=
  rfl

theorem reducedTerminal_encodes_mem_relevant
    {I : AutomataSOAInstance α QC QL QR}
    {left : DFA α QL} {right : DFA α QR}
    {event : InsertionEvent α} {w : Word α} {j t : Nat}
    {terminal :
      FirstEventReducedTerminal I left right event w j t}
    {query : FirstEventTerminalQuery I left right event w j t}
    (hencodes :
      FirstEventReducedTerminal.Encodes terminal query) :
    query ∈ relevantFirstEventQueries
      I left right event w j t := by
  cases hencodes with
  | finiteGuard encodes =>
      cases encodes <;> simp [relevantFirstEventQueries]
  | pwe encodes =>
      cases encodes <;> simp [relevantFirstEventQueries]

def relevantFirstEventFamilies
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    List HornFamily :=
  (relevantFirstEventQueries I left right event w j t).map
    (exactSolverHornFamily
      (firstEventTerminalSolver I left right rightFinal event w j t))

theorem relevantFirstEventRoot_derives_iff
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    HornDerives
        (hornFamilyCompiler
          (relevantFirstEventFamilies I left right rightFinal
            event w j t)) 1 ↔
      ∃ query ∈
          relevantFirstEventQueries I left right event w j t,
        (firstEventTerminalSolver I left right rightFinal
          event w j t).formula query := by
  rw [hornFamilyRoot_derives_iff]
  constructor
  · rintro ⟨family, hfamily, hderive⟩
    simp only [relevantFirstEventFamilies, List.mem_map] at hfamily
    obtain ⟨query, hquery, rfl⟩ := hfamily
    exact ⟨query, hquery,
      (exactSolverHornFamily_derives_iff
        (firstEventTerminalSolver I left right rightFinal
          event w j t) query).1 hderive⟩
  · rintro ⟨query, hquery, hformula⟩
    refine ⟨exactSolverHornFamily
      (firstEventTerminalSolver I left right rightFinal
        event w j t) query, ?_, ?_⟩
    · simp only [relevantFirstEventFamilies, List.mem_map]
      exact ⟨query, hquery, rfl⟩
    · exact
        (exactSolverHornFamily_derives_iff
          (firstEventTerminalSolver I left right rightFinal
            event w j t) query).2 hformula

theorem firstEvent_check_false_derives_finite_family_root
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length)
    (hfalse :
      checkFirstEventLeakage I left right rightFinal
        event w j t = false) :
    HornDerives
      (hornFamilyCompiler
        (relevantFirstEventFamilies I left right rightFinal
          event w j t)) 1 := by
  have hfailure :=
    (firstEvent_check_false_iff_failure
      I left right rightFinal event w j t hjt ht).1 hfalse
  obtain ⟨query, hencodes, haccepted⟩ :=
    FirstEventReducedTerminal.exists_exact_solved_query
      rightFinal hfailure.reduce
  apply
    (relevantFirstEventRoot_derives_iff
      I left right rightFinal event w j t).2
  refine ⟨query,
    reducedTerminal_encodes_mem_relevant hencodes, ?_⟩
  exact
    ((firstEventTerminalSolver I left right rightFinal
      event w j t).correct query).1 haccepted

def relevantGlobalDispositions
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    List
      (FirstEventGlobalDisposition I left right event w j t) :=
  (relevantFirstEventQueries I left right event w j t).map
    globalDisposition

theorem relevantGlobalDispositions_eq_responseIds
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    relevantGlobalDispositions I left right event w j t =
      firstEventResponseIdEnumeration.values.map fun responseId =>
        globalDisposition
          (firstEventQueryOfResponseId
            I left right event w j t responseId) := by
  rw [relevantGlobalDispositions,
    relevantFirstEventQueries_eq_responseIds, List.map_map]
  rfl

theorem mem_relevantGlobalDispositions_iff_responseId
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    disposition ∈
        relevantGlobalDispositions I left right event w j t ↔
      ∃ responseId,
        disposition =
          globalDisposition
            (firstEventQueryOfResponseId
              I left right event w j t responseId) := by
  rw [relevantGlobalDispositions_eq_responseIds]
  simp only [List.mem_map]
  constructor
  · rintro ⟨responseId, _, rfl⟩
    exact ⟨responseId, rfl⟩
  · rintro ⟨responseId, rfl⟩
    exact ⟨responseId,
      firstEventResponseIdEnumeration.complete responseId, rfl⟩

@[simp] theorem relevantGlobalDispositions_length
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    (relevantGlobalDispositions I left right event w j t).length = 6 := by
  simp [relevantGlobalDispositions]

def relevantGlobalResponseFamilies
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    List HornFamily :=
  (relevantGlobalDispositions I left right event w j t).map
    (responseHornFamily I left right rightFinal event w j t)

@[simp] theorem relevantGlobalResponseFamilies_length
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    (relevantGlobalResponseFamilies I left right rightFinal
      event w j t).length = 6 := by
  simp [relevantGlobalResponseFamilies]

theorem relevantGlobalResponseRoot_derives_iff
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    HornDerives
        (hornFamilyCompiler
          (relevantGlobalResponseFamilies
            I left right rightFinal event w j t)) 1 ↔
      ∃ disposition ∈
          relevantGlobalDispositions I left right event w j t,
        GlobalDispositionDerives I left right rightFinal
          event w j t disposition := by
  rw [hornFamilyRoot_derives_iff]
  constructor
  · rintro ⟨family, hfamily, hderive⟩
    simp only [relevantGlobalResponseFamilies,
      List.mem_map] at hfamily
    obtain ⟨disposition, hdisposition, rfl⟩ := hfamily
    exact ⟨disposition, hdisposition,
      (responseHorn_root_derives_iff
        I left right rightFinal event w j t disposition).1 hderive⟩
  · rintro ⟨disposition, hdisposition, hderive⟩
    exact ⟨responseHornFamily I left right rightFinal
      event w j t disposition, by
        simp only [relevantGlobalResponseFamilies, List.mem_map]
        exact ⟨disposition, hdisposition, rfl⟩,
      (responseHorn_root_derives_iff
        I left right rightFinal event w j t disposition).2 hderive⟩

theorem relevantGlobalResponseRoot_derives_iff_responseId
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    HornDerives
        (hornFamilyCompiler
          (relevantGlobalResponseFamilies
            I left right rightFinal event w j t)) 1 ↔
      ∃ responseId,
        decideFirstEventResponseId I left right rightFinal
          event w j t responseId = true := by
  rw [relevantGlobalResponseRoot_derives_iff]
  constructor
  · rintro ⟨disposition, hmem, hderive⟩
    obtain ⟨responseId, rfl⟩ :=
      (mem_relevantGlobalDispositions_iff_responseId
        I left right event w j t disposition).1 hmem
    refine ⟨responseId, ?_⟩
    exact
      (globalDisposition_preserves_solver
        I left right rightFinal event w j t
        (firstEventQueryOfResponseId
          I left right event w j t responseId)).2
        ((globalDispositionSolved_iff_derives
          I left right rightFinal event w j t
          (globalDisposition
            (firstEventQueryOfResponseId
              I left right event w j t responseId))).2 hderive)
  · rintro ⟨responseId, hsolved⟩
    let query :=
      firstEventQueryOfResponseId
        I left right event w j t responseId
    let disposition := globalDisposition query
    refine ⟨disposition,
      (mem_relevantGlobalDispositions_iff_responseId
        I left right event w j t disposition).2
        ⟨responseId, rfl⟩, ?_⟩
    apply
      (globalDispositionSolved_iff_derives
        I left right rightFinal event w j t disposition).1
    exact
      (globalDisposition_preserves_solver
        I left right rightFinal event w j t query).1 hsolved

theorem firstEvent_check_false_derives_global_finite_root
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length)
    (hfalse :
      checkFirstEventLeakage I left right rightFinal
        event w j t = false) :
    HornDerives
      (hornFamilyCompiler
        (relevantGlobalResponseFamilies
          I left right rightFinal event w j t)) 1 := by
  have hfailure :=
    (firstEvent_check_false_iff_failure
      I left right rightFinal event w j t hjt ht).1 hfalse
  obtain ⟨query, hencodes, haccepted⟩ :=
    FirstEventReducedTerminal.exists_exact_solved_query
      rightFinal hfailure.reduce
  apply
    (relevantGlobalResponseRoot_derives_iff
      I left right rightFinal event w j t).2
  refine ⟨globalDisposition query, ?_, ?_⟩
  · simp only [relevantGlobalDispositions, List.mem_map]
    exact ⟨query,
      reducedTerminal_encodes_mem_relevant hencodes, rfl⟩
  · apply
      (globalDispositionSolved_iff_derives
        I left right rightFinal event w j t
          (globalDisposition query)).1
    exact
      (globalDisposition_preserves_solver
        I left right rightFinal event w j t query).1 haccepted

theorem classifiedResponseStream_nonavoider_or_global_finite_root
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
      ∃ (failedEvent : InsertionEvent α) (failedWord : Word α)
          (failedSource failedTarget : Nat),
        HornDerives
          (hornFamilyCompiler
            (relevantGlobalResponseFamilies I left right rightFinal
              failedEvent failedWord failedSource failedTarget)) 1 := by
  induction hclassified with
  | done w j t =>
      exact Or.inl
        (selectedRowWitness_contradicts_avoider
          I left right hrow w j t hwitness)
  | failed event events w j t terminal =>
      obtain ⟨query, hencodes, haccepted⟩ :=
        FirstEventReducedTerminal.exists_exact_solved_query
          rightFinal terminal
      apply Or.inr
      refine ⟨event, w, j, t, ?_⟩
      apply
        (relevantGlobalResponseRoot_derives_iff
          I left right rightFinal event w j t).2
      refine ⟨globalDisposition query, ?_, ?_⟩
      · simp only [relevantGlobalDispositions, List.mem_map]
        exact ⟨query,
          reducedTerminal_encodes_mem_relevant hencodes, rfl⟩
      · apply
          (globalDispositionSolved_iff_derives
            I left right rightFinal event w j t
              (globalDisposition query)).1
        exact
          (globalDisposition_preserves_solver
            I left right rightFinal event w j t query).1 haccepted
  | next event events w j t success tail ih =>
      have hnext :=
        selectedRowWitness_advance_of_success
          I left right rightFinal event w j t hwitness success
      simpa [InsertionEvent.applyStream] using ih hnext

theorem validStream_nonavoider_or_global_finite_root
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (hrow : (left, right) ∈ I.rows)
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hvalid : ValidRestorationStream events w)
    (hwitness : SelectedRowWitness I left right w j t) :
    (¬ I.toSOA.Avoider (InsertionEvent.applyStream events w)) ∨
      ∃ (failedEvent : InsertionEvent α) (failedWord : Word α)
          (failedSource failedTarget : Nat),
        HornDerives
          (hornFamilyCompiler
            (relevantGlobalResponseFamilies I left right rightFinal
              failedEvent failedWord failedSource failedTarget)) 1 := by
  apply classifiedResponseStream_nonavoider_or_global_finite_root
    I left right rightFinal hrow events w j t
  · exact classifiedResponseStream_total
      I left right rightFinal events w j t hvalid
        hwitness.source_lt_target hwitness.target_lt_length
  · exact hwitness

theorem global_finite_root_has_response_fixedPoint
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hroot :
      HornDerives
        (hornFamilyCompiler
          (relevantGlobalResponseFamilies
            I left right rightFinal event w j t)) 1) :
    ∃ disposition ∈
        relevantGlobalDispositions I left right event w j t,
      ∃ responseClass,
        DispositionHasClass I left right event w j t
          disposition responseClass ∧
        LeastFixedPointSpec
          (markAt (responseClassIndex responseClass))
          responseInitialMask
          (markAt (responseClassIndex responseClass)
            responseInitialMask) ∧
        decideLeastFixedPoint
          (markAt (responseClassIndex responseClass))
          responseInitialMask
          (responseClassIndex responseClass) = true := by
  obtain ⟨disposition, hmem, hderive⟩ :=
    (relevantGlobalResponseRoot_derives_iff
      I left right rightFinal event w j t).1 hroot
  obtain ⟨responseClass, hclass, hfixed, _⟩ :=
    globalDerivation_has_responseLeastFixedPoint
      I left right rightFinal event w j t disposition hderive
  exact ⟨disposition, hmem, responseClass, hclass, hfixed,
    decideResponseClassFixedPoint responseClass⟩

end NSSE
