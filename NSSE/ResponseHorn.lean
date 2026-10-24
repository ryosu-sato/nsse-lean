import NSSE.GlobalTerminalBridge
import NSSE.HornCompiler
import NSSE.HornFamilyCompiler

/-!
# Concrete Horn compiler for the response rule family

One solved global response disposition is represented by a terminal
state and a single terminal-to-root Horn rule.  Root derivability is
proved exactly equivalent to the PWE/bounded disposition derivation.
-/

namespace NSSE

universe u vc vl vr

def decideGlobalDisposition
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    FirstEventGlobalDisposition I left right event w j t → Bool
  | .inl (.bounded _ _ query) =>
      (finiteGuardSolver I left right rightFinal
        event w j t).decide query
  | .inl _ => false
  | .inr terminal => decideResponsePWETerminal terminal

theorem decideGlobalDisposition_correct
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    decideGlobalDisposition I left right rightFinal
        event w j t disposition = true ↔
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition := by
  rw [← globalDispositionSolved_iff_derives]
  cases disposition with
  | inr terminal => rfl
  | inl tag =>
      cases tag <;>
        simp [decideGlobalDisposition, GlobalDispositionSolved]

def responseHornRule : HornRule where
  parent := 1
  children := [0]

def responseHornCompiler
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    FiniteHornCompiler where
  stateCount := 2
  terminal := fun state =>
    if state = 0 then
      decideGlobalDisposition I left right rightFinal
        event w j t disposition
    else false
  rules := [responseHornRule]

theorem decideResponseHornTerminal
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    decideHornState
        (responseHornCompiler I left right rightFinal
          event w j t disposition) 0 =
      decideGlobalDisposition I left right rightFinal
        event w j t disposition := by
  simp [decideHornState, responseHornCompiler, hornInitial,
    iterateMask, hornUpdate, hornBuild, hornNewBit, hornFires,
    allMaskBits, responseHornRule, maskBit, decideLeastFixedPoint]

theorem decideResponseHornRoot
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    decideHornState
        (responseHornCompiler I left right rightFinal
          event w j t disposition) 1 =
      decideGlobalDisposition I left right rightFinal
        event w j t disposition := by
  simp [decideHornState, responseHornCompiler, hornInitial,
    iterateMask, hornUpdate, hornBuild, hornNewBit, hornFires,
    allMaskBits, responseHornRule, maskBit, decideLeastFixedPoint]

theorem responseHorn_terminal_derives_iff
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    HornDerives
        (responseHornCompiler I left right rightFinal
          event w j t disposition) 0 ↔
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition := by
  rw [← decideGlobalDisposition_correct,
    ← decideResponseHornTerminal,
    decideHornState_correct
      (responseHornCompiler I left right rightFinal
        event w j t disposition) 0 (by
          simp [responseHornCompiler])]

theorem responseHorn_root_derives_iff
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    HornDerives
        (responseHornCompiler I left right rightFinal
          event w j t disposition) 1 ↔
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition := by
  rw [← decideGlobalDisposition_correct,
    ← decideResponseHornRoot,
    decideHornState_correct
      (responseHornCompiler I left right rightFinal
        event w j t disposition) 1 (by
          simp [responseHornCompiler])]

theorem decideResponseHornRoot_correct
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    decideHornState
        (responseHornCompiler I left right rightFinal
          event w j t disposition) 1 = true ↔
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition := by
  rw [decideHornState_correct
    (responseHornCompiler I left right rightFinal
      event w j t disposition) 1 (by
        simp [responseHornCompiler])]
  exact responseHorn_root_derives_iff
    I left right rightFinal event w j t disposition

theorem validStream_nonavoider_or_responseHornRoot
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
        ∃ disposition :
            FirstEventGlobalDisposition I left right
              failedEvent failedWord failedSource failedTarget,
          HornDerives
            (responseHornCompiler I left right rightFinal
              failedEvent failedWord failedSource failedTarget
              disposition)
            1 := by
  rcases validStream_nonavoider_or_globalDerivation
      I left right rightFinal hrow events w j t hvalid hwitness with
    hnot | ⟨failedEvent, failedWord, failedSource, failedTarget,
      disposition, hderive⟩
  · exact Or.inl hnot
  · exact Or.inr
      ⟨failedEvent, failedWord, failedSource, failedTarget,
        disposition,
        (responseHorn_root_derives_iff
          I left right rightFinal failedEvent failedWord
            failedSource failedTarget disposition).2 hderive⟩

def responseHornFamily
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    HornFamily where
  compiler :=
    responseHornCompiler I left right rightFinal
      event w j t disposition
  root := 1
  root_lt := by simp [responseHornCompiler]

theorem singletonResponseFamily_root_iff
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (disposition :
      FirstEventGlobalDisposition I left right event w j t) :
    HornDerives
        (hornFamilyCompiler
          [responseHornFamily I left right rightFinal
            event w j t disposition])
        1 ↔
      GlobalDispositionDerives I left right rightFinal
        event w j t disposition := by
  rw [hornFamilyRoot_derives_iff]
  constructor
  · rintro ⟨family, hmem, hderive⟩
    simp only [List.mem_singleton] at hmem
    subst family
    exact (responseHorn_root_derives_iff
      I left right rightFinal event w j t disposition).1 hderive
  · intro hderive
    exact ⟨responseHornFamily I left right rightFinal
      event w j t disposition, by simp,
      (responseHorn_root_derives_iff
        I left right rightFinal event w j t disposition).2 hderive⟩

theorem validStream_nonavoider_or_responseFamilyRoot
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
        ∃ disposition :
            FirstEventGlobalDisposition I left right
              failedEvent failedWord failedSource failedTarget,
          HornDerives
            (hornFamilyCompiler
              [responseHornFamily I left right rightFinal
                failedEvent failedWord failedSource failedTarget
                disposition])
            1 := by
  rcases validStream_nonavoider_or_globalDerivation
      I left right rightFinal hrow events w j t hvalid hwitness with
    hnot | ⟨failedEvent, failedWord, failedSource, failedTarget,
      disposition, hderive⟩
  · exact Or.inl hnot
  · exact Or.inr
      ⟨failedEvent, failedWord, failedSource, failedTarget,
        disposition,
        (singletonResponseFamily_root_iff
          I left right rightFinal failedEvent failedWord
            failedSource failedTarget disposition).2 hderive⟩

end NSSE
