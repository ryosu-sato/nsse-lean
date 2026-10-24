import NSSE.AddressedFactorCasePresburger

/-!
# Complete finite enumeration of addressed factor cases
-/

namespace NSSE

universe u v

def offsetPairs (firstLength secondLength : Nat) :
    List (Nat × Nat) :=
  (List.range (firstLength + 1)).flatMap fun first =>
    (List.range (secondLength + 1)).map fun second =>
      (first, second)

theorem mem_offsetPairs_iff
    (first second firstLength secondLength : Nat) :
    (first, second) ∈ offsetPairs firstLength secondLength ↔
      first ≤ firstLength ∧ second ≤ secondLength := by
  simp [offsetPairs]
  omega

namespace LinearWordFamily

def allAddressedFactorCases
    (family : LinearWordFamily α arity) :
    List (AddressedFactorCase arity) :=
  (offsetPairs family.initial.length family.initial.length).map
      (fun offsets =>
        .initialInitial offsets.1 offsets.2) ++
  (List.finRange arity).flatMap (fun endIndex =>
    (offsetPairs family.initial.length
      (family.pump endIndex).length).map (fun offsets =>
        .initialPump endIndex offsets.1 offsets.2)) ++
  (List.finRange arity).flatMap (fun endIndex =>
    (offsetPairs family.initial.length
      (family.separator endIndex).length).map (fun offsets =>
        .initialSeparator endIndex offsets.1 offsets.2)) ++
  (List.finRange arity).flatMap (fun index =>
    (offsetPairs (family.pump index).length
      (family.pump index).length).map (fun offsets =>
        .samePump index offsets.1 offsets.2)) ++
  (List.finRange arity).flatMap (fun startIndex =>
    (List.finRange arity).flatMap (fun endIndex =>
      (offsetPairs (family.pump startIndex).length
        (family.pump endIndex).length).map (fun offsets =>
          .crossPump startIndex endIndex offsets.1 offsets.2))) ++
  (List.finRange arity).flatMap (fun index =>
    (offsetPairs (family.pump index).length
      (family.separator index).length).map (fun offsets =>
        .pumpOwnSeparator index offsets.1 offsets.2)) ++
  (List.finRange arity).flatMap (fun startIndex =>
    (List.finRange arity).flatMap (fun endIndex =>
      (offsetPairs (family.pump startIndex).length
        (family.separator endIndex).length).map (fun offsets =>
          .pumpLaterSeparator startIndex endIndex
            offsets.1 offsets.2))) ++
  (List.finRange arity).flatMap (fun startIndex =>
    (List.finRange arity).flatMap (fun endIndex =>
      (offsetPairs (family.separator startIndex).length
        (family.pump endIndex).length).map (fun offsets =>
          .separatorPump startIndex endIndex
            offsets.1 offsets.2))) ++
  (List.finRange arity).flatMap (fun index =>
    (offsetPairs (family.separator index).length
      (family.separator index).length).map (fun offsets =>
        .sameSeparator index offsets.1 offsets.2)) ++
  (List.finRange arity).flatMap (fun startIndex =>
    (List.finRange arity).flatMap (fun endIndex =>
      (offsetPairs (family.separator startIndex).length
        (family.separator endIndex).length).map (fun offsets =>
          .separatorSeparator startIndex endIndex
            offsets.1 offsets.2)))

def AddressedFactorCaseOffsetsInRange
    (family : LinearWordFamily α arity) :
    AddressedFactorCase arity → Prop
  | .initialInitial startOffset endOffset =>
      startOffset ≤ family.initial.length ∧
      endOffset ≤ family.initial.length
  | .initialPump endIndex startOffset endOffset =>
      startOffset ≤ family.initial.length ∧
      endOffset ≤ (family.pump endIndex).length
  | .initialSeparator endIndex startOffset endOffset =>
      startOffset ≤ family.initial.length ∧
      endOffset ≤ (family.separator endIndex).length
  | .samePump index startOffset endOffset =>
      startOffset ≤ (family.pump index).length ∧
      endOffset ≤ (family.pump index).length
  | .crossPump startIndex endIndex startOffset endOffset =>
      startOffset ≤ (family.pump startIndex).length ∧
      endOffset ≤ (family.pump endIndex).length
  | .pumpOwnSeparator index startOffset endOffset =>
      startOffset ≤ (family.pump index).length ∧
      endOffset ≤ (family.separator index).length
  | .pumpLaterSeparator startIndex endIndex startOffset endOffset =>
      startOffset ≤ (family.pump startIndex).length ∧
      endOffset ≤ (family.separator endIndex).length
  | .separatorPump startIndex endIndex startOffset endOffset =>
      startOffset ≤ (family.separator startIndex).length ∧
      endOffset ≤ (family.pump endIndex).length
  | .sameSeparator index startOffset endOffset =>
      startOffset ≤ (family.separator index).length ∧
      endOffset ≤ (family.separator index).length
  | .separatorSeparator startIndex endIndex startOffset endOffset =>
      startOffset ≤ (family.separator startIndex).length ∧
      endOffset ≤ (family.separator endIndex).length

theorem addressedFactorCase_mem_all_iff
    (family : LinearWordFamily α arity)
    (factorCase : AddressedFactorCase arity) :
    factorCase ∈ family.allAddressedFactorCases ↔
      family.AddressedFactorCaseOffsetsInRange factorCase := by
  cases factorCase <;>
    simp [allAddressedFactorCases,
      AddressedFactorCaseOffsetsInRange,
      mem_offsetPairs_iff]

theorem addressedFactorCaseWitness_offsetsInRange
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (factorCase : AddressedFactorCase arity)
    (hwitness :
      family.AddressedFactorCaseWitness automaton parameters
        factorCase) :
    family.AddressedFactorCaseOffsetsInRange factorCase := by
  cases factorCase with
  | initialInitial startOffset endOffset =>
      exact ⟨hwitness.1.1.trans hwitness.1.2,
        hwitness.1.2⟩
  | initialPump endIndex startOffset endOffset =>
      obtain ⟨endCopy, hstart, hend, haccepts⟩ := hwitness
      exact ⟨hstart, hend.2⟩
  | initialSeparator endIndex startOffset endOffset =>
      exact ⟨hwitness.1, hwitness.2.1⟩
  | samePump index startOffset endOffset =>
      obtain ⟨startCopy, gap, hvalid, haccepts⟩ := hwitness
      exact ⟨hvalid.2.1, hvalid.2.2⟩
  | crossPump startIndex endIndex startOffset endOffset =>
      obtain ⟨startCopy, endCopy, remaining, hvalid, haccepts⟩ :=
        hwitness
      exact ⟨hvalid.2.2.2.1, hvalid.2.2.2.2⟩
  | pumpOwnSeparator index startOffset endOffset =>
      obtain ⟨startCopy, remaining, hvalid, haccepts⟩ := hwitness
      exact ⟨hvalid.2.1, hvalid.2.2⟩
  | pumpLaterSeparator startIndex endIndex startOffset endOffset =>
      obtain ⟨startCopy, remaining, hvalid, haccepts⟩ := hwitness
      exact ⟨hvalid.2.2.1, hvalid.2.2.2⟩
  | separatorPump startIndex endIndex startOffset endOffset =>
      obtain ⟨endCopy, hvalid, haccepts⟩ := hwitness
      exact ⟨hvalid.2.1, hvalid.2.2.2⟩
  | sameSeparator index startOffset endOffset =>
      exact ⟨hwitness.1.1.trans hwitness.1.2,
        hwitness.1.2⟩
  | separatorSeparator startIndex endIndex startOffset endOffset =>
      exact ⟨hwitness.1.2.1, hwitness.1.2.2⟩

noncomputable def allAddressedFactorAcceptanceFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  family.addressedFactorCasesFormula automaton
    family.allAddressedFactorCases

theorem eval_allAddressedFactorAcceptanceFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    (family.allAddressedFactorAcceptanceFormula automaton).Eval
        parameters ↔
      ∃ factorCase,
        family.AddressedFactorCaseWitness automaton parameters
          factorCase := by
  rw [allAddressedFactorAcceptanceFormula,
    family.eval_addressedFactorCasesFormula_iff]
  constructor
  · rintro ⟨factorCase, hmem, hwitness⟩
    exact ⟨factorCase, hwitness⟩
  · rintro ⟨factorCase, hwitness⟩
    refine ⟨factorCase, ?_, hwitness⟩
    rw [family.addressedFactorCase_mem_all_iff]
    exact family.addressedFactorCaseWitness_offsetsInRange
      automaton parameters factorCase hwitness

end LinearWordFamily

end NSSE
