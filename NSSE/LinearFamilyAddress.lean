import NSSE.LinearWordFamily
import Mathlib.Algebra.BigOperators.Fin

/-!
# Addresses in a linear word family

For a fixed pumped segment and fixed within-copy offset, the absolute
position is affine in the family parameters and in the quantified copy
number. This is the address arithmetic used in Theorem A.
-/

namespace NSSE

universe u

namespace LinearWordFamily

def precedingIndices (index : Fin arity) :
    Finset (Fin arity) :=
  Finset.univ.filter fun earlier => earlier < index

def addressPosition
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) : Nat :=
  family.initial.length +
    ∑ earlier ∈ precedingIndices index,
      (parameters earlier *
        (family.pump earlier).length +
        (family.separator earlier).length) +
    copy * (family.pump index).length +
    offset

def addressExpression
    (family : LinearWordFamily α arity)
    (index : Fin arity) (offset : Nat) :
    NatLinearExpr (arity + 1) where
  constant :=
    family.initial.length +
      ∑ earlier ∈ precedingIndices index,
        (family.separator earlier).length +
      offset
  coefficient :=
    Fin.lastCases
      (family.pump index).length
      (fun earlier =>
        if earlier < index
        then (family.pump earlier).length
        else 0)

def addressPrefix
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) : Word α :=
  family.initial ++
    ((List.finRange arity).filter
      (fun earlier => earlier < index)).flatMap
        (fun earlier =>
          Word.power (family.pump earlier)
              (parameters earlier) ++
            family.separator earlier) ++
    Word.power (family.pump index) copy ++
    (family.pump index).take offset

theorem addressPrefix_length
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat)
    (hoffset : offset ≤ (family.pump index).length) :
    (family.addressPrefix parameters index copy offset).length =
      family.addressPosition parameters index copy offset := by
  classical
  have hsum (f : Fin arity → Nat) :
      (((List.finRange arity).filter
          (fun earlier => earlier < index)).map f).sum =
        ∑ earlier ∈ precedingIndices index, f earlier := by
    rw [← List.sum_toFinset f
      ((List.nodup_finRange arity).filter _)]
    simp [precedingIndices]
  simp [addressPrefix, addressPosition,
    List.length_flatMap, Word.power_length,
    Nat.min_eq_left hoffset, hsum,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem addressPosition_eq_expression
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) :
    family.addressPosition parameters index copy offset =
      (family.addressExpression index offset).Eval
        (NatPresburger.extendValuation parameters copy) := by
  classical
  unfold addressPosition addressExpression
    NatLinearExpr.Eval
  rw [Fin.sum_univ_castSucc]
  simp only [NatPresburger.extendValuation_castSucc,
    NatPresburger.extendValuation_last,
    Fin.lastCases_castSucc, Fin.lastCases_last]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [precedingIndices]
  rw [Finset.sum_add_distrib]
  simp [Nat.mul_comm, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

/-- A powered-block address is legal when its copy exists and its offset
lies inside that copy. -/
def ValidPumpAddress
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) : Prop :=
  copy < parameters index ∧
  offset ≤ (family.pump index).length

def validPumpAddressFormula
    (family : LinearWordFamily α arity)
    (index : Fin arity) (offset : Nat) :
    NatPresburger (arity + 1) :=
  .conj
    (.lessEqual
      (.add (.varExpr (Fin.last arity)) (.const 1))
      (.varExpr index.castSucc))
    (if offset ≤ (family.pump index).length
      then .equal (.const 0) (.const 0)
      else .falsum)

theorem eval_validPumpAddressFormula_iff
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) :
    (family.validPumpAddressFormula index offset).Eval
        (NatPresburger.extendValuation parameters copy) ↔
      family.ValidPumpAddress parameters index copy offset := by
  classical
  unfold validPumpAddressFormula ValidPumpAddress
  simp only [NatPresburger.Eval,
    NatLinearExpr.eval_add, NatLinearExpr.eval_variable,
    NatLinearExpr.eval_const,
    NatPresburger.extendValuation_last,
    NatPresburger.extendValuation_castSucc]
  by_cases hoffset :
      offset ≤ (family.pump index).length
  · simp [hoffset, NatPresburger.Eval]
    omega
  · simp [hoffset, NatPresburger.Eval]

/-- The endpoint of a legal address does not pass the end of its own
pumped segment. -/
theorem address_local_end_le
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat)
    (hvalid :
      family.ValidPumpAddress parameters index copy offset) :
    copy * (family.pump index).length + offset ≤
      parameters index * (family.pump index).length := by
  rcases hvalid with ⟨hcopy, hoffset⟩
  have hsucc : copy + 1 ≤ parameters index := by omega
  calc
    copy * (family.pump index).length + offset ≤
        copy * (family.pump index).length +
          (family.pump index).length :=
      Nat.add_le_add_left hoffset _
    _ = (copy + 1) * (family.pump index).length := by
      rw [Nat.add_mul, Nat.one_mul]
    _ ≤ parameters index *
          (family.pump index).length :=
      Nat.mul_le_mul_right _ hsucc

def precedingWord
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity) : Word α :=
  ((List.finRange arity).filter
    (fun earlier => earlier < index)).flatMap
      (fun earlier =>
        Word.power (family.pump earlier)
            (parameters earlier) ++
          family.separator earlier)

def DFA.stateAfterAddress
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) : Q :=
  automaton.runFrom
    (automaton.runFrom
      (automaton.runFrom
        (automaton.run family.initial)
        (family.precedingWord parameters index))
      (Word.power (family.pump index) copy))
    ((family.pump index).take offset)

/-- Lemma A.0's state-composition formula at a powered-block address. -/
theorem DFA.run_addressPrefix
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) :
    automaton.run
        (family.addressPrefix parameters index copy offset) =
      DFA.stateAfterAddress automaton family parameters
        index copy offset := by
  unfold addressPrefix DFA.stateAfterAddress
  simp only [precedingWord]
  simp only [automaton.run_append, automaton.runFrom_append,
    List.append_assoc]

end LinearWordFamily

end NSSE
