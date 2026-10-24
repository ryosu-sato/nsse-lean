import NSSE.AddressedStatePresburger
import NSSE.AutomataMembership

/-!
# Automata conditions at linear-family addresses

Addressed DFA-state formulas are specialized to ordinary acceptance and
to productive-state lookup, the latter being exactly prefix-closure
membership for a certified productive DFA.
-/

namespace NSSE

universe u v

namespace LinearWordFamily

noncomputable def addressedProductiveFormula
    [Fintype Q]
    (automaton : ProductiveDFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat) :
    NatPresburger (arity + 1) :=
  family.addressedStatePredicateFormula
    automaton.automaton index offset
    (fun state => automaton.productive state = true)

theorem eval_addressedProductiveFormula_iff
    [Fintype Q]
    (automaton : ProductiveDFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat) :
    (family.addressedProductiveFormula automaton index
        offset).Eval
          (NatPresburger.extendValuation parameters copy) ↔
      Language.prefixClosure automaton.language
        (family.addressPrefix parameters index copy offset) := by
  rw [addressedProductiveFormula,
    family.eval_addressedStatePredicateFormula_iff]
  rw [automaton.prefixClosure_iff]
  rw [DFA.run_addressPrefix]

/-- A legal powered-block address satisfying a state predicate is one
Presburger conjunction. -/
noncomputable def validAddressedStatePredicateFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    NatPresburger (arity + 1) :=
  .conj
    (family.validPumpAddressFormula index offset)
    (family.addressedStatePredicateFormula automaton index
      offset predicate)

theorem eval_validAddressedStatePredicateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (copy offset : Nat)
    (predicate : Q → Prop) :
    (family.validAddressedStatePredicateFormula automaton
        index offset predicate).Eval
          (NatPresburger.extendValuation parameters copy) ↔
      family.ValidPumpAddress parameters index copy offset ∧
        predicate
          (DFA.stateAfterAddress automaton family parameters
            index copy offset) := by
  simp only [validAddressedStatePredicateFormula,
    NatPresburger.Eval]
  rw [family.eval_validPumpAddressFormula_iff,
    family.eval_addressedStatePredicateFormula_iff]

noncomputable def existsValidAddressedStatePredicateFormula
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    NatPresburger arity :=
  .existsQ
    (family.validAddressedStatePredicateFormula automaton
      index offset predicate)

theorem eval_existsValidAddressedStatePredicateFormula_iff
    [Fintype Q]
    (automaton : DFA α Q)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat)
    (index : Fin arity)
    (offset : Nat)
    (predicate : Q → Prop) :
    (family.existsValidAddressedStatePredicateFormula automaton
        index offset predicate).Eval parameters ↔
      ∃ copy,
        family.ValidPumpAddress parameters index copy offset ∧
          predicate
            (DFA.stateAfterAddress automaton family parameters
              index copy offset) := by
  simp only [existsValidAddressedStatePredicateFormula,
    NatPresburger.Eval]
  constructor
  · rintro ⟨copy, heval⟩
    exact ⟨copy,
      (family.eval_validAddressedStatePredicateFormula_iff
        automaton parameters index copy offset predicate).1 heval⟩
  · rintro ⟨copy, hcopy⟩
    exact ⟨copy,
      (family.eval_validAddressedStatePredicateFormula_iff
        automaton parameters index copy offset predicate).2 hcopy⟩

end LinearWordFamily

end NSSE
