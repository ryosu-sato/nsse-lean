import NSSE.AddressedSplitRoutePresburger

/-!
# The two route branches of component normal form are Presburger
-/

namespace NSSE

universe u v₁ v₂

namespace LinearWordFamily

noncomputable def prefixRouteFormula
    [Fintype Q]
    (automaton : ProductiveDFA α Q)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  NatPresburger.poweredStatePredicateFormula
    (family.dfaStages automaton.automaton)
    (automaton.automaton.run family.initial)
    (fun state => automaton.productive state = true)

theorem eval_prefixRouteFormula_iff
    [Fintype Q]
    (automaton : ProductiveDFA α Q)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (parameters : Fin arity → Nat) :
    (family.prefixRouteFormula automaton).Eval parameters ↔
      PrefixRoute
        (automataCapComponent automaton right)
        (family.word parameters) := by
  rw [prefixRouteFormula,
    NatPresburger.poweredStatePredicateFormula_correct,
    family.evaluate_dfaStages]
  unfold PrefixRoute automataCapComponent
  exact automaton.prefixClosure_iff
    (family.word parameters) |>.symm

noncomputable def componentRoutesFormula
    [Fintype Q₁] [Fintype Q₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity) :
    NatPresburger arity :=
  .disj
    (family.prefixRouteFormula left)
    (family.allAddressedSplitRoutesFormula left.automaton right)

theorem eval_componentRoutesFormula_iff
    [Fintype Q₁] [Fintype Q₂]
    (left : ProductiveDFA α Q₁)
    (right : ProductiveDFA α Q₂)
    (family : LinearWordFamily α arity)
    (hnonempty : family.PumpsNonempty)
    (parameters : Fin arity → Nat) :
    (family.componentRoutesFormula left right).Eval parameters ↔
      PrefixRoute (automataCapComponent left right)
          (family.word parameters) ∨
        SplitRoute (automataCapComponent left right)
          (family.word parameters) := by
  simp only [componentRoutesFormula, NatPresburger.Eval]
  rw [family.eval_prefixRouteFormula_iff left right,
    family.eval_allAddressedSplitRoutesFormula_iff_splitRoute
      left right hnonempty]

end LinearWordFamily

end NSSE
