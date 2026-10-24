import NSSE.ContraTermDecision
import NSSE.ContraEntailmentDecision
import NSSE.ContraFiniteEntailment

/-!
# Contravariant NSSE: the decision for original nested term input

Final assembly of the contravariant extension (stages S1–S7, notes/claude/claude_v163.md …
claude_v168.md). Signature: bottom, top and ONE constructor of arity `d > 0` with an
arbitrary polarity vector `POL` (`POL i = true`: contravariant in argument `i`). Input: a
finite list of inequalities and equalities between arbitrarily nested terms, and a query
`a ≤ b` between two terms. Semantics: the non-structural contravariant order on arbitrary
(possibly infinite) trees, defined as the greatest simulation (`ContraTrees`), on regular
trees, and on finite trees.

The flat decisions are `ContraEntailmentDecision.decideEntails_correct` (S4),
`decideRegularEntails_correct` and `ContraFiniteEntailment.decideFiniteEntails_correct`; the
term layer is `ContraTermDecision` (S7 part 1). This file only composes them.
No `sorry`; no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace NSSE.ContraTermEntailmentDecision

open SubtypeTerms (Query)
open ContraTrees ContraConstraints ContraTermSemantics ContraTermDecision

variable {n d : Nat} {POL : Polarity d}

/-- Term entailment over arbitrary contravariant trees is decided by `termDecideEntails`. -/
theorem decideAll_correct (Q : Query n d) (hd : 0 < d) :
    termDecideEntails POL Q hd = true ↔ ContraTermSemantics.Entails (treeConstructor POL) Q :=
  termDecideEntails_correct_of_flat Q hd
    (ContraEntailmentDecision.decideEntails_correct hd (flat POL Q hd))

/-- The same Boolean decides term entailment over regular contravariant trees. -/
theorem decideRegular_correct (Q : Query n d) (hd : 0 < d) :
    termDecideEntails POL Q hd = true ↔ ContraTermSemantics.RegularEntails POL Q :=
  termDecideEntails_regular_correct_of_flat Q hd
    (ContraEntailmentDecision.decideRegularEntails_correct hd (flat POL Q hd))

/-- Term entailment over finite contravariant trees is decided by `termDecideFiniteEntails`. -/
theorem decideFinite_correct (Q : Query n d) (hd : 0 < d) :
    termDecideFiniteEntails POL Q hd = true ↔
      ContraTermSemantics.Entails (finiteConstructor POL) Q :=
  termDecideFiniteEntails_correct_of_flat Q hd
    (ContraFiniteEntailment.decideFiniteEntails_correct hd (flat POL Q hd))

/-- Regular and arbitrary term entailment coincide. -/
theorem regular_entails_iff_all (Q : Query n d) (hd : 0 < d) :
    ContraTermSemantics.RegularEntails POL Q ↔
      ContraTermSemantics.Entails (treeConstructor POL) Q :=
  (decideRegular_correct Q hd).symm.trans (decideAll_correct Q hd)

/-- Decidability instances for the three semantic domains. -/
def allDecision (Q : Query n d) (hd : 0 < d) :
    Decidable (ContraTermSemantics.Entails (treeConstructor POL) Q) :=
  decidable_of_iff _ (decideAll_correct Q hd)

def regularDecision (Q : Query n d) (hd : 0 < d) :
    Decidable (ContraTermSemantics.RegularEntails POL Q) :=
  decidable_of_iff _ (decideRegular_correct Q hd)

def finiteDecision (Q : Query n d) (hd : 0 < d) :
    Decidable (ContraTermSemantics.Entails (finiteConstructor POL) Q) :=
  decidable_of_iff _ (decideFinite_correct Q hd)

end NSSE.ContraTermEntailmentDecision
