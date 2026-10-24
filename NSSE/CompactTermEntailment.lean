import NSSE.SubtypeTermCompaction
import NSSE.StoredTermFiniteEntailment
import NSSE.StoredTermRegularEntailment

/-! # Term entailment decided after compaction, with an identifier-free bound

`StoredTermFiniteEntailment.bound_explicit` and its regular counterpart bound
the actual returned counter by seven exponentials of a polynomial in
`StoredQuerySize.size Q`, which charges the DECLARED variable universe and every
variable index in unary. This file composes those theorems with
`SubtypeTermCompaction`, so that the same decisions are certified with a bound
whose argument is a polynomial in `SubtypeTermCompaction.unitSize Q` — the plain
symbol count of the original query, which mentions neither the declared universe
nor the size of any variable name.

What is NOT claimed here: the compaction itself is an ordinary Lean function on
the original inductive query and its own cost is not counted; and the relation
between `unitSize` and an encoded input string, as well as machine-time
simulation of the counted implementation, remain open.
-/

namespace NSSE.CompactTermEntailment

open DirectRankStateTower DirectRankFormulaTower SubtypeTerms SubtypeTermCompaction

variable {n d : Nat}

/-- Compact the declared universe, then run the complete counted decision. -/
def decideFinite (Q : Query n d) (hd : 0 < d) : Bool × Nat :=
  StoredTermFiniteEntailment.decide (StoredTermQuery.packQuery (compactQuery Q))
    (StoredQueryWellFormed.packed (compactQuery Q)) hd

def decideAll (Q : Query n d) (hd : 0 < d) : Bool × Nat :=
  StoredTermRegularEntailment.decide (StoredTermQuery.packQuery (compactQuery Q))
    (StoredQueryWellFormed.packed (compactQuery Q)) hd

/-! ## Correctness for the ORIGINAL query, in all three semantics -/

theorem finite_correct (Q : Query n d) (hd : 0 < d) :
    (decideFinite Q hd).1 = true ↔ Entails (FiniteSubtypeTrees.constructor d) Q := by
  rw [decideFinite, StoredTermFiniteEntailment.correct (compactQuery Q) hd,
    entails_compactQuery (FiniteSubtypeTrees.constructor d) Q]

theorem arbitrary_correct (Q : Query n d) (hd : 0 < d) :
    (decideAll Q hd).1 = true ↔ Entails (AbsorbingSubtypeTrees.constructor d) Q := by
  rw [decideAll, StoredTermRegularEntailment.correct (compactQuery Q) hd,
    entails_compactQuery (AbsorbingSubtypeTrees.constructor d) Q]

theorem regular_correct (Q : Query n d) (hd : 0 < d) :
    (decideAll Q hd).1 = true ↔ SubtypeTermSemantics.RegularEntails Q := by
  rw [arbitrary_correct Q hd, TermEntailmentDecision.regular_entails_iff_all Q hd]

/-! ## The identifier-free seven-exponential bound -/

/-- The argument of the tower, with `u` the symbol count of the original query. -/
def argument (u d : Nat) := 16*((u+1)^2)^4+40*((u+1)^2)^3+53*((u+1)^2)^2+34*(u+1)^2+d+74426

theorem argument_polynomial (u d : Nat) :
    argument u d = 16*(u+1)^8+40*(u+1)^6+53*(u+1)^4+34*(u+1)^2+d+74426 := by
  unfold argument
  rw [← pow_mul, ← pow_mul, ← pow_mul]

theorem finite_bound (Q : Query n d) (hd : 0 < d) :
    (decideFinite Q hd).2 ≤ tower 7 (argument (unitSize Q) d) := by
  have hs := size_compactQuery Q
  refine (StoredTermFiniteEntailment.bound_explicit (StoredTermQuery.packQuery (compactQuery Q))
    (StoredQueryWellFormed.packed (compactQuery Q)) hd).trans (tower_mono 7 ?_)
  unfold argument
  gcongr <;> first | exact hs | omega

theorem all_bound (Q : Query n d) (hd : 0 < d) :
    (decideAll Q hd).2 ≤ tower 7 (argument (unitSize Q) d) := by
  have hs := size_compactQuery Q
  refine (StoredTermRegularEntailment.bound_explicit (StoredTermQuery.packQuery (compactQuery Q))
    (StoredQueryWellFormed.packed (compactQuery Q)) hd).trans (tower_mono 7 ?_)
  unfold argument
  gcongr <;> first | exact hs | omega

/-- Both statements at once, in the explicit polynomial form: the actual
counted decision of original nested-term entailment is correct for finite,
regular and arbitrary trees, and its returned counter is at most seven
exponentials of a polynomial in the query's symbol count. -/
theorem decide_complete (Q : Query n d) (hd : 0 < d) :
    ((decideFinite Q hd).1 = true ↔ Entails (FiniteSubtypeTrees.constructor d) Q) ∧
      ((decideAll Q hd).1 = true ↔ Entails (AbsorbingSubtypeTrees.constructor d) Q) ∧
      ((decideAll Q hd).1 = true ↔ SubtypeTermSemantics.RegularEntails Q) ∧
      (decideFinite Q hd).2 ≤ tower 7 (16*(unitSize Q+1)^8+40*(unitSize Q+1)^6+
        53*(unitSize Q+1)^4+34*(unitSize Q+1)^2+d+74426) ∧
      (decideAll Q hd).2 ≤ tower 7 (16*(unitSize Q+1)^8+40*(unitSize Q+1)^6+
        53*(unitSize Q+1)^4+34*(unitSize Q+1)^2+d+74426) :=
  ⟨finite_correct Q hd, arbitrary_correct Q hd, regular_correct Q hd,
    by simpa only [argument_polynomial] using finite_bound Q hd,
    by simpa only [argument_polynomial] using all_bound Q hd⟩

end NSSE.CompactTermEntailment
