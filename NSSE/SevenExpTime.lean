import NSSE.SevenExpTimeTarget
import NSSE.CodedDecisionExamples

/-! # The seven-exponential result, in the adopted cost model

## The cost model

Every function in the `Stored*`/`Counted*`/`Raw*` line returns a pair
`(value, steps)`: the algorithm and a step count charged at its every
elementary operation — list cell, constructor, comparison, table lookup. That
counter, and nothing else, is the cost model used here. By the maintainer's
decision of 2026-09-18 it is the model in which the complexity statement below
is made, exactly as formalised complexity results are normally stated relative
to a declared model.

What the model does and does not entail is kept explicit, not blurred:

* `MachineTimeBound.PolynomiallyFaithful c a T S` is the (unproved) premise
  relating a run of `S` counted steps to `T` machine steps; `MachineTimeBound`
  proves that under ANY such polynomial relation the tower height is unchanged
  and the argument shifts by an additive constant.
* `BitMachine` fixes a machine in which one step reads or moves one bit, and
  realises the first stage of the pipeline on it in linear time.
* `SevenExpTimeTarget.SevenExpTime` is the same statement on that machine. It
  remains OPEN; this file does not claim it.

## The result

For every positive arity `d`, an actual Lean function decides, from the BIT
CODE of an original nested-term entailment question, whether it is entailed —
over finite trees, over regular trees and over arbitrary trees — and its counted
step number, decoding included, is at most seven exponentials of an explicit
degree-eight polynomial in the length of that bit string, on EVERY input.
-/

namespace NSSE.SevenExpTime

open DirectRankStateTower SubtypeTerms RawQueryCodec CodedQueryConversion
open CodedTermEntailment SevenExpTimeTarget

/-- The explicit bound: `tower 7` of a degree-eight polynomial in `|w|`. -/
def bound (d L : Nat) : Nat := tower 7 (argument L d+1)

theorem bound_explicit (d L : Nat) :
    bound d L = tower 7 (16*((d+1)*(L+1)^2)^4+40*((d+1)*(L+1)^2)^3
      +53*((d+1)*(L+1)^2)^2+34*((d+1)*(L+1)^2)+d+74427) := by
  unfold bound argument
  congr 1

theorem bound_isPoly (d : Nat) : IsPoly (fun L => argument L d+1) := argument_isPoly d

/-! ## Finite trees -/

theorem finite (d : Nat) (hd : 0 < d) :
    (∀ w : List Bool, (decideFinite d w hd).2 ≤ bound d w.length) ∧
      (∀ (n : Nat) (Q : Query n d),
        (decideFinite d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
          Entails (FiniteSubtypeTrees.constructor d) Q) :=
  ⟨fun w => finite_bound d w hd,fun _ Q => finite_correct Q hd⟩

/-! ## Arbitrary and regular trees -/

theorem arbitrary (d : Nat) (hd : 0 < d) :
    (∀ w : List Bool, (decideAll d w hd).2 ≤ bound d w.length) ∧
      (∀ (n : Nat) (Q : Query n d),
        (decideAll d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
          Entails (AbsorbingSubtypeTrees.constructor d) Q) :=
  ⟨fun w => all_bound d w hd,fun _ Q => arbitrary_correct Q hd⟩

theorem regular (d : Nat) (hd : 0 < d) :
    (∀ w : List Bool, (decideAll d w hd).2 ≤ bound d w.length) ∧
      (∀ (n : Nat) (Q : Query n d),
        (decideAll d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
          SubtypeTermSemantics.RegularEntails Q) :=
  ⟨fun w => all_bound d w hd,fun _ Q => regular_correct Q hd⟩

/-! ## Everything at once -/

/-- **The result.** For every positive arity: on every bit string the counted
cost of the decision, decoding included, is at most `tower 7` of a degree-eight
polynomial in the input length; on the code of a query the answer is the
ORIGINAL entailment, in all three tree semantics; and the answer is not
constant — `⊤ ≤ ⊥` is rejected while reflexivity is accepted, so the
equivalences have content in both directions. -/
theorem result (d : Nat) (hd : 0 < d) :
    (∀ w : List Bool, (decideFinite d w hd).2 ≤ bound d w.length) ∧
      (∀ w : List Bool, (decideAll d w hd).2 ≤ bound d w.length) ∧
      (∀ (n : Nat) (Q : Query n d),
        (decideFinite d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
          Entails (FiniteSubtypeTrees.constructor d) Q) ∧
      (∀ (n : Nat) (Q : Query n d),
        (decideAll d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
          Entails (AbsorbingSubtypeTrees.constructor d) Q) ∧
      (∀ (n : Nat) (Q : Query n d),
        (decideAll d (encQuery (rawOfQuery Q)) hd).1 = some true ↔
          SubtypeTermSemantics.RegularEntails Q) ∧
      ((decideFinite d (encQuery (rawOfQuery (CodedDecisionExamples.Qrefl (d := d)))) hd).1
          = some true ∧
        (decideFinite d (encQuery (rawOfQuery (CodedDecisionExamples.Qtb (d := d)))) hd).1
          ≠ some true) :=
  ⟨(finite d hd).1,(arbitrary d hd).1,(finite d hd).2,(arbitrary d hd).2,(regular d hd).2,
    CodedDecisionExamples.decision_separates hd⟩

/-- The same, in the language form of `SevenExpTimeTarget`: the language of
codes of entailed queries has counted cost `tower 7 (poly)`. -/
theorem language_counted (d : Nat) (hd : 0 < d) :
    SevenExpTimeCounted (fun w => (decideFinite d w hd).2) ∧
      SevenExpTimeCounted (fun w => (decideAll d w hd).2) :=
  ⟨entailment_counted d hd,arbitrary_counted d hd⟩

/-! ## The boundary of the claim

Not claimed: several constructors, contravariance, disjunction, unrestricted
quantified inputs (the scope statement of v1358 is unchanged); a lower bound;
practical executability (a single evaluation of the pipeline is astronomically
expensive); and machine time, which is
`SevenExpTimeTarget.SevenExpTime (entailmentLanguage d hd)` and remains open.
-/

end NSSE.SevenExpTime
