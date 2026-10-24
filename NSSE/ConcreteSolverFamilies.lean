import NSSE.IndexedHornFamily
import NSSE.CountStream
import NSSE.GlobalTerminalBridge

/-!
# Concrete exact-solver Horn families

This module registers three already finite, executable pieces of the
compiler semantics under the common `HornFamily` interface:

* post-compression identity loops;
* the `0 / 1 / ≥2` retained-count edge classification;
* literal suffix-copy disequality terminals.

Each family has two Horn states.  Its root is derivable exactly when the
corresponding concrete semantic proposition holds.
-/

namespace NSSE

universe u vc vl vr

def identityLoopSolver (wireEq : ExactEqTest Wire) :
    ExactSolver (LoopSummary Wire) where
  formula := IdentityLoop
  decide := isIdentityLoop wireEq
  correct := isIdentityLoop_correct wireEq

def identityLoopHornFamily
    (wireEq : ExactEqTest Wire) (loop : LoopSummary Wire) :
    HornFamily :=
  exactSolverHornFamily (identityLoopSolver wireEq) loop

theorem identityLoopHornFamily_derives_iff
    (wireEq : ExactEqTest Wire) (loop : LoopSummary Wire) :
    HornDerives
        (identityLoopHornFamily wireEq loop).compiler
        (identityLoopHornFamily wireEq loop).root ↔
      IdentityLoop loop :=
  exactSolverHornFamily_derives_iff (identityLoopSolver wireEq) loop

structure CountEdgeQuery where
  retainedBefore : Nat
  expected : CountEdgeKind

def countEdgeSolver : ExactSolver CountEdgeQuery where
  formula := fun query =>
    countEdgeKind query.retainedBefore = query.expected
  decide := fun query =>
    decide (countEdgeKind query.retainedBefore = query.expected)
  correct := by
    intro query
    simp

def countEdgeHornFamily (query : CountEdgeQuery) : HornFamily :=
  exactSolverHornFamily countEdgeSolver query

theorem countEdgeHornFamily_derives_iff (query : CountEdgeQuery) :
    HornDerives
        (countEdgeHornFamily query).compiler
        (countEdgeHornFamily query).root ↔
      countEdgeKind query.retainedBefore = query.expected :=
  exactSolverHornFamily_derives_iff countEdgeSolver query

theorem firstCountEdgeHornFamily_derives_iff (n : Nat) :
    HornDerives
        (countEdgeHornFamily ⟨n, .first⟩).compiler
        (countEdgeHornFamily ⟨n, .first⟩).root ↔
      n = 0 := by
  rw [countEdgeHornFamily_derives_iff, countEdgeKind_first_iff]

theorem secondCountEdgeHornFamily_derives_iff (n : Nat) :
    HornDerives
        (countEdgeHornFamily ⟨n, .second⟩).compiler
        (countEdgeHornFamily ⟨n, .second⟩).root ↔
      n = 1 := by
  rw [countEdgeHornFamily_derives_iff, countEdgeKind_second_iff]

theorem stableCountEdgeHornFamily_derives_iff (n : Nat) :
    HornDerives
        (countEdgeHornFamily ⟨n, .stable⟩).compiler
        (countEdgeHornFamily ⟨n, .stable⟩).root ↔
      2 ≤ n := by
  rw [countEdgeHornFamily_derives_iff, countEdgeKind_stable_iff]

def countExpectedSolver (n : Nat) : ExactSolver CountEdgeKind where
  formula := fun expected => countEdgeKind n = expected
  decide := fun expected => decide (countEdgeKind n = expected)
  correct := by
    intro expected
    simp

def countEdgeIndexedFamily (n : Nat) :
    IndexedHornFamily CountEdgeKind :=
  IndexedHornFamily.ofExactSolver
    countEdgeKindEnumeration (countExpectedSolver n)

theorem countEdgeIndexedFamily_root_derives (n : Nat) :
    HornDerives (countEdgeIndexedFamily n).compiler 1 := by
  rw [countEdgeIndexedFamily,
    IndexedHornFamily.ofExactSolver_root_derives_iff]
  exact ⟨countEdgeKind n, rfl⟩

theorem countEdgeIndexedFamily_root_derives_iff (n : Nat) :
    HornDerives (countEdgeIndexedFamily n).compiler 1 ↔
      ∃ expected, countEdgeKind n = expected := by
  exact IndexedHornFamily.ofExactSolver_root_derives_iff
    countEdgeKindEnumeration (countExpectedSolver n)

def suffixDisequalityHornFamily [DecidableEq α]
    (query : SuffixDisequalityQuery α) : HornFamily :=
  exactSolverHornFamily suffixDisequalitySolver query

theorem suffixDisequalityHornFamily_derives_iff
    [DecidableEq α] (query : SuffixDisequalityQuery α) :
    HornDerives
        (suffixDisequalityHornFamily query).compiler
        (suffixDisequalityHornFamily query).root ↔
      Word.factor query.word query.source
          (query.word.length - query.target) ≠
        Word.factor query.word query.target
          (query.word.length - query.target) :=
  exactSolverHornFamily_derives_iff suffixDisequalitySolver query

def finiteGuardHornFamily
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (query : FirstEventFiniteGuardQuery I left right event w j t) :
    HornFamily :=
  exactSolverHornFamily
    (finiteGuardSolver I left right rightFinal event w j t) query

def finiteGuardIndexedFamily
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    IndexedHornFamily
      (FirstEventFiniteGuardQuery I left right event w j t) :=
  IndexedHornFamily.ofExactSolver
    (finiteGuardQueryEnumeration I left right event w j t)
    (finiteGuardSolver I left right rightFinal event w j t)

theorem finiteGuardIndexedFamily_root_derives_iff
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat) :
    HornDerives
        (finiteGuardIndexedFamily I left right rightFinal
          event w j t).compiler 1 ↔
      ∃ query,
        finiteGuardFormula I left right event w j t query := by
  exact IndexedHornFamily.ofExactSolver_root_derives_iff
    (finiteGuardQueryEnumeration I left right event w j t)
    (finiteGuardSolver I left right rightFinal event w j t)

theorem finiteGuardHornFamily_derives_iff
    [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (query : FirstEventFiniteGuardQuery I left right event w j t) :
    HornDerives
        (finiteGuardHornFamily I left right rightFinal
          event w j t query).compiler
        (finiteGuardHornFamily I left right rightFinal
          event w j t query).root ↔
      finiteGuardFormula I left right event w j t query :=
  exactSolverHornFamily_derives_iff
    (finiteGuardSolver I left right rightFinal event w j t) query

def firstEventTerminalHornFamily
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (query : FirstEventTerminalQuery I left right event w j t) :
    HornFamily :=
  exactSolverHornFamily
    (firstEventTerminalSolver I left right rightFinal event w j t)
    query

theorem firstEventTerminalHornFamily_derives_iff
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (query : FirstEventTerminalQuery I left right event w j t) :
    HornDerives
        (firstEventTerminalHornFamily I left right rightFinal
          event w j t query).compiler
        (firstEventTerminalHornFamily I left right rightFinal
          event w j t query).root ↔
      (firstEventTerminalSolver I left right rightFinal
        event w j t).formula query :=
  exactSolverHornFamily_derives_iff
    (firstEventTerminalSolver I left right rightFinal event w j t)
    query

theorem firstEvent_check_false_has_Horn_root
    [DecidableEq α] [DecidableEq QC] [DecidableEq QL]
    (I : AutomataSOAInstance α QC QL QR)
    (left : DFA α QL) (right : DFA α QR)
    (rightFinal : DFAFinalTest right)
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hjt : j < t) (ht : t < w.length)
    (hfalse :
      checkFirstEventLeakage I left right rightFinal
        event w j t = false) :
    ∃ query,
      HornDerives
        (firstEventTerminalHornFamily I left right rightFinal
          event w j t query).compiler
        (firstEventTerminalHornFamily I left right rightFinal
          event w j t query).root := by
  obtain ⟨query, haccepted⟩ :=
    firstEvent_check_false_has_solved_terminal
      I left right rightFinal event w j t hjt ht hfalse
  refine ⟨query, ?_⟩
  rw [firstEventTerminalHornFamily_derives_iff,
    ← (firstEventTerminalSolver I left right rightFinal
      event w j t).correct query]
  exact haccepted

end NSSE
