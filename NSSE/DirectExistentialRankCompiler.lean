import NSSE.ExistentialRowNonempty
import NSSE.FiniteRankDecision

/-! # Actual recursive existential rank compiler using bounded scalar lowering -/

namespace NSSE.DirectExistentialRankCompiler

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ExistentialFormulaPackage ArrayAtomExistentialPackages
open RankAvoidanceCompiler (Problem Avoid RankBound avoid_split)
open DirectRankTransition DirectRankResources DirectRankExistentialStep

def solve : (h : Nat) → (I : Problem) →
    (∀ i, RowQF (I.rows i)) → RowQF I.candidate → Package I.language I.Parameters
  | 0, I, hr, hc => Package.disj (ExistentialRowNonempty.seedOnly I.candidate hc)
      (lowerStep I hr hc (ExistentialRowNonempty.nonempty (next I).candidate (next_candidate_qf I)))
  | h+1, I, hr, hc => Package.disj (ExistentialRowNonempty.seedOnly I.candidate hc)
      (lowerStep I hr hc (solve h (next I) (next_rows_qf I) (next_candidate_qf I)))

universe u

theorem solve_correct (h : Nat) : ∀ (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    {D : Type u} [I.language.Structure D] [DecidableEq D] [Nontrivial D] (p : I.Parameters → D),
    RankBound I p h → ((solve h I hr hc).toFormula.Realize p ↔ Avoid I p) := by
  induction h with
  | zero =>
    intro I hr hc D M dec nt p hb
    rw [solve, Package.disj_correct, ExistentialRowNonempty.seedOnly_correct, lowerStep_correct, avoid_split]
    apply or_congr Iff.rfl
    apply exists_congr
    intro s
    apply exists_congr
    intro a
    letI := stepModel I (Sum.elim p ![s,a])
    rw [ExistentialRowNonempty.nonempty_correct]
    exact (slice_zero_iff_nonempty I p s a hb).symm
  | succ h ih =>
    intro I hr hc D M dec nt p hb
    rw [solve, Package.disj_correct, ExistentialRowNonempty.seedOnly_correct, lowerStep_correct, avoid_split]
    apply or_congr Iff.rfl
    apply exists_congr
    intro s
    apply exists_congr
    intro a
    letI := stepModel I (Sum.elim p ![s,a])
    exact (ih (next I) (next_rows_qf I) (next_candidate_qf I) (D := List D) Empty.elim
      (next_rank_bound I p s a h hb)).trans (slice_iff_next I p s a).symm

theorem solve_body_qf (h : Nat) (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate) :
    (solve h I hr hc).boundedBody.IsQF := Package.boundedBody_qf _

theorem solve_exs_correct (h : Nat) (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    {D : Type*} [I.language.Structure D] [DecidableEq D] [Nontrivial D] (p : I.Parameters → D)
    (hb : RankBound I p h) :
    (solve h I hr hc).boundedBody.exs.Realize p ↔ Avoid I p := solve_correct h I hr hc p hb

/-- Execute the actual finite-model evaluator on the generated existential sentence. -/
def evaluate (h : Nat) (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    {D : Type*} [I.language.Structure D] [Fintype D] [DecidableEq D]
    (relDec : FiniteRankDecision.RelationDecision I.language D) (p : I.Parameters → D) : Bool :=
  FiniteRankDecision.evaluate relDec (solve h I hr hc).toFormula p

theorem evaluate_correct (h : Nat) (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    {D : Type*} [I.language.Structure D] [Fintype D] [DecidableEq D] [Nontrivial D]
    (relDec : FiniteRankDecision.RelationDecision I.language D) (p : I.Parameters → D) (hb : RankBound I p h) :
    evaluate h I hr hc relDec p = true ↔ Avoid I p :=
  (FiniteRankDecision.evaluate_correct relDec _ p).trans (solve_correct h I hr hc p hb)

end NSSE.DirectExistentialRankCompiler
