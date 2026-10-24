import NSSE.StoredNextProblem
import NSSE.StoredPreparedRankStep
import NSSE.StoredRelationalNonempty

/-! The stored rank recursion: `solve h S` produces the existential package
deciding avoidance of a stored problem at rank `h`, by actual counted
construction — seed-only package, one stored next-rank step, the recursive
package, its counted lowering through the prepared rank step, and a stored
disjunction.  This is the stored analogue of
`DirectExistentialRankCompiler.solve` / `solve_correct`.  Costs are
accumulated but not yet bounded here. -/
namespace NSSE.StoredRankSolve
open FirstOrder FirstOrder.Language StoredRelationalRow StoredRelationalClosure GuardedRowFiring
open StoredNextProblem
open RankAvoidanceCompiler (Avoid RankBound avoid_split avoid_iff_lists)

variable {R : Nat → Type} {P : Type}

/-- The mathematical problem denoted by a stored problem. -/
abbrev Problem.original (S : Problem R P) : RankAvoidanceCompiler.Problem :=
  ⟨UniformWordLowering.wordLanguage R,P,S.c,S.candidate.original,S.k,S.ns,S.rows.original⟩

/-! ### One retained step -/

/-- Everything `next` computes, retained so that the lowering can use the
actual lifted rows and cleaned candidate without recomputation. -/
structure Step (R : Nat → Type) (P : Type) (S : Problem R P) where
  rows : StoredRelationArrayPackage.Family R (Fresh P) S.ns
  cleaned : StoredCleanedNextCandidate.Result R (Fresh P) S.ns
  table : StoredBranchEnumeration.Table S.ns
  fam : StoredRelationArrayPackage.Family (UnifiedBlockPresentation.Rel S.ns cleaned.cleaned.1) Empty
    (familyDims S.ns table)

def step (S : Problem R P) : Step R P S × Nat :=
  let r := liftRows S
  let c := liftCandidate S
  let a := StoredCleanedNextCandidate.build r.1 c.1 last
  let t := StoredBranchEnumeration.build S.ns
  let f := family S.ns a.1.cleaned.1 t.1
  (⟨r.1,a.1,t.1,f.1⟩,5+r.2+c.2+a.2+t.2+f.2)

def Step.problem {S : Problem R P} (st : Step R P S) :
    Problem (UnifiedBlockPresentation.Rel S.ns st.cleaned.cleaned.1) Empty :=
  ⟨st.table.count,familyDims S.ns st.table,st.cleaned.candidate.states.count,st.cleaned.candidate.row,st.fam⟩

theorem step_rows (S : Problem R P) : (step S).1.rows = (liftRows S).1 := rfl
theorem step_cleaned (S : Problem R P) : (step S).1.cleaned = (cleanedCandidate S).1 := rfl
theorem step_problem (S : Problem R P) :
    (⟨(step S).1.cleaned.cleaned.1,(step S).1.problem⟩ :
      (c' : Nat) × Problem (UnifiedBlockPresentation.Rel S.ns c') Empty) = (next S).1 := rfl

/-- Lowering a package of the next problem back to the source parameters,
through the actual lifted rows and the actual cleaned candidate. -/
def lower (S : Problem R P) (st : Step R P S)
    (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel S.ns st.cleaned.cleaned.1) Empty) :
    StoredRelationalClosure.Package R P × Nat :=
  StoredPreparedRankStep.build st.rows st.cleaned.cleaned.2 A

/-! ### The recursion -/

def solve : (h : Nat) → {R : Nat → Type} → {P : Type} → (S : Problem R P) →
    StoredRelationalClosure.Package R P × Nat
  | 0, _, _, S =>
    let a := StoredRelationalNonempty.seed S.candidate
    let st := step S
    let b := StoredRelationalNonempty.nonempty st.1.problem.candidate
    let l := lower S st.1 b.1
    let d := StoredRelationalPackages.disj a.1 l.1
    (d.1,4+a.2+st.2+b.2+l.2+d.2)
  | h+1, _, _, S =>
    let a := StoredRelationalNonempty.seed S.candidate
    let st := step S
    let r := solve h st.1.problem
    let l := lower S st.1 r.1
    let d := StoredRelationalPackages.disj a.1 l.1
    (d.1,4+a.2+st.2+r.2+l.2+d.2)

/-! ### Semantics -/

theorem lower_correct (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    [Nontrivial D] (p : P → D)
    (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel S.ns (step S).1.cleaned.cleaned.1) Empty) :
    Formula.Realize (lower S (step S).1 A).1.original.toFormula p ↔ ∃ s a : D,
      letI : (UnifiedBlockPresentation.language S.ns (step S).1.cleaned.cleaned.1).Structure (List D) :=
        stepModel S p s a
      A.original.toFormula.Realize (Empty.elim : Empty → List D) :=
  StoredPreparedRankStep.source_correct (liftRows S).1 (cleanedCandidate S).1.cleaned.2 A p

theorem next_candidate_nonempty (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (s a : D) (bs : List (List D)) :
    letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
    ((next S).1.2.candidate.original.dataNFA (Empty.elim : Empty → List D)).Accepts bs → bs ≠ [] := by
  letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
  letI := stepModel S p s a
  intro hC
  change ((StoredNextCandidate.build S.ns (cleanedCandidate S).1.cleaned.1).1.row.original.dataNFA
    (Empty.elim : Empty → List D)).Accepts bs at hC
  rw [StoredNextCandidate.accepts] at hC
  exact hC.1

/-- At rank zero only nonemptiness of the stored next candidate is needed. -/
theorem slice_zero_iff_nonempty (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    [DecidableEq D] (p : P → D) (s a : D)
    (hb : ∀ x body, (S.candidate.original.dataNFA p).Accepts (x :: body) →
      TerminalBorderRank.suffixBorderRank body = 0) :
    (∃ w : List D, (S.candidate.original.dataNFA p).Accepts (s :: (w ++ [a])) ∧
      ∀ i, ¬ Fires (S.rows.original i) p s (w ++ [a])) ↔
      letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
      ∃ bs : List (List D),
        ((next S).1.2.candidate.original.dataNFA (Empty.elim : Empty → List D)).Accepts bs := by
  letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
  letI := stepModel S p s a
  constructor
  · intro h
    obtain ⟨bs,hC,_⟩ := (slice_iff_next S p s a).mp h
    exact ⟨bs,hC⟩
  · rintro ⟨bs,hC⟩
    change ((StoredNextCandidate.build S.ns (cleanedCandidate S).1.cleaned.1).1.row.original.dataNFA
      (Empty.elim : Empty → List D)).Accepts bs at hC
    rw [StoredNextCandidate.accepts] at hC
    obtain ⟨hne,_,hC0⟩ := hC
    obtain ⟨w,hw⟩ := BlockCandidateTransport.decode_terminal (Sum.elim p ![s,a] last) bs hne
    rw [hw] at hC0
    change ((cleanedCandidate S).1.cleaned.2.original.dataNFA (Sum.elim p ![s,a])).Accepts
      (s :: (w ++ [a])) at hC0
    have hold : (S.candidate.original.dataNFA p).Accepts (s :: (w ++ [a])) := by
      have h1 := hC0
      change ((StoredCleanedNextCandidate.build (liftRows S).1 (liftCandidate S).1 last).1.cleaned.2.original.dataNFA
        (Sum.elim p ![s,a])).Accepts (s :: (w ++ [a])) at h1
      simp only [StoredCleanedNextCandidate.build,StoredCleanupFamily.accepts,liftCandidate_dataNFA] at h1
      exact h1.1
    refine ⟨w,(cleaned_avoidance S p s a w).mp ⟨hC0,?_⟩⟩
    intro i
    exact EmptyTailRemoval.no_positive_of_rank_zero _ _ s (w ++ [a]) (hb s (w ++ [a]) hold)

theorem avoid_next_iff (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (s a : D) :
    (letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a;
      Avoid (Problem.original (next S).1.2) (Empty.elim : Empty → List D)) ↔
      letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
      ∃ bs : List (List D),
        ((next S).1.2.candidate.original.dataNFA (Empty.elim : Empty → List D)).Accepts bs ∧
        ∀ j, ¬ Fires ((next S).1.2.rows.original j) (Empty.elim : Empty → List D)
          (bs.head?.getD []) bs.tail := by
  letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
  exact avoid_iff_lists (Problem.original (next S).1.2) Empty.elim ([] : List D)
    (fun xs => next_candidate_nonempty S p s a xs)

theorem solve_correct (h : Nat) : ∀ {R : Nat → Type} {P : Type} (S : Problem R P)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] [DecidableEq D] [Nontrivial D]
    (p : P → D), RankBound (Problem.original S) p h →
      (Formula.Realize (solve h S).1.original.toFormula p ↔ Avoid (Problem.original S) p) := by
  induction h with
  | zero =>
    intro R P S D M dec nt p hb
    rw [solve,StoredRelationalPackages.disj_original,ExistentialFormulaPackage.Package.disj_correct,
      StoredRelationalNonempty.seed_value,ExistentialRowNonempty.seedOnly_correct,avoid_split]
    apply or_congr Iff.rfl
    rw [lower_correct]
    apply exists_congr; intro s
    apply exists_congr; intro a
    letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
    letI := stepModel S p s a
    rw [StoredRelationalNonempty.nonempty_value,ExistentialRowNonempty.nonempty_correct]
    exact (slice_zero_iff_nonempty S p s a (fun x body hx => Nat.eq_zero_of_le_zero (hb x body hx))).symm
  | succ h ih =>
    intro R P S D M dec nt p hb
    rw [solve,StoredRelationalPackages.disj_original,ExistentialFormulaPackage.Package.disj_correct,
      StoredRelationalNonempty.seed_value,ExistentialRowNonempty.seedOnly_correct,avoid_split]
    apply or_congr Iff.rfl
    rw [lower_correct]
    apply exists_congr; intro s
    apply exists_congr; intro a
    letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
    letI := stepModel S p s a
    have hr : RankBound (Problem.original (next S).1.2) (Empty.elim : Empty → List D) h :=
      fun U body hC => next_rank_bound S p s a h hb U body hC
    exact ((ih (next S).1.2 (D := List D) Empty.elim hr).trans (avoid_next_iff S p s a)).trans
      (slice_iff_next S p s a).symm

end NSSE.StoredRankSolve
