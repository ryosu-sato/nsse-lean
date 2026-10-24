import NSSE.ExplicitOriginalSOARows

/-! Original finite SOA inputs into the concrete, counted rank evaluator. -/

namespace NSSE.ExplicitFiniteSOADecision

open RankAvoidanceCompiler GuardedRowFiring SymbolicGuardedBlocks
open FiniteSOARankDecision (InputDFA Component toSOA)
open ArrayAtomExistentialPackages ExplicitUnaryTableLanguage FiniteValuationLookup

variable {d : Nat}

def compiledRows (rows : List (Component (Fin d))) (i : Fin rows.length) :=
  ExplicitOriginalSOARows.compile (rows.get i).left.automaton (rows.get i).right.automaton

abbrev problem (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) :=
  ConcreteValuationEvaluationTower.problem (compiledRows rows)
    (ExplicitOriginalSOARows.candidate C.automaton)

theorem rows_qf (rows : List (Component (Fin d))) (i : Fin rows.length) :
    RowQF (compiledRows rows i) := ExplicitOriginalSOARows.compile_qf _ _

theorem candidate_correct (C : InputDFA (Fin d)) (rows : List (Component (Fin d)))
    (p : Fin 0 → Fin d) (s : Fin d) (body : List (Fin d)) :
    ((problem C rows).candidate.dataNFA p).Accepts (s :: body) ↔ C.automaton.Accepts body :=
  ExplicitOriginalSOARows.candidate_correct C.automaton p s body

theorem row_correct (C : InputDFA (Fin d)) (rows : List (Component (Fin d)))
    (p : Fin 0 → Fin d) (s : Fin d) (body : List (Fin d)) (i : Fin rows.length) :
    Fires ((problem C rows).rows i) p s body ↔ NSSE.MarkedOccurrence (rows.get i).denote body :=
  ExplicitOriginalSOARows.fires_correct (rows.get i).left.automaton (rows.get i).right.automaton p s body

theorem rootCov_iff_index (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) (body : List (Fin d)) :
    (toSOA C rows).RootCov body ↔
      ∃ i : Fin rows.length, NSSE.MarkedOccurrence (rows.get i).denote body := by
  constructor
  · rintro ⟨R, hR, hocc⟩
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hR
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
    exact ⟨i, by simpa only [hi] using hocc⟩
  · rintro ⟨i, hocc⟩
    refine ⟨(rows.get i).denote, ?_, hocc⟩
    exact List.mem_map.mpr ⟨rows.get i, List.mem_iff_get.mpr ⟨i, rfl⟩, rfl⟩

/-- A concrete seed is needed only to witness a nonempty base alphabet.
The candidate permits every seed and the original cap rows ignore it. -/
theorem avoid_iff (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) (p : Fin 0 → Fin d) (seed : Fin d) :
    Avoid (problem C rows) p ↔ ∃ body : List (Fin d), (toSOA C rows).Avoider body := by
  unfold Avoid
  simp only [ExplicitOriginalSOARows.candidate_correct, compiledRows, ExplicitOriginalSOARows.fires_correct]
  change (∃ s body, C.automaton.Accepts body ∧
    ∀ i : Fin rows.length, ¬ NSSE.MarkedOccurrence (rows.get i).denote body) ↔
    ∃ body : List (Fin d), C.automaton.Accepts body ∧ ¬ (toSOA C rows).RootCov body
  simp only [rootCov_iff_index, not_exists]
  constructor
  · rintro ⟨_, body, hC, hrows⟩
    exact ⟨body, hC, hrows⟩
  · rintro ⟨body, hC, hrows⟩
    exact ⟨seed, body, hC, hrows⟩

theorem rankBound_of_candidate (C : InputDFA (Fin d)) (rows : List (Component (Fin d)))
    (p : Fin 0 → Fin d) (h : Nat)
    (hb : ∀ body, C.automaton.Accepts body → TerminalBorderRank.suffixBorderRank body ≤ h) :
    RankBound (problem C rows) p h := by
  intro s body hC
  exact hb body ((candidate_correct C rows p s body).mp hC)

def decide (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) (h : Nat) : Bool × Nat :=
  ConcreteValuationEvaluationTower.evaluate h (compiledRows rows)
    (ExplicitOriginalSOARows.candidate C.automaton) (rows_qf rows)
    (ExplicitOriginalSOARows.candidate_qf C.automaton) (Values.nil : Values d 0)

theorem decide_correct [Nontrivial (Fin d)]
    (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) (h : Nat) (seed : Fin d)
    (hb : ∀ body, C.automaton.Accepts body → TerminalBorderRank.suffixBorderRank body ≤ h) :
    (decide C rows h).1 = true ↔ ∃ body : List (Fin d), (toSOA C rows).Avoider body :=
  (ConcreteValuationEvaluationTower.evaluate_correct h (compiledRows rows) _ (rows_qf rows)
    (ExplicitOriginalSOARows.candidate_qf C.automaton) Values.nil
    (rankBound_of_candidate C rows _ h hb)).trans (avoid_iff C rows _ seed)

theorem decide_bound (C : InputDFA (Fin d)) (rows : List (Component (Fin d))) (h : Nat) :
    let S := DirectRankHorizonStates.initialBudget (problem C rows)
    (decide C rows h).2 ≤ DirectRankStateTower.tower 4 (8*h^2+4*S*h+23*h+7*S+2*d+3144) := by
  simpa only [Nat.add_zero] using ConcreteValuationEvaluationTower.evaluate_tower h
    (compiledRows rows) _ (rows_qf rows) (ExplicitOriginalSOARows.candidate_qf C.automaton)
    (Values.nil : Values d 0)

theorem decide_nonlive_correct [Nontrivial (Fin d)]
    (G C : InputDFA (Fin d)) (rows : List (Component (Fin d))) (seed : Fin d)
    (hpc : NonliveBorderRank.PrefixClosed G.automaton)
    (hsub : ∀ body, C.automaton.Accepts body →
      (NonliveBorderRank.nonliveDFA G.automaton).Accepts body) :
    (decide C rows (G.count - 2)).1 = true ↔
      ∃ body : List (Fin d), (toSOA C rows).Avoider body := by
  apply decide_correct C rows (G.count - 2) seed
  intro body hC
  obtain ⟨hG, hn⟩ := (NonliveBorderRank.nonliveDFA_accepts_iff G.automaton hpc body).mp (hsub body hC)
  have hr := NonliveBorderRank.nonlive_rank_le_states_sub_two G.automaton hpc Finset.univ
    (fun _ _ => Finset.mem_univ _) hG hn
  simpa using hr

end NSSE.ExplicitFiniteSOADecision
