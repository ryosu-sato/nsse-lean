import NSSE.StoredRankDecisionTower

/-! Actual counted terminal evaluation from stored cap inputs. The semantic
correctness theorem derives its rank promise from the constructed nonlive
candidate; it does not ask the caller for a rank or short-avoider bound. -/
namespace NSSE.StoredTerminalDecision
open FirstOrder FirstOrder.Language
variable {d : Nat}

def decide (E : StoredNormalizationBuild.Data) : Bool × Nat :=
  let f := StoredTerminalInput.fromCap (d := d) E
  let r := StoredRankAdapter.decide (d := d) f.1.problem f.1.rank
  (r.1,1+f.2+r.2)

theorem problem_value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (StoredTerminalInput.fromCap (d := d) (StoredNormalizationBuild.snapshot E)).1.problem =
      StoredRankAdapter.inputOf (FiniteCapTerminal.residual (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E))
        (FiniteCapFrontEnd.prepared E).rows := by
  simp only [StoredTerminalInput.fromCap, StoredCapFrontEnd.value,
    StoredTerminalInput.build, StoredCapFrontEnd.snapshot, StoredResidualDFA.value]

theorem rank_value (E : FiniteCapFrontEnd.Input (Fin d)) :
    (StoredTerminalInput.fromCap (d := d) (StoredNormalizationBuild.snapshot E)).1.rank =
      (FiniteCapFrontEnd.G E).count-2 := by
  simp only [StoredTerminalInput.fromCap, StoredCapFrontEnd.value,
    StoredTerminalInput.build, StoredCapFrontEnd.snapshot, StoredTerminalInput.rank_value]
  rfl

theorem correct (E : FiniteCapFrontEnd.Input (Fin d)) [Nontrivial (Fin d)] :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).1 = true ↔
      ∃ xs, E.denote.Uncovered xs ∧ ¬ NonliveBorderRank.Live (FiniteCapFrontEnd.G E).automaton xs := by
  obtain ⟨seed⟩ := (inferInstance : Nonempty (Fin d))
  have hb := FiniteSOARankDecision.rankBound_of_nonlive (FiniteCapFrontEnd.G E)
    (FiniteCapTerminal.residual (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E))
    (FiniteCapFrontEnd.prepared E).rows (Empty.elim : Empty → Fin d)
    (FiniteCapFrontEnd.G_prefixClosed E)
    (fun body h => ((FiniteCapTerminal.residual_correct _ _ body).mp h).1)
  simp only [decide, problem_value, rank_value]
  rw [StoredRankAdapter.decide_correct _ _ _ hb,
    FiniteSOARankDecision.avoid_iff _ _ Empty.elim seed]
  apply exists_congr
  intro xs
  change ((FiniteCapTerminal.residual (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E)).automaton.Accepts xs ∧
    ¬ (FiniteSOARankDecision.toSOA (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.prepared E).rows).RootCov xs) ↔ _
  rw [FiniteCapTerminal.residual_correct,
    NonliveBorderRank.nonliveDFA_accepts_iff _ (FiniteCapFrontEnd.G_prefixClosed E),
    FiniteCapFrontEnd.uncovered_iff]
  tauto

/-- The stored seed row has one extra state. -/
theorem input_candidate_count (C : StoredOrdinaryDFABuild.Data) (rs : List StoredNormalizationRows.Row) :
    (StoredRankInput.build (d := d) C rs).1.candidate.count = C.count+1 := rfl

/-- Each cap row has the two DFA state sets and three extra states. -/
theorem input_rows_bound (C : StoredOrdinaryDFABuild.Data) (rs : List StoredNormalizationRows.Row)
    (N : Nat) (hn : ∀ r ∈ rs, r.left.count+r.right.count+3 ≤ N) :
    ∀ A ∈ (StoredRankInput.build (d := d) C rs).1.rows, A.count ≤ N := by
  intro A hA
  change A ∈ (StoredRankInput.collect (d := d) rs).1 at hA
  rw [StoredRankInput.collect, CountedListConstruction.map_value] at hA
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hA
  change (StoredCapRowNFABuild.dimension r.left.count r.right.count).1 ≤ N
  rw [StoredCapRowNFABuild.dimension_value]
  exact hn r hr

/-- Composition with the actual front-end counter. Dimensions of the
constructed rows and rank are still explicit here, rather than term size. -/
theorem bound (E : FiniteCapFrontEnd.Input (Fin d)) (N M : Nat)
    (hn : ∀ r ∈ (FiniteCapFrontEnd.prepared E).rows, r.left.count+r.right.count+3 ≤ N)
    (hk : (FiniteCapFrontEnd.prepared E).rows.length ≤ M) (hNM : N ≤ M)
    (hc : (FiniteCapFrontEnd.G E).count*(FiniteCapFrontEnd.R E).count+1 ≤ M)
    (h3 : 3 ≤ M) (hh : (FiniteCapFrontEnd.G E).count-2+1 ≤ M) :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      1+StoredTerminalInput.fromCapBudget E+
        DirectRankStateTower.tower 4
          (StoredRankDecisionTower.argument M ((FiniteCapFrontEnd.G E).count-2)+2*d+70) := by
  have hf := StoredTerminalInput.fromCap_bound E
  have hi := input_rows_bound (d := d)
    (StoredOrdinaryDFABuild.snapshot (FiniteCapTerminal.residual (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E)))
    ((FiniteCapFrontEnd.prepared E).rows.map StoredNormalizationRows.snapshot) N (by
      intro r hr
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hr
      exact hn a ha)
  have hk' : (StoredRankAdapter.inputOf (FiniteCapTerminal.residual (FiniteCapFrontEnd.G E)
      (FiniteCapFrontEnd.R E)) (FiniteCapFrontEnd.prepared E).rows).rows.length ≤ M := by
    rw [StoredRankAdapter.inputOf, StoredRankInput.rows_length, List.length_map]
    exact hk
  have hc' : (StoredRankAdapter.inputOf (FiniteCapTerminal.residual (FiniteCapFrontEnd.G E)
      (FiniteCapFrontEnd.R E)) (FiniteCapFrontEnd.prepared E).rows).candidate.count ≤ M := by
    rw [StoredRankAdapter.inputOf, input_candidate_count]
    exact hc
  have he := StoredRankDecisionTower.decide_tower (d := d) _ N M _ hi hk' hNM hc' h3 hh
  simp only [decide]
  rw [problem_value, rank_value]
  simp only [StoredRankAdapter.inputOf] at he ⊢
  omega

/-- A polynomial dominating every dimension needed by the rank engine. -/
def dimension (E : FiniteCapFrontEnd.Input (Fin d)) :=
  let T := ExplicitCapTerminal.size (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E)
    (FiniteCapFrontEnd.prepared E).rows
  T^2+T+3

/-- No externally supplied rank or dimension bound: all parameters are read
from the constructed automata of this cap input. -/
theorem bound_from_counts (E : FiniteCapFrontEnd.Input (Fin d)) :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      1+StoredTerminalInput.fromCapBudget E+
        DirectRankStateTower.tower 4
          (StoredRankDecisionTower.argument (dimension E) ((FiniteCapFrontEnd.G E).count-2)+2*d+70) := by
  let T := ExplicitCapTerminal.size (FiniteCapFrontEnd.G E) (FiniteCapFrontEnd.R E)
    (FiniteCapFrontEnd.prepared E).rows
  have hg : (FiniteCapFrontEnd.G E).count ≤ T := by dsimp [T, ExplicitCapTerminal.size]; omega
  have hr : (FiniteCapFrontEnd.R E).count ≤ T := by dsimp [T, ExplicitCapTerminal.size]; omega
  have hk : (FiniteCapFrontEnd.prepared E).rows.length ≤ T := by dsimp [T, ExplicitCapTerminal.size]; omega
  have hn : ∀ r ∈ (FiniteCapFrontEnd.prepared E).rows, r.left.count+r.right.count+3 ≤ T+3 := by
    intro r hmem
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hmem
    have h := ComputedScalarLoweringBudget.summand_le
      (fun j : Fin (FiniteCapFrontEnd.prepared E).rows.length =>
        (((FiniteCapFrontEnd.prepared E).rows.get j).left.count+
        ((FiniteCapFrontEnd.prepared E).rows.get j).right.count)) i
    dsimp [T, ExplicitCapTerminal.size]
    simp only [List.get_eq_getElem] at h ⊢
    omega
  have hm : dimension E = T^2+T+3 := rfl
  apply bound E (T+3) (dimension E) hn
  · rw [hm]; omega
  · rw [hm]; omega
  · have hp := Nat.mul_le_mul hg hr
    rw [hm]; nlinarith
  · rw [hm]; omega
  · rw [hm]; omega

end NSSE.StoredTerminalDecision
