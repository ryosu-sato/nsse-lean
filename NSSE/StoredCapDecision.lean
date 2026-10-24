import NSSE.StoredLiveDecisionBudget

/-! Actual complete live/terminal composition. Semantic correctness here
inherits the terminal solver's nontrivial-alphabet requirement. -/
namespace NSSE.StoredCapDecision
open DirectRankStateTower DirectRankFormulaTower
variable {d : Nat}

def decide (E : StoredNormalizationBuild.Data) : Bool × Nat :=
  let l := StoredLiveDecision.decide (d := d) E
  let t := StoredTerminalDecision.decide (d := d) E
  (l.1 || t.1,1+l.2+t.2)

theorem correct (E : FiniteCapFrontEnd.Input (Fin d)) [Nontrivial (Fin d)] :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).1=true ↔ ∃ xs, E.denote.Uncovered xs := by
  simp only [decide,Bool.or_eq_true,StoredLiveDecision.correct,StoredTerminalDecision.correct]
  classical
  constructor
  · rintro (⟨xs,h,_⟩ | ⟨xs,h,_⟩) <;> exact ⟨xs,h⟩
  · rintro ⟨xs,h⟩
    by_cases hl : NonliveBorderRank.Live (FiniteCapFrontEnd.G E).automaton xs
    · exact Or.inl ⟨xs,h,hl⟩
    · exact Or.inr ⟨xs,h,hl⟩

theorem universal_correct (E : FiniteCapFrontEnd.Input (Fin d)) [Nontrivial (Fin d)] :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).1=false ↔ E.denote.Universal := by
  have hb : ∀ b : Bool, b=false ↔ ¬b=true := by decide
  rw [hb,correct]
  classical
  simp [CapExpression.Uncovered,CapExpression.Universal]

theorem bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      tower 5 (70625*(3*ExplicitCapTerminalTower.size E+d+3)+2) := by
  let x := 70625*(3*ExplicitCapTerminalTower.size E+d+3)
  have hl := StoredLiveDecisionBudget.bound_explicit E
  have hl' : (StoredLiveDecision.decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤ tower 5 x :=
    hl.trans ((tower_mono 3 (by dsimp [x]; omega)).trans (TowerExpression.height_mono 3 5 x (by decide)))
  have ht := StoredCapFrontBudget.terminal_explicit E
  have hp : 1≤tower 5 x := Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 4 x
  have h2 := TowerExpression.double_step 4 (x+1)
  change 2*tower 5 x≤tower 5 (x+1) at h1
  change 2*tower 5 (x+1)≤tower 5 (x+2) at h2
  change 1+_+_ ≤ tower 5 (x+2)
  change _ ≤ tower 5 x at ht
  omega
end NSSE.StoredCapDecision
