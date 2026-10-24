import NSSE.StoredCapDecision
import NSSE.StoredCapPadding

/-! Complete counted cap decision for all finite alphabets. Padding is
actually constructed and charged before the live/terminal solver. -/
namespace NSSE.StoredPaddedCapDecision
open DirectRankStateTower DirectRankFormulaTower
variable {d : Nat}

def decide (E : StoredNormalizationBuild.Data) : Bool × Nat :=
  let p := StoredCapPadding.build (d := d) E
  let r := StoredCapDecision.decide (d := d+2) p.1
  (r.1,1+p.2+r.2)

theorem correct (E : FiniteCapFrontEnd.Input (Fin d)) :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).1=true ↔
      ∃ xs, E.denote.Uncovered xs := by
  haveI : Nontrivial (Fin (d+2)) := ⟨⟨0,1,by
    intro h
    have h' := congrArg (fun x : Fin (d+2) => x.val) h
    change 0=1 at h'
    omega⟩⟩
  simp only [decide,StoredCapPadding.value]
  exact (StoredCapDecision.correct (PaddedCapInput.pad E)).trans
    (PaddedCapInput.exists_uncovered_iff E)

theorem universal_correct (E : FiniteCapFrontEnd.Input (Fin d)) :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).1=false ↔ E.denote.Universal := by
  have hb : ∀ b : Bool, b=false ↔ ¬b=true := by decide
  rw [hb,correct]
  classical
  simp [CapExpression.Uncovered,CapExpression.Universal]

def paddingExpression : TowerExpression.Expr :=
  let s : TowerExpression.Expr := .var 0
  let d : TowerExpression.Expr := .var 1
  let tab := fun n b : TowerExpression.Expr => 2+(n+1)^2+n*(1+b)
  let f := 6+tab 2 (tab (d+2) (d+6))
  let p := 4+tab (s+1) (tab (d+2) (2*s+2*d+9))+tab (s+1) (2*s+3)
  4+f+s*(2+2*p)+s*(1+p)

theorem paddingExpression_value (s d : Nat) :
    TowerExpression.eval ![s,d,0] paddingExpression = StoredCapPadding.budget s d s s := rfl

theorem padding_bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    (StoredCapPadding.build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      tower 2 (ExplicitCapTerminalTower.size E+d+TowerExpression.weight paddingExpression) := by
  let s := ExplicitCapTerminalTower.size E
  have h := StoredCapPadding.bound_input (d := d) (StoredNormalizationBuild.snapshot E)
  rw [StoredCapPadding.size_snapshot] at h
  have hr : E.rows.length ≤ s := by dsimp [s,ExplicitCapTerminalTower.size]; omega
  have ht : E.routes.length ≤ s := by
    have h := PaddedCapInput.route_length_le E.routes
    dsimp [s,ExplicitCapTerminalTower.size]
    omega
  have hm : StoredCapPadding.budget s d E.rows.length E.routes.length ≤
      StoredCapPadding.budget s d s s := by unfold StoredCapPadding.budget; gcongr
  have he := TowerExpression.bound paddingExpression ![s,d,0] (s+d) (by
    intro i; fin_cases i <;> dsimp <;> omega)
  rw [paddingExpression_value,show TowerExpression.height paddingExpression=2 by decide] at he
  simp only [StoredNormalizationBuild.snapshot,List.length_map] at h
  exact h.trans (hm.trans he)

theorem bound (E : FiniteCapFrontEnd.Input (Fin d)) :
    (decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      tower 5 (70625*(15*ExplicitCapTerminalTower.size E+d+14)+4) := by
  let x := 70625*(15*ExplicitCapTerminalTower.size E+d+14)+2
  have hs := PaddedCapInput.size_bound E
  have hr := StoredCapDecision.bound (PaddedCapInput.pad E)
  have hr' : (StoredCapDecision.decide (d := d+2)
      (StoredNormalizationBuild.snapshot (PaddedCapInput.pad E))).2 ≤ tower 5 x :=
    hr.trans (tower_mono 5 (by dsimp [x]; omega))
  have hw : TowerExpression.weight paddingExpression ≤ 1000 := by decide
  have hp : (StoredCapPadding.build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤ tower 5 x :=
    (padding_bound E).trans ((TowerExpression.height_mono 2 5 _ (by decide)).trans
      (tower_mono 5 (by dsimp [x]; omega)))
  have ho : 1≤tower 5 x := Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 4 x
  have h2 := TowerExpression.double_step 4 (x+1)
  change 2*tower 5 x≤tower 5 (x+1) at h1
  change 2*tower 5 (x+1)≤tower 5 (x+2) at h2
  change 1+_+_ ≤ tower 5 (x+2)
  rw [StoredCapPadding.value]
  omega
end NSSE.StoredPaddedCapDecision
