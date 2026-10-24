import NSSE.StoredTerminalDecision
import NSSE.StoredUnionBudget

/-! Cap-input size controls the actual stored rank engine and both union
folds in its front end. The other front-end counters remain explicit. -/
namespace NSSE.StoredCapDimensionTower
open DirectRankStateTower DirectRankFormulaTower
open FiniteCapFrontEnd ExplicitCapTerminalTower
variable {d : Nat}

theorem length_le_sum_succ {α : Type} (xs : List α) (f : α → Nat) :
    xs.length ≤ (xs.map (fun a => f a+1)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; omega

theorem route_length_le (E : Input (Fin d)) : E.routes.length ≤ size E := by
  have h := length_le_sum_succ E.routes (fun a => a.count)
  unfold size
  omega

theorem row_length_le (E : Input (Fin d)) : (prepared E).rows.length ≤ size E := by
  have h : (prepared E).rows.length ≤ E.rows.length := List.length_filter_le _ _
  unfold size
  omega

/-- Cost of the union fold in the actual route-free construction. -/
theorem route_union_exp (E : Input (Fin d)) :
    StoredDFAUnions.budget d (E.routes.map (fun a => 2^(a.count+1))) ≤
      2^(PolynomialTowerEnvelope.weight StoredUnionBudget.expression*(2*size E+d+1)) := by
  apply StoredUnionBudget.budget_exp d _ (2*size E+d+1) (by omega)
  · have h := StoredUnionBudget.safeProduct_exp E.routes
      (fun a => 2^(a.count+1)) (fun a => a.count+1) (fun _ _ => le_rfl)
    apply h.trans (exp_mono ?_)
    have hl := route_length_le E
    unfold size at *
    omega
  · exact (self_le_exp d).trans (exp_mono (by omega))
  · rw [List.length_map]
    exact (route_length_le E).trans ((self_le_exp (size E)).trans (exp_mono (by omega)))

/-- Cost of the union fold in the actual cap-regular construction. -/
theorem regular_union_exp (E : Input (Fin d)) :
    StoredDFAUnions.budget d ((StoredCapRegular.sizes (prepared E).rows).map
      (fun nm => nm.1*2^(nm.1+nm.2))) ≤
      2^(PolynomialTowerEnvelope.weight StoredUnionBudget.expression*(2*size E+d+1)) := by
  simp only [StoredCapRegular.sizes,List.map_map,Function.comp_def]
  apply StoredUnionBudget.budget_exp d _ (2*size E+d+1) (by omega)
  · have h := StoredUnionBudget.safeProduct_exp (prepared E).rows
      (fun a => a.left.count*2^(a.left.count+a.right.count))
      (fun a => 2*a.left.count+a.right.count) (fun a _ => by
        have h := mul_exp (self_le_exp a.left.count) (le_rfl : 2^(a.left.count+a.right.count) ≤ _)
        have he : a.left.count+(a.left.count+a.right.count) = 2*a.left.count+a.right.count := by omega
        rw [he] at h
        exact h)
    apply h.trans (exp_mono ?_)
    have hf := ExplicitCapFrontEndSize.filter_sum_le E.rows
      (fun c => FiniteDFAOperations.nonempty c.right) (fun c => 2*c.left.count+c.right.count)
    have hl := row_length_le E
    change ((prepared E).rows.map _).sum ≤ _ at hf
    unfold size at *
    omega
  · exact (self_le_exp d).trans (exp_mono (by omega))
  · rw [List.length_map]
    exact (row_length_le E).trans ((self_le_exp (size E)).trans (exp_mono (by omega)))

/-- Polynomial expression after the generated dimension T^2+T+3 is substituted. -/
def rankExpression : PolynomialTowerEnvelope.Expr :=
  let t : PolynomialTowerEnvelope.Expr := .var 0
  let d : PolynomialTowerEnvelope.Expr := .var 1
  let m := t^2+t+3
  48*m^2+71*m+3664*t+62830+2*d+70

theorem rankExpression_value (T d : Nat) :
    PolynomialTowerEnvelope.eval ![T,d,0,0] rankExpression =
      StoredRankDecisionTower.argument (T^2+T+3) T+2*d+70 := by
  rw [StoredRankDecisionTower.argument_polynomial]
  rfl

theorem rank_argument_exp (E : Input (Fin d)) :
    StoredRankDecisionTower.argument (StoredTerminalDecision.dimension E) ((G E).count-2)+2*d+70 ≤
      2^(PolynomialTowerEnvelope.weight rankExpression*(3*size E+d+3)) := by
  let T := ExplicitCapTerminal.size (G E) (R E) (prepared E).rows
  have ht : T ≤ 2^(3*size E+d+3) := (terminal_size_exp E).trans (exp_mono (by omega))
  have hd : d ≤ 2^(3*size E+d+3) := (self_le_exp d).trans (exp_mono (by omega))
  have h := eval_exp_linear rankExpression ![T,d,0,0] (3*size E+d+3) (by omega) (by
    intro i; fin_cases i
    · exact ht
    · exact hd
    all_goals exact Nat.zero_le _)
  rw [rankExpression_value] at h
  have hh : (G E).count-2 ≤ T := by dsimp [T,ExplicitCapTerminal.size]; omega
  apply le_trans ?_ h
  rw [StoredRankDecisionTower.argument_polynomial,StoredRankDecisionTower.argument_polynomial]
  change 48*(T^2+T+3)^2+71*(T^2+T+3)+3664*((G E).count-2)+62830+2*d+70 ≤ _
  omega

/-- The actual rank/closing counter contributes five exponentials in original
cap size. The counted front end remains a separate explicit term here. -/
theorem terminal_bound (E : Input (Fin d)) :
    (StoredTerminalDecision.decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      1+StoredTerminalInput.fromCapBudget E+
        tower 5 (PolynomialTowerEnvelope.weight rankExpression*(3*size E+d+3)) := by
  have h := StoredTerminalDecision.bound_from_counts E
  have ht := tower_mono 4 (rank_argument_exp E)
  rw [tower_exp] at ht
  norm_num only at ht
  omega

theorem terminal_explicit_bound (E : Input (Fin d)) :
    (StoredTerminalDecision.decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      1+StoredTerminalInput.fromCapBudget E+tower 5 (66729*(3*size E+d+3)) := by
  have hw : PolynomialTowerEnvelope.weight rankExpression = 66729 := by decide
  simpa only [hw] using terminal_bound E

end NSSE.StoredCapDimensionTower
