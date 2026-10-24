import NSSE.StoredFrontBudgetExpressions

/-! Absorb every counted cap-front-end operation in a single exponential
of original cap size, and combine it with the actual terminal decision. -/
namespace NSSE.StoredCapFrontBudget
open DirectRankStateTower DirectRankFormulaTower
open FiniteCapFrontEnd ExplicitCapTerminalTower PolynomialTowerEnvelope
open StoredFrontBudgetExpressions
variable {d : Nat}

def coefficient := 1000+weight preparation+weight component+weight residual+weight capRow+weight seedRow
def exponent (E : Input (Fin d)) := 3*size E+d+3

theorem exponent_pos (E : Input (Fin d)) : 1 ≤ exponent E := by unfold exponent; omega

theorem scalar_bound (e : Expr) (he : weight e ≤ coefficient) (v : Fin 4 → Nat)
    (E : Input (Fin d)) (hv : ∀ i, v i ≤ 2^(exponent E)) :
    eval v e ≤ 2^(coefficient*exponent E) :=
  (eval_exp_linear e v (exponent E) (exponent_pos E) hv).trans
    (exp_mono (Nat.mul_le_mul_right _ he))

theorem size_exp (E : Input (Fin d)) : size E ≤ 2^(exponent E) :=
  (self_le_exp _).trans (exp_mono (by unfold exponent; omega))
theorem alphabet_exp (E : Input (Fin d)) : d ≤ 2^(exponent E) :=
  (self_le_exp _).trans (exp_mono (by unfold exponent; omega))
theorem input_rows_exp (E : Input (Fin d)) : E.rows.length ≤ 2^(exponent E) :=
  (show E.rows.length ≤ size E by unfold size; omega).trans (size_exp E)

theorem row_size (E : Input (Fin d)) (r : FiniteSOARankDecision.Component (Fin d))
    (hr : r ∈ (prepared E).rows) : r.left.count+r.right.count ≤ size E := by
  have hm : r ∈ E.rows := (List.mem_filter.mp hr).1
  have h := StoredQuerySize.sum_member (fun a => 2*a.left.count+a.right.count) E.rows r hm
  dsimp only at h
  unfold size
  omega

theorem preparation_exp (E : Input (Fin d)) :
    StoredCapPreparation.budget (size E) d E.rows.length ≤ 2^(coefficient*exponent E) := by
  have h := scalar_bound preparation (by unfold coefficient; omega) ![size E,E.rows.length,d,0] E (by
    intro i; fin_cases i
    · exact size_exp E
    · exact input_rows_exp E
    · exact alphabet_exp E
    · exact Nat.zero_le _)
  rwa [preparation_value] at h

theorem component_exp (E : Input (Fin d)) (r : FiniteSOARankDecision.Component (Fin d))
    (hr : r ∈ (prepared E).rows) :
    StoredComponentRegular.budget r.left.count r.right.count d ≤ 2^(coefficient*exponent E) := by
  have hs := row_size E r hr
  have h := scalar_bound component (by unfold coefficient; omega)
    ![r.left.count,r.right.count,d,2^(r.left.count+r.right.count)] E (by
      intro i; fin_cases i
      · exact (show r.left.count ≤ size E by omega).trans (size_exp E)
      · exact (show r.right.count ≤ size E by omega).trans (size_exp E)
      · exact alphabet_exp E
      · exact exp_mono (by unfold exponent; omega))
  rwa [component_value] at h

theorem capRow_exp (E : Input (Fin d)) (r : FiniteSOARankDecision.Component (Fin d))
    (hr : r ∈ (prepared E).rows) :
    StoredOriginalRows.capBudget r.left.count r.right.count d ≤ 2^(coefficient*exponent E) := by
  have hs := row_size E r hr
  have h := scalar_bound capRow (by unfold coefficient; omega) ![r.left.count,r.right.count,d,0] E (by
    intro i; fin_cases i
    · exact (show r.left.count ≤ size E by omega).trans (size_exp E)
    · exact (show r.right.count ≤ size E by omega).trans (size_exp E)
    · exact alphabet_exp E
    · exact Nat.zero_le _)
  rwa [capRow_value] at h

theorem G_exp (E : Input (Fin d)) : (G E).count ≤ 2^(size E) :=
  (ExplicitCapFrontEndSize.G_count E).trans (exp_mono (by unfold size; omega))
theorem R_exp (E : Input (Fin d)) : (R E).count ≤ 2^(size E) :=
  (ExplicitCapFrontEndSize.R_count E).trans (exp_mono (by unfold size; omega))

theorem residual_exp (E : Input (Fin d)) :
    StoredResidualDFA.budget (G E).count (R E).count d ≤ 2^(coefficient*exponent E) := by
  have h := scalar_bound residual (by unfold coefficient; omega) ![(G E).count,(R E).count,d,0] E (by
    intro i; fin_cases i
    · exact (G_exp E).trans (exp_mono (by unfold exponent; omega))
    · exact (R_exp E).trans (exp_mono (by unfold exponent; omega))
    · exact alphabet_exp E
    · exact Nat.zero_le _)
  rwa [residual_value] at h

theorem seedRow_exp (E : Input (Fin d)) :
    StoredOriginalRows.seedBudget ((G E).count*(R E).count) d ≤ 2^(coefficient*exponent E) := by
  have h := scalar_bound seedRow (by unfold coefficient; omega) ![(G E).count*(R E).count,0,d,0] E (by
    intro i; fin_cases i
    · exact (mul_exp (G_exp E) (R_exp E)).trans (exp_mono (by unfold exponent; omega))
    · exact Nat.zero_le _
    · exact alphabet_exp E
    · exact Nat.zero_le _)
  rwa [seedRow_value] at h

/-- Collection adds only a linear term to the exponent coefficient. -/
theorem collection_exp {α : Type} (xs : List α) (f : α → Nat) (c x : Nat) (hx : 1 ≤ x)
    (hl : xs.length ≤ 2^x) (hf : ∀ a ∈ xs, f a ≤ 2^(c*x)) :
    1+(xs.map (fun a => 1+f a)).sum ≤ 2^((c+5)*x) := by
  have hb (a : α) (ha : a ∈ xs) : 1+f a ≤ 2^(c*x+2) := by
    have h := add_exp (self_le_exp 1) (hf a ha)
    have he : 1+c*x+1 = c*x+2 := by omega
    rwa [he] at h
  have hs := StoredRouteBudget.sum_map_bound xs _ _ hb
  have hm := mul_exp hl (le_rfl : 2^(c*x+2) ≤ _)
  have h := add_exp (self_le_exp 1) (hs.trans hm)
  exact h.trans (exp_mono (by nlinarith))

theorem regular_collect_exp (E : Input (Fin d)) :
    StoredCapRegular.rowBudget d (StoredCapRegular.sizes (prepared E).rows) ≤
      2^((coefficient+5)*exponent E) := by
  have h := collection_exp (prepared E).rows
    (fun r => StoredComponentRegular.budget r.left.count r.right.count d) coefficient (exponent E)
    (exponent_pos E) ((StoredCapDimensionTower.row_length_le E).trans (size_exp E)) (component_exp E)
  simpa only [StoredCapRegular.rowBudget,StoredCapRegular.sizes,List.map_map,Function.comp_def] using h

theorem rank_collect_exp (E : Input (Fin d)) :
    StoredRankInput.collectBudget d ((prepared E).rows.map StoredNormalizationRows.snapshot) ≤
      2^((coefficient+5)*exponent E) := by
  have h := collection_exp (prepared E).rows
    (fun r => StoredOriginalRows.capBudget r.left.count r.right.count d) coefficient (exponent E)
    (exponent_pos E) ((StoredCapDimensionTower.row_length_le E).trans (size_exp E)) (capRow_exp E)
  simpa only [StoredRankInput.collectBudget,List.map_map,Function.comp_def,StoredNormalizationRows.snapshot,
    StoredOrdinaryDFABuild.snapshot] using h

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- All preprocessing counters, including their composition overhead. -/
theorem fromCapBudget_exp (E : Input (Fin d)) :
    StoredTerminalInput.fromCapBudget E ≤ 2^((coefficient+9)*exponent E) := by
  let Q := 2^((coefficient+5)*exponent E)
  have lift (a : Nat) (h : a ≤ 2^(coefficient*exponent E)) : a ≤ Q :=
    h.trans (exp_mono (by nlinarith))
  have hp := lift _ (preparation_exp E)
  have hr := lift _ (residual_exp E)
  have hs := lift _ (seedRow_exp E)
  have hc := regular_collect_exp E
  have hk := rank_collect_exp E
  have hroute : StoredCapRouteFree.budget d (E.routes.map FiniteSOARankDecision.InputDFA.count) ≤ Q := by
    have h := StoredRouteBudget.budget_exp E
    have hw : StoredRouteBudget.coefficient = 804 := by decide
    rw [hw] at h
    apply h.trans (exp_mono ?_)
    have hw' : 804 ≤ coefficient+5 := by unfold coefficient; omega
    have hx : 2*size E+d+1 ≤ exponent E := by unfold exponent; omega
    exact Nat.mul_le_mul hw' hx
  have hu : StoredDFAUnions.budget d ((StoredCapRegular.sizes (prepared E).rows).map
      (fun nm => nm.1*2^(nm.1+nm.2))) ≤ Q := by
    have h := StoredCapDimensionTower.regular_union_exp E
    have hw : weight StoredUnionBudget.expression = 208 := by decide
    rw [hw] at h
    apply h.trans (exp_mono ?_)
    have hw' : 208 ≤ coefficient+5 := by unfold coefficient; omega
    exact Nat.mul_le_mul hw' (by unfold exponent; omega)
  have hQ : 14 ≤ Q := by
    have he : 4 ≤ (coefficient+5)*exponent E := by
      have hx := exponent_pos E
      have hc : 4 ≤ coefficient+5 := by unfold coefficient; omega
      nlinarith
    exact (show 14 ≤ 2^4 by decide).trans (exp_mono he)
  have hsum : StoredTerminalInput.fromCapBudget E ≤ 16*Q := by
    unfold StoredTerminalInput.fromCapBudget StoredCapFrontEnd.budget StoredCapRegular.budget
      StoredTerminalInput.budget StoredRankInput.budget
    change StoredCapRegular.rowBudget d (StoredCapRegular.sizes (prepared E).rows) ≤ Q at hc
    change StoredRankInput.collectBudget d ((prepared E).rows.map StoredNormalizationRows.snapshot) ≤ Q at hk
    omega
  apply hsum.trans
  simp only [Q]
  rw [show (16 : Nat) = 2^4 by decide, ← pow_add]
  apply exp_mono
  have hx := exponent_pos E
  nlinarith

/-- The actual counted front end, with every intermediate stage included. -/
theorem fromCap_bound (E : Input (Fin d)) :
    (StoredTerminalInput.fromCap (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      2^((coefficient+9)*exponent E) :=
  (StoredTerminalInput.fromCap_bound E).trans (fromCapBudget_exp E)

/-- Total counted cap-terminal decision in five exponentials of original
cap size: no residual budget or externally supplied dimension bound. -/
theorem terminal_bound (E : Input (Fin d)) :
    (StoredTerminalDecision.decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      tower 5 ((coefficient+66742)*exponent E) := by
  let z := (coefficient+66740)*exponent E
  have hs := StoredCapDimensionTower.terminal_explicit_bound E
  have hf := fromCapBudget_exp E
  have ht : StoredTerminalInput.fromCapBudget E ≤ tower 5 z := by
    have h := hf.trans (TowerExpression.height_mono 1 5 ((coefficient+9)*exponent E) (by decide))
    exact h.trans (tower_mono 5 (by dsimp [z]; nlinarith))
  have hr : tower 5 (66729*(3*size E+d+3)) ≤ tower 5 z := by
    apply tower_mono 5
    change 66729*exponent E ≤ (coefficient+66740)*exponent E
    nlinarith
  have hp : 1 ≤ tower 5 z := by change 1 ≤ 2^_; exact Nat.one_le_pow _ _ (by decide)
  have h1 := TowerExpression.double_step 4 z
  have h2 := TowerExpression.double_step 4 (z+1)
  change 2*tower 5 z ≤ tower 5 (z+1) at h1
  change 2*tower 5 (z+1) ≤ tower 5 (z+1+1) at h2
  have hm : tower 5 (z+1+1) ≤ tower 5 ((coefficient+66742)*exponent E) := by
    apply tower_mono 5
    have hx := exponent_pos E
    dsimp [z]
    nlinarith
  omega

theorem fromCap_explicit (E : Input (Fin d)) :
    (StoredTerminalInput.fromCap (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      2^(3892*(3*size E+d+3)) := by
  have hc : coefficient+9 = 3892 := by decide
  simpa only [hc,exponent] using fromCap_bound E

theorem terminal_explicit (E : Input (Fin d)) :
    (StoredTerminalDecision.decide (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      tower 5 (70625*(3*size E+d+3)) := by
  have hc : coefficient+66742 = 70625 := by decide
  simpa only [hc,exponent] using terminal_bound E

end NSSE.StoredCapFrontBudget
