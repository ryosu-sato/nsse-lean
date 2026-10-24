import NSSE.StoredCapDimensionTower

/-! Single-exponential envelopes for the complete route-free front end,
including right-ideal determinization, the union fold and complement. -/
namespace NSSE.StoredRouteBudget
open DirectRankStateTower DirectRankFormulaTower
open FiniteCapFrontEnd ExplicitCapTerminalTower
variable {d : Nat}

/-- The exact scalar budget with the subset count supplied as variable 2. -/
def expression : PolynomialTowerEnvelope.Expr :=
  let n : PolynomialTowerEnvelope.Expr := .var 0
  let d : PolynomialTowerEnvelope.Expr := .var 1
  let p : PolynomialTowerEnvelope.Expr := .var 2
  let t := n+1
  let tab := fun k b => 2+(k+1)^2+k*(1+b)
  let dec := 7+(n+1)^2+4*n
  let nfa := 2+tab (n+1) (3+dec+n)+
    tab (n+1) (tab d (tab (n+1) (4+2*dec+2*n+d)))+tab (n+1) (2+dec+n)
  let idx := 2+10*p+p*(2*t+3)
  let ini := 1+tab t t+idx
  let step := 4+11*p+tab t (tab t (3*t+d+3))+idx
  let acc := 3+11*p+tab t (2*t+1)
  let det := 1+(p+2*t)+ini+tab p (tab d step)+tab p acc
  n+2+(1+nfa+det)

theorem expression_value (n d : Nat) :
    PolynomialTowerEnvelope.eval ![n,d,2^(n+1),0] expression = StoredRouteIdeal.budget n d := rfl

theorem scalar_exp (n d x : Nat) (hn : n+1 ≤ x) (hd : d ≤ x) :
    StoredRouteIdeal.budget n d ≤ 2^(PolynomialTowerEnvelope.weight expression*x) := by
  have h := eval_exp_linear expression ![n,d,2^(n+1),0] x (by omega) (by
    intro i; fin_cases i
    · exact (self_le_exp n).trans (exp_mono (by omega))
    · exact (self_le_exp d).trans (exp_mono hd)
    · exact exp_mono hn
    · exact Nat.zero_le _)
  rw [expression_value] at h
  exact h

theorem sum_map_bound {α : Type} (xs : List α) (f : α → Nat) (b : Nat)
    (h : ∀ a ∈ xs, f a ≤ b) : (xs.map f).sum ≤ xs.length*b := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun c hc => h c (by simp [hc]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

theorem member_count (E : Input (Fin d)) (a : FiniteSOARankDecision.InputDFA (Fin d))
    (ha : a ∈ E.routes) : a.count+1 ≤ size E := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp ha
  have h := ComputedScalarLoweringBudget.summand_le
    (fun j : Fin E.routes.length => (E.routes.get j).count+1) i
  rw [sum_get E.routes (fun a => a.count+1)] at h
  unfold size
  omega

/-- Explicit exponent coefficient for the complete route-free construction. -/
def coefficient := PolynomialTowerEnvelope.weight expression+
  PolynomialTowerEnvelope.weight StoredUnionBudget.expression+40

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem collect_exp (E : Input (Fin d)) :
    StoredCapRouteFree.collectBudget d (E.routes.map FiniteSOARankDecision.InputDFA.count) ≤
      2^((PolynomialTowerEnvelope.weight expression+5)*(2*size E+d+1)) := by
  let x := 2*size E+d+1
  let w := PolynomialTowerEnvelope.weight expression
  have hx : 1 ≤ x := by dsimp [x]; omega
  have hb (a : FiniteSOARankDecision.InputDFA (Fin d)) (ha : a ∈ E.routes) :
      1+StoredRouteIdeal.budget a.count d ≤ 2^(w*x+2) := by
    have h := scalar_exp a.count d x ((member_count E a ha).trans (by dsimp [x]; omega)) (by dsimp [x]; omega)
    have hh := add_exp (self_le_exp 1) h
    have he : 1+(PolynomialTowerEnvelope.weight expression*x)+1 = w*x+2 := by
      change 1+w*x+1 = w*x+2
      omega
    rw [he] at hh
    exact hh
  have hs := sum_map_bound E.routes (fun a => 1+StoredRouteIdeal.budget a.count d) (2^(w*x+2)) hb
  have hl : E.routes.length ≤ 2^x := (StoredCapDimensionTower.route_length_le E).trans
    ((self_le_exp (size E)).trans (exp_mono (by dsimp [x]; omega)))
  have hm := mul_exp hl (le_rfl : 2^(w*x+2) ≤ _)
  have hh := add_exp (self_le_exp 1) (hs.trans hm)
  have he : 1+(x+(w*x+2))+1 ≤ (w+5)*x := by nlinarith
  have hfinal := hh.trans (exp_mono he)
  simpa only [StoredCapRouteFree.collectBudget,List.map_map,Function.comp_def] using hfinal

theorem complement_exp (E : Input (Fin d)) :
    StoredDFAComplement.budget ((E.routes.map (fun a => 2^(a.count+1))).prod) ≤
      2^(30*(2*size E+d+1)) := by
  let x := 2*size E+d+1
  let P := (E.routes.map (fun a => 2^(a.count+1))).prod
  have hp : P ≤ 2^x := by
    dsimp only [P]
    rw [← StoredCapRouteFree.original_count]
    exact (ExplicitCapFrontEndSize.G_count E).trans (exp_mono (by dsimp [x]; unfold size; omega))
  let e : PolynomialTowerEnvelope.Expr := 1+(2+(.var 0+1)^2+.var 0*(.var 0+2))
  have hv : PolynomialTowerEnvelope.eval ![P,0,0,0] e = StoredDFAComplement.budget P := by
    simp only [e,PolynomialTowerEnvelope.eval,StoredDFAComplement.budget,StoredForwardTableBuild.tabBudget]
    simp only [Matrix.cons_val_zero]
    ring
  have h := eval_exp_linear e ![P,0,0,0] x (by dsimp [x]; omega) (by
    intro i; fin_cases i
    · exact hp
    all_goals exact Nat.zero_le _)
  have hw : PolynomialTowerEnvelope.weight e ≤ 30 := by decide
  rw [hv] at h
  exact h.trans (exp_mono (Nat.mul_le_mul_right x hw))

/-- Complete route-free preprocessing cost in original cap size. -/
theorem budget_exp (E : Input (Fin d)) :
    StoredCapRouteFree.budget d (E.routes.map FiniteSOARankDecision.InputDFA.count) ≤
      2^(coefficient*(2*size E+d+1)) := by
  have h1 := collect_exp E
  have h2 := StoredCapDimensionTower.route_union_exp E
  have h3 := complement_exp E
  have h := add_exp (add_exp (add_exp (self_le_exp 2) h1) h2) h3
  have he : 2+(PolynomialTowerEnvelope.weight expression+5)*(2*size E+d+1)+1+
      PolynomialTowerEnvelope.weight StoredUnionBudget.expression*(2*size E+d+1)+1+
      30*(2*size E+d+1)+1 ≤ coefficient*(2*size E+d+1) := by
    unfold coefficient
    nlinarith
  have hf := h.trans (exp_mono he)
  simpa only [StoredCapRouteFree.budget,List.map_map,Function.comp_def] using hf

/-- The actual route-free constructor, with the coefficient evaluated. -/
theorem build_explicit (E : Input (Fin d)) :
    (StoredCapRouteFree.build (d := d) (StoredNormalizationBuild.snapshot E)).2 ≤
      2^(804*(2*size E+d+1)) := by
  have h := (StoredCapRouteFree.bound E).trans (budget_exp E)
  have hc : coefficient = 804 := by decide
  simpa only [hc] using h

end NSSE.StoredRouteBudget
