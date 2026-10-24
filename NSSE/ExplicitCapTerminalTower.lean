import NSSE.ExplicitCapFrontEndSize

/-! Original cap state-count size to the five-level terminal counter bound.
This remains the structural evaluator metric, not total construction/runtime. -/

namespace NSSE.ExplicitCapTerminalTower

open FiniteSOARankDecision FiniteCapFrontEnd ExplicitCapFrontEndSize
open DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope

variable {d : Nat}

def size (E : Input (Fin d)) : Nat :=
  (E.routes.map (fun A => A.count+1)).sum+
  (E.rows.map (fun c => 2*c.left.count+c.right.count)).sum+E.rows.length+1

theorem sum_get {α : Type*} (as : List α) (f : α → Nat) :
    (∑ i : Fin as.length, f (as.get i)) = (as.map f).sum := by
  induction as with
  | nil => simp
  | cons a as ih => simp [Fin.sum_univ_succ, ih]

theorem row_sum_le (rows : List (Component (Fin d))) :
    (rows.map (fun c => c.left.count+c.right.count)).sum ≤
      (rows.map (fun c => 2*c.left.count+c.right.count)).sum := by
  induction rows with
  | nil => simp
  | cons c rows ih => simp only [List.map_cons, List.sum_cons]; omega

theorem terminal_size_exp (E : Input (Fin d)) :
    ExplicitCapTerminal.size (G E) (R E) (prepared E).rows ≤ 2^(3*size E+2) := by
  have hg := (G_count E).trans (exp_mono (show (E.routes.map (fun A => A.count+1)).sum ≤ size E by unfold size; omega))
  have hr := (R_count E).trans (exp_mono (show (E.rows.map (fun c => 2*c.left.count+c.right.count)).sum ≤ size E by unfold size; omega))
  have hp := filter_sum_le E.rows (fun c => FiniteDFAOperations.nonempty c.right)
    (fun c => c.left.count+c.right.count)
  have hq := row_sum_le E.rows
  have hl : (prepared E).rows.length ≤ E.rows.length := List.length_filter_le _ _
  have hs : (prepared E).rows.length+
      (∑ i : Fin (prepared E).rows.length,
        (((prepared E).rows.get i).left.count+((prepared E).rows.get i).right.count))+1 ≤ size E := by
    rw [sum_get (prepared E).rows (fun c => c.left.count+c.right.count)]
    change ((E.rows.filter (fun c => FiniteDFAOperations.nonempty c.right)).map
      (fun c => c.left.count+c.right.count)).sum ≤ _ at hp
    dsimp only [prepared] at hl ⊢
    unfold size
    omega
  have hrest := hs.trans (self_le_exp (size E))
  have hh := add_exp (add_exp hg hr) hrest
  rw [show size E+size E+1+size E+1 = 3*size E+2 by omega] at hh
  simpa only [ExplicitCapTerminal.size, Nat.add_assoc] using hh

theorem eval_exp_linear (e : Expr) (v : Fin 4 → Nat) (x : Nat) (hx : 1 ≤ x) (hv : ∀ i, v i ≤ 2^x) :
    eval v e ≤ 2^(weight e*x) := by
  induction e with
  | const n =>
    exact (self_le_exp n).trans (exp_mono (by change n ≤ (n+1)*x; nlinarith))
  | var i => simpa only [eval, weight, Nat.one_mul] using hv i
  | add a b iha ihb =>
    apply (add_exp iha ihb).trans
    apply exp_mono
    change weight a*x+weight b*x+1 ≤ (weight a+weight b+1)*x
    nlinarith
  | mul a b iha ihb =>
    apply (mul_exp iha ihb).trans
    apply exp_mono
    change weight a*x+weight b*x ≤ (weight a+weight b)*x
    nlinarith
  | max a b iha ihb =>
    apply max_le
    · apply iha.trans
      apply exp_mono
      change weight a*x ≤ (weight a+weight b)*x
      exact Nat.mul_le_mul_right _ (by omega)
    · apply ihb.trans
      apply exp_mono
      change weight b*x ≤ (weight a+weight b)*x
      exact Nat.mul_le_mul_right _ (by omega)
  | pow a n ih =>
    apply (pow_exp ih n).trans
    apply exp_mono
    change weight a*x*n ≤ (weight a*n+1)*x
    nlinarith

def exponentExpression : Expr :=
  let N : Expr := .var 0
  let D : Expr := .var 1
  let A := N^2+N+1
  let Q := (A+3)+3+(A+3)*6+(A+3)*(A+3)*9
  let B := (A+1)*Q+A+1
  8*N^2+4*B*N+23*N+7*B+2*D+3144

theorem exponent_eval (N d : Nat) :
    eval ![N,d,0,0] exponentExpression =
      8*N^2+4*ExplicitSOAInputBudget.budget (N^2+N+1)*N+23*N+
        7*ExplicitSOAInputBudget.budget (N^2+N+1)+2*d+3144 := rfl

theorem tower_exp (k x : Nat) : tower k (2^x) = tower (k+1) x := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun n => 2^n) ih

theorem terminalDecision_bound (E : Input (Fin d)) :
    (ExplicitCapTerminal.terminalDecision E).2 ≤
      tower 5 (weight exponentExpression*(3*size E+d+3)) := by
  let N := ExplicitCapTerminal.size (G E) (R E) (prepared E).rows
  have hn : N ≤ 2^(3*size E+d+3) :=
    (terminal_size_exp E).trans (exp_mono (by omega))
  have hd : d ≤ 2^(3*size E+d+3) := (self_le_exp d).trans (exp_mono (by omega))
  have hv : ∀ i : Fin 4, (![N,d,0,0] : Fin 4 → Nat) i ≤ 2^(3*size E+d+3) := by
    intro i
    fin_cases i
    · exact hn
    · exact hd
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  have hp := eval_exp_linear exponentExpression ![N,d,0,0] (3*size E+d+3) (by omega) hv
  rw [exponent_eval] at hp
  have ht := (ExplicitCapTerminal.terminalDecision_bound E).trans (tower_mono 4 hp)
  rw [tower_exp] at ht
  exact ht

theorem terminalDecision_explicit_bound (E : Input (Fin d)) :
    (ExplicitCapTerminal.terminalDecision E).2 ≤ tower 5 (3403*(3*size E+d+3)) :=
  terminalDecision_bound E

end NSSE.ExplicitCapTerminalTower
