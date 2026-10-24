import NSSE.ExistentialRowNonemptySize

/-! # Actual recursive formula growth with an explicit cubic step majorant -/

namespace NSSE.DirectRankFormulaRecurrence

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ExistentialFormulaPackage ArrayAtomExistentialPackages
open ExactReachabilitySize ComputedScalarLoweringBudget ExistentialRowNonemptySize
open RankAvoidanceCompiler (Problem liftedRows)
open DirectRankTransition DirectRankResources DirectRankExistentialStep DirectExistentialRankCompiler

universe u v w

theorem package_parts {L : FirstOrder.Language.{u,v}} {P : Type w} (A : Package L P) :
    A.vars ≤ nodes A.toFormula ∧ nodes A.boundedBody ≤ nodes A.toFormula := by
  have hv := ExistentialScalarPrenexSize.prefix_vars_le A
  have he : nodes A.toFormula = nodes A.boundedBody+5*A.vars := by
    simp only [Package.toFormula, Package.boundedBody, nodes_bdRelabel, nodes_closeColumn]
  omega

theorem seed_mono {n B n' B' : Nat} (hn : n ≤ n') (hb : B ≤ B') : seedBound n B ≤ seedBound n' B' := by
  unfold seedBound; gcongr

theorem nonempty_mono {n B n' B' : Nat} (hn : n ≤ n') (hb : B ≤ B') :
    nonemptyBound n B ≤ nonemptyBound n' B' := by unfold nonemptyBound; gcongr; decide

theorem scalar_mono {B q s B' q' s' : Nat} (hb : B ≤ B') (hq : q ≤ q') (hs : s ≤ s') :
    ScalarLoweringSingleExponential.bound B q s ≤ ScalarLoweringSingleExponential.bound B' q' s' := by
  unfold ScalarLoweringSingleExponential.bound
  gcongr
  · exact UniformArrayAtomBound.atomBound_mono hb le_rfl
  · decide
  · unfold WholeScalarLoweringBound.presentationExponent; gcongr

def coefficient (B : Nat) := 4*(UniformArrayAtomBound.atomBound B 1+24)*2^WholeScalarLoweringBound.presentationExponent B

theorem scalar_cubic (B s : Nat) : ScalarLoweringSingleExponential.bound B s s ≤ coefficient B*(s+1)^3 := by
  unfold ScalarLoweringSingleExponential.bound coefficient
  have h : s+s+1 ≤ 2*(s+1) := by omega
  calc
    _ ≤ 2*(2*(s+1))*(s+1)^2*(UniformArrayAtomBound.atomBound B 1+24)*2^WholeScalarLoweringBound.presentationExponent B := by gcongr
    _ = _ := by ring

def presentationBudget (I : Problem) := presentationSize (liftedRows I) (cleaned I).2

def factor (B : Nat) := 32+seedBound B B+coefficient B

theorem step_bound (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    (A : Package (next I).language Empty) (B s : Nat)
    (hC : rowSize I.candidate ≤ B) (hP : presentationBudget I ≤ B) (hA : nodes A.toFormula ≤ s) :
    nodes (Package.disj (ExistentialRowNonempty.seedOnly I.candidate hc) (lowerStep I hr hc A)).toFormula+1 ≤
      factor B*(s+1)^3 := by
  have hp := package_parts A
  have hcb := row_budget I.candidate
  have hc' := DirectRowBooleanSize.of_budget _ hcb
  have hseed := (seed_le I.candidate hc hc').trans (seed_mono (hcb.states.trans hC) hC)
  have hl := lowerStep_bound I hr hc A
  have hb := (scalar_mono hP (hp.1.trans hA) (hp.2.trans hA)).trans (scalar_cubic B s)
  have hon : 1 ≤ (s+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hadd : 32+seedBound B B ≤ (32+seedBound B B)*(s+1)^3 := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  rw [Package.nodes_disj]
  unfold factor
  unfold presentationBudget at hb
  nlinarith

/-- Uniform budget computed from the actual finite recursive input trajectory. -/
def commonBudget : Nat → Problem → Nat
  | 0, I => max (max (rowSize I.candidate) (presentationBudget I)) (rowSize (next I).candidate)
  | h+1, I => max (max (rowSize I.candidate) (presentationBudget I)) (commonBudget h (next I))

def majorant (B : Nat) : Nat → Nat
  | 0 => factor B*(nonemptyBound B B+1)^3
  | h+1 => factor B*(majorant B h)^3

theorem solve_bound (h : Nat) : ∀ (I : Problem) (hr : ∀ i, RowQF (I.rows i)) (hc : RowQF I.candidate)
    (B : Nat), commonBudget h I ≤ B → nodes (solve h I hr hc).toFormula+1 ≤ majorant B h := by
  induction h with
  | zero =>
    intro I hr hc B hb
    have hC : rowSize I.candidate ≤ B := (le_max_left _ _).trans ((le_max_left _ _).trans hb)
    have hP : presentationBudget I ≤ B := (le_max_right _ _).trans ((le_max_left _ _).trans hb)
    have hN : rowSize (next I).candidate ≤ B := (le_max_right _ _).trans hb
    have hn := row_budget (next I).candidate
    have hbase := (nonempty_le (next I).candidate (next_candidate_qf I) (DirectRowBooleanSize.of_budget _ hn)).trans
      (nonempty_mono (hn.states.trans hN) hN)
    exact step_bound I hr hc _ B _ hC hP hbase
  | succ h ih =>
    intro I hr hc B hb
    have hC : rowSize I.candidate ≤ B := (le_max_left _ _).trans ((le_max_left _ _).trans hb)
    have hP : presentationBudget I ≤ B := (le_max_right _ _).trans ((le_max_left _ _).trans hb)
    have hN : commonBudget h (next I) ≤ B := (le_max_right _ _).trans hb
    have hr' := ih (next I) (next_rows_qf I) (next_candidate_qf I) B hN
    have hp := step_bound I hr hc (solve h (next I) (next_rows_qf I) (next_candidate_qf I)) B
      (nodes (solve h (next I) (next_rows_qf I) (next_candidate_qf I)).toFormula) hC hP le_rfl
    apply hp.trans
    change factor B*(_+1)^3 ≤ factor B*(majorant B h)^3
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr' 3)

end NSSE.DirectRankFormulaRecurrence
