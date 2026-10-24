import NSSE.StoredRankCostEnvelope

/-! The closed cost recursion of the stored rank recursion: every budget of
one step is replaced by its horizon envelope, the recursive package's size
by `sizeAt`, and `solve_cost` bounds the counted cost of `solve` at every
depth and rank within the horizon. -/
namespace NSSE.StoredRankCostHorizon
open StoredNextProblem StoredRankSolve StoredRankSolveBounds StoredRankSolveEnvelope
open StoredRankHorizon StoredRankCostEnvelope
open StoredRelationalElimination (size)

/-- The cost envelope of one step, for a recursive package of size `≤ s`:
`k` rows, `N` states, candidate `c`, cleaned `cl`, candidate nodes `F`,
row nodes `Bn`, lifted node bound `L`, arity `K`. -/
def stepEnv (k N c cl F Bn L K s : Nat) :=
  4+StoredRelationalNonempty.seedBudget c F K+StoredNextProblem.budget k N c F Bn K+
    costEnv k (N+cl) cl s s L K+disjBudget K (seedSize c F) (sizeEnv k N cl s L s)

theorem stepEnv_mono_size {k N c cl F Bn L K s s' : Nat} (h : s ≤ s') :
    stepEnv k N c cl F Bn L K s ≤ stepEnv k N c cl F Bn L K s' := by
  unfold stepEnv
  have h1 := costEnv_mono (le_refl k) (le_refl (N+cl)) (le_refl cl) h h (le_refl L) (le_refl K)
  have h2 := disjBudget_mono (le_refl K) (le_refl (seedSize c F))
    (sizeEnv_mono (le_refl k) (le_refl N) (le_refl cl) h (le_refl L) h)
  omega

def costRec (k N c cl F Bn L K : Nat) (sz : Nat → Nat) : Nat → Nat
  | 0 => stepEnv k N c cl F Bn L K (nonemptySize c F)+StoredRelationalNonempty.nonemptyBudget c F K
  | h+1 => stepEnv k N c cl F Bn L K (sz h)+costRec k N c cl F Bn L K sz h

def costAt (k N c F B K H : Nat) (h : Nat) :=
  costRec (rowCount k N H) (rowLimit N H) (candBound k N c H) (cleanedBound k N c H)
    (candNodes k N c F H) (max B 9) (liftedEnv k N c F B H) (max K 2) (sizeAt k N c F B H) h

/-! ### One step at depth `t` -/

theorem step_cost_le (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat)
    (ht : t+1 ≤ H) (V Fr s : Nat) (hV : V ≤ s) (hF : Fr ≤ s) :
    stepBudget (descend t X).2.2 (rowLimit N H) (candNodes k N c F H) (max B 9) (max K 2) V Fr ≤
      stepEnv (rowCount k N H) (rowLimit N H) (candBound k N c H) (cleanedBound k N c H)
        (candNodes k N c F H) (max B 9) (liftedEnv k N c F B H) (max K 2) s := by
  have hns := fun i => ns_le X k N c F B K h H t (by omega) i
  have hk := k_le X k N c F B K h H t (by omega)
  have hc := c_le X k N c F B K h H t (by omega)
  have hcl := cleaned_le X k N c F B K h H t (by omega)
  have hlift := lifted_le X k N c F B K h H t (by omega)
  -- seed
  have h1 := seedBudget_mono (n := (descend t X).2.2.c) (n' := candBound k N c H) (F' := candNodes k N c F H)
    (K' := max K 2) (by omega) le_rfl le_rfl
  -- next
  have h2 := nextBudget_mono hk (le_refl (rowLimit N H)) (show (descend t X).2.2.c ≤ candBound k N c H by omega)
    (le_refl (candNodes k N c F H)) (le_refl (max B 9)) (le_refl (max K 2))
  -- lowering cost
  have h3 : lowerBudget (descend t X).2.2 (rowLimit N H) (candNodes k N c F H) (max B 9) (max K 2) V Fr ≤
      costEnv (rowCount k N H) (rowLimit N H+cleanedBound k N c H) (cleanedBound k N c H) s s
        (liftedEnv k N c F B H) (max K 2) := by
    unfold lowerBudget
    refine (budget_le_env (descend t X).2.2.ns _ V _ _ (max K 2) Fr
      (fun i => (hns i).trans (Nat.le_add_right _ _))).trans ?_
    exact costEnv_mono hk (by omega) hcl hV hF hlift le_rfl
  -- lowering size, for the disjunction
  have h4 : lowerSize (descend t X).2.2 (candNodes k N c F H) (max B 9) V Fr ≤
      sizeEnv (rowCount k N H) (rowLimit N H) (cleanedBound k N c H) s (liftedEnv k N c F B H) s :=
    (lowerSize_le_env (descend t X).2.2 (rowLimit N H) _ _ V Fr hns).trans
      (sizeEnv_mono hk le_rfl hcl hV hlift hF)
  have h5 := disjBudget_mono (le_refl (max K 2))
    (seedSize_mono (n := (descend t X).2.2.c) (n' := candBound k N c H) (F' := candNodes k N c F H) (by omega) le_rfl) h4
  unfold stepBudget stepEnv
  omega

theorem base_cost_at (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat)
    (ht : t+1 ≤ H) :
    (base (descend t X).2.2).2 ≤
      StoredRelationalNonempty.nonemptyBudget (candBound k N c H) (candNodes k N c F H) (max K 2) := by
  have hb := base_cost (descend t X).2.2
  have hc := c_le X k N c F B K h H (t+1) ht
  rw [descend_succ] at hc
  refine hb.trans (nonemptyBudget_mono (by omega) ?_ (by omega))
  rw [next_states] at hc
  unfold candNodes cleanedStates
  omega

/-! ### The recursion -/

theorem solve_cost (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H : Nat) :
    ∀ (r t : Nat), t+r+1 ≤ H →
      (solve r (descend t X).2.2).2 ≤ costAt k N c F B K H r := by
  intro r
  induction r with
  | zero =>
    intro t ht
    have hs := solve_zero_cost (descend t X).2.2 (rowLimit N H) (candNodes k N c F H) (max B 9) (max K 2)
      (fun i => ns_le X k N c F B K h H t (by omega) i)
      (candidate_at X k N c F B K h H t (by omega)) (family_at X k N c F B K h t)
    have hbase := base_size_at X k N c F B K h H t (by omega)
    have hst := step_cost_le X k N c F B K h H t (by omega) _ _ _
      ((vars_le_size _).trans hbase) ((nodes_le_size _).trans hbase)
    have hbc := base_cost_at X k N c F B K h H t (by omega)
    simp only [costAt,costRec]
    omega
  | succ r ih =>
    intro t ht
    have hs := solve_succ_cost r (descend t X).2.2 (rowLimit N H) (candNodes k N c F H) (max B 9) (max K 2)
      (fun i => ns_le X k N c F B K h H t (by omega) i)
      (candidate_at X k N c F B K h H t (by omega)) (family_at X k N c F B K h t)
    have hsize : size (inner r (descend t X).2.2).1 ≤ sizeAt k N c F B H r :=
      solve_size X k N c F B K h H r (t+1) (by omega)
    have hst := step_cost_le X k N c F B K h H t (by omega) _ _ _
      ((vars_le_size _).trans hsize) ((nodes_le_size _).trans hsize)
    have hin : (inner r (descend t X).2.2).2 ≤ costAt k N c F B K H r := ih (t+1) (by omega)
    simp only [costAt,costRec] at hin ⊢
    omega

/-- The whole recursion from the initial problem. -/
theorem solve_cost_initial (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H : Nat) :
    (solve H X.2.2).2 ≤ costAt k N c F B K (H+1) H :=
  solve_cost X k N c F B K h (H+1) H 0 (by omega)

end NSSE.StoredRankCostHorizon
