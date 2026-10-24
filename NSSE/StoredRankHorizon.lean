import NSSE.StoredRankSolveEnvelope

/-! Horizon-wide parameter bounds for the stored rank recursion: the chain of
stored problems `descend t X` produced by iterating `next`, with uniform
bounds on row states, row count, candidate states, candidate/row field nodes
and arity at every depth `t ≤ H`, from bounds on the initial problem alone.
Then the closed size recursion `sizeRec` for `solve`.  This is the stored
counterpart of `DirectRankHorizonStates`. -/
namespace NSSE.StoredRankHorizon
open StoredNextProblem StoredRankSolve StoredRankSolveBounds StoredRankSolveEnvelope
open StoredRelationalElimination (size)

/-- A stored problem with its relation family and parameter type packed. -/
abbrev Packed := Σ (R : Nat → Type) (P : Type), Problem R P

def descend : Nat → Packed → Packed
  | 0, X => X
  | t+1, X => ⟨_,_,(next (descend t X).2.2).1.2⟩

theorem descend_succ (t : Nat) (X : Packed) :
    (descend (t+1) X).2.2 = (next (descend t X).2.2).1.2 := rfl

/-- Uniform bounds on one stored problem. -/
structure Bounds (X : Packed) (k N c F B K : Nat) : Prop where
  rows : X.2.2.k ≤ k
  ns : ∀ i, X.2.2.ns i ≤ N
  cand : X.2.2.c ≤ c
  candidate : StoredRowTransport.Bounds X.2.2.candidate F K
  family : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read X.2.2.rows i).1 B K

/-! ### One step -/

theorem next_bounds_of (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K)
    (hB : 9 ≤ B) (hK : 2 ≤ K) :
    Bounds ⟨_,_,(next X.2.2).1.2⟩ (k*(2*N^4)) (4*N+2) (c*2^((3*N+1)*k)+1)
      (7+10*(c*2^((3*N+1)*k))) B K := by
  have hk := next_k_le X.2.2 N h.ns
  have hc := next_c_le X.2.2 N h.ns
  have hpow : 2^((3*N+1)*X.2.2.k) ≤ 2^((3*N+1)*k) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left (3*N+1) h.rows)
  have hprod : X.2.2.c*2^((3*N+1)*X.2.2.k) ≤ c*2^((3*N+1)*k) := Nat.mul_le_mul h.cand hpow
  have hcs := cleanedStates_le X.2.2 N h.ns
  refine ⟨?_,next_ns_le X.2.2 N h.ns,?_,?_,?_⟩
  · exact hk.trans (Nat.mul_le_mul_right _ h.rows)
  · show (next X.2.2).1.2.c ≤ _
    omega
  · exact bounds_mono (next_candidate_bounds X.2.2) (by omega) (by omega)
  · intro j; exact bounds_mono (next_rows_bounds X.2.2 j) hB hK

/-! ### Horizon envelopes -/

def rowLimit (N : Nat) (t : Nat) := (N+1)*4^t
def rowCount (k N H : Nat) := k*(2*(rowLimit N H)^4+1)^H
def stepExp (k N H : Nat) := (3*rowLimit N H+1)*rowCount k N H+1
def candBound (k N c H : Nat) := (c+1)*2^(H*stepExp k N H)
def cleanedBound (k N c H : Nat) := candBound k N c H*2^(stepExp k N H)
def candNodes (k N c F H : Nat) := max F (7+10*candBound k N c H)

theorem rowLimit_mono (N : Nat) {s t : Nat} (h : s ≤ t) : rowLimit N s ≤ rowLimit N t := by
  unfold rowLimit; gcongr; norm_num

theorem four_pow_pos (t : Nat) : 1 ≤ 4^t := Nat.one_le_pow _ _ (by decide)

/-- Row states along the chain. -/
theorem ns_at (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (t : Nat) :
    ∀ i, (descend t X).2.2.ns i+1 ≤ rowLimit N t := by
  induction t with
  | zero => intro i; have := h.ns i; simp only [descend,rowLimit,pow_zero,Nat.mul_one]; omega
  | succ t ih =>
    intro j
    change (next (descend t X).2.2).1.2.ns j+1 ≤ _
    have hj := next_ns_le (descend t X).2.2 (rowLimit N t-1) (fun i => by have := ih i; omega) j
    have h4 : rowLimit N (t+1) = 4*rowLimit N t := by unfold rowLimit; ring
    have hpos : 0 < rowLimit N t := by unfold rowLimit; positivity
    omega

theorem ns_le (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat) (ht : t ≤ H)
    (i : Fin (descend t X).2.2.k) : (descend t X).2.2.ns i ≤ rowLimit N H := by
  have := ns_at X k N c F B K h t i
  have := rowLimit_mono N ht
  omega

/-- Row count along the chain. -/
theorem k_at (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat) (ht : t ≤ H) :
    (descend t X).2.2.k ≤ k*(2*(rowLimit N H)^4+1)^t := by
  induction t with
  | zero => simpa only [descend,pow_zero,Nat.mul_one] using h.rows
  | succ t ih =>
    have hi := ih (by omega)
    have hn := next_k_le (descend t X).2.2 (rowLimit N H) (fun i => ns_le X k N c F B K h H t (by omega) i)
    rw [descend_succ]
    calc (next (descend t X).2.2).1.2.k ≤ (descend t X).2.2.k*(2*(rowLimit N H)^4) := hn
      _ ≤ (k*(2*(rowLimit N H)^4+1)^t)*(2*(rowLimit N H)^4+1) :=
          Nat.mul_le_mul hi (Nat.le_add_right _ _)
      _ = _ := by ring

theorem k_le (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat) (ht : t ≤ H) :
    (descend t X).2.2.k ≤ rowCount k N H := by
  apply (k_at X k N c F B K h H t ht).trans
  unfold rowCount
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) ht)

theorem two_pow_pos (x : Nat) : 1 ≤ 2^x := Nat.one_le_pow _ _ (by decide)

/-- Candidate states along the chain. -/
theorem c_at (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat) (ht : t ≤ H) :
    (descend t X).2.2.c+1 ≤ (c+1)*2^(t*stepExp k N H) := by
  induction t with
  | zero => simpa only [descend,Nat.zero_mul,pow_zero,Nat.mul_one] using Nat.add_le_add_right h.cand 1
  | succ t ih =>
    have hi := ih (by omega)
    have hn := next_c_le (descend t X).2.2 (rowLimit N H) (fun i => ns_le X k N c F B K h H t (by omega) i)
    have hk := k_le X k N c F B K h H t (by omega)
    have he : (3*rowLimit N H+1)*(descend t X).2.2.k ≤ (3*rowLimit N H+1)*rowCount k N H :=
      Nat.mul_le_mul_left _ hk
    have hp : 2^((3*rowLimit N H+1)*(descend t X).2.2.k) ≤ 2^((3*rowLimit N H+1)*rowCount k N H) :=
      Nat.pow_le_pow_right (by decide) he
    rw [descend_succ]
    have h1 := two_pow_pos ((3*rowLimit N H+1)*rowCount k N H)
    have h2 := two_pow_pos (t*stepExp k N H)
    -- c' + 1 ≤ c_t·2^X + 2 ≤ (c_t+1)·2^(X+1) ≤ (c+1)·2^(t·s)·2^(s)
    have hs : (descend t X).2.2.c*2^((3*rowLimit N H+1)*(descend t X).2.2.k)+1+1 ≤
        ((descend t X).2.2.c+1)*2^(stepExp k N H) := by
      unfold stepExp
      rw [pow_succ]
      have := Nat.mul_le_mul_left (descend t X).2.2.c hp
      nlinarith
    calc (next (descend t X).2.2).1.2.c+1 ≤ _ := Nat.add_le_add_right hn 1
      _ ≤ ((descend t X).2.2.c+1)*2^(stepExp k N H) := hs
      _ ≤ ((c+1)*2^(t*stepExp k N H))*2^(stepExp k N H) := Nat.mul_le_mul_right _ hi
      _ = (c+1)*2^((t+1)*stepExp k N H) := by ring

theorem c_le (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat) (ht : t ≤ H) :
    (descend t X).2.2.c+1 ≤ candBound k N c H := by
  apply (c_at X k N c F B K h H t ht).trans
  unfold candBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ ht))

/-- Cleaned candidate states along the chain. -/
theorem cleaned_le (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat) (ht : t ≤ H) :
    cleanedStates (descend t X).2.2 ≤ cleanedBound k N c H := by
  have h1 := cleanedStates_le (descend t X).2.2 (rowLimit N H) (fun i => ns_le X k N c F B K h H t ht i)
  have h2 := c_le X k N c F B K h H t ht
  have h3 := k_le X k N c F B K h H t ht
  have hp : 2^((3*rowLimit N H+1)*(descend t X).2.2.k) ≤ 2^(stepExp k N H) := by
    apply Nat.pow_le_pow_right (by decide)
    unfold stepExp
    have := Nat.mul_le_mul_left (3*rowLimit N H+1) h3
    omega
  unfold cleanedBound
  calc cleanedStates (descend t X).2.2 ≤ _ := h1
    _ ≤ candBound k N c H*2^(stepExp k N H) := Nat.mul_le_mul (by omega) hp

/-- Candidate and row field bounds along the chain. -/
theorem candidate_at (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat) (ht : t ≤ H) :
    StoredRowTransport.Bounds (descend t X).2.2.candidate (candNodes k N c F H) (max K 2) := by
  cases t with
  | zero => exact bounds_mono h.candidate (le_max_left _ _) (le_max_left _ _)
  | succ t =>
    rw [descend_succ]
    have hc := c_le X k N c F B K h H (t+1) ht
    rw [descend_succ,next_states] at hc
    refine bounds_mono (next_candidate_bounds (descend t X).2.2) ?_ (by omega)
    unfold candNodes cleanedStates
    omega

theorem family_at (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (t : Nat)
    (i : Fin (descend t X).2.2.k) :
    StoredRowTransport.Bounds (StoredRelationArrayPackage.read (descend t X).2.2.rows i).1 (max B 9) (max K 2) := by
  cases t with
  | zero => exact bounds_mono (h.family i) (le_max_left _ _) (le_max_left _ _)
  | succ t => exact bounds_mono (next_rows_bounds (descend t X).2.2 i) (le_max_right _ _) (le_max_right _ _)

/-! ### The lifted node bound along the chain -/

theorem increase_mono_nodes {n B B' : Nat} (h : B ≤ B') :
    StoredCleanupStep.increase n B ≤ StoredCleanupStep.increase n B' := by
  unfold StoredCleanupStep.increase StoredRowComplementGuards.sizeBudget StoredRowComplementGuards.sumSize
    StoredRowComplementGuards.termSize StoredEmptyTailGuards.sizeBudget StoredEmptyTailGuards.switchSize
  gcongr

def liftedEnv (k N c F B H : Nat) :=
  candNodes k N c F H+rowCount k N H*StoredCleanupStep.increase (rowLimit N H) (max B 9)+max B 9

theorem lifted_le (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat) (ht : t ≤ H) :
    liftedNodes (descend t X).2.2 (candNodes k N c F H) (max B 9) ≤ liftedEnv k N c F B H := by
  unfold liftedNodes liftedEnv
  have hf := StoredCleanupBound.fieldIncrease_bound (List.ofFn (descend t X).2.2.ns) (rowLimit N H) (max B 9) (by
    intro n hn
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
    exact ns_le X k N c F B K h H t ht i)
  rw [List.length_ofFn] at hf
  have hk := k_le X k N c F B K h H t ht
  have := Nat.mul_le_mul_right (StoredCleanupStep.increase (rowLimit N H) (max B 9)) hk
  omega

/-! ### The closed size recursion -/

theorem seedSize_mono {n n' F F' : Nat} (hn : n ≤ n') (hF : F ≤ F') : seedSize n F ≤ seedSize n' F' := by
  unfold seedSize; gcongr
theorem nonemptySize_mono {n n' F F' : Nat} (hn : n ≤ n') (hF : F ≤ F') :
    nonemptySize n F ≤ nonemptySize n' F' := by
  unfold nonemptySize; gcongr; norm_num

/-- The size recursion over the rank, with all problem parameters replaced by
their horizon envelopes: `k` rows, `N` states, candidate `c`, cleaned
candidate `cl`, candidate nodes `F`, lifted node bound `L`. -/
def sizeRec (k N c cl F L : Nat) : Nat → Nat
  | 0 => 3+seedSize c F+sizeEnv k N cl (nonemptySize c F) L (nonemptySize c F)
  | h+1 => 3+seedSize c F+sizeEnv k N cl (sizeRec k N c cl F L h) L (sizeRec k N c cl F L h)

def sizeAt (k N c F B H : Nat) (h : Nat) :=
  sizeRec (rowCount k N H) (rowLimit N H) (candBound k N c H) (cleanedBound k N c H)
    (candNodes k N c F H) (liftedEnv k N c F B H) h

/-- The rank-0 nonemptiness package at depth `t < H`. -/
theorem base_size_at (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H t : Nat)
    (ht : t+1 ≤ H) :
    size (base (descend t X).2.2).1 ≤ nonemptySize (candBound k N c H) (candNodes k N c F H) := by
  have hb := (base_shape (descend t X).2.2).1
  have hc := c_le X k N c F B K h H (t+1) ht
  rw [descend_succ] at hc
  refine hb.trans (nonemptySize_mono (by omega) ?_)
  rw [next_states] at hc
  unfold candNodes cleanedStates
  omega

theorem solve_size (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H : Nat) :
    ∀ (r t : Nat), t+r+1 ≤ H →
      size (solve r (descend t X).2.2).1 ≤ sizeAt k N c F B H r := by
  intro r
  induction r with
  | zero =>
    intro t ht
    have hs := (solve_zero_shape (descend t X).2.2 (candNodes k N c F H) (max B 9) (max K 2)
      (candidate_at X k N c F B K h H t (by omega)) (family_at X k N c F B K h t)).1
    have hc := c_le X k N c F B K h H t (by omega)
    have hseed := seedSize_mono (n := (descend t X).2.2.c) (n' := candBound k N c H) (F' := candNodes k N c F H) (by omega) le_rfl
    have hbase := base_size_at X k N c F B K h H t (by omega)
    have hl := lowerSize_le_env (descend t X).2.2 (rowLimit N H) (candNodes k N c F H) (max B 9)
      (base (descend t X).2.2).1.vars (StoredRelationalFormula.nodes (base (descend t X).2.2).1.body)
      (fun i => ns_le X k N c F B K h H t (by omega) i)
    have hm := sizeEnv_mono (k_le X k N c F B K h H t (by omega)) (le_refl (rowLimit N H))
      (cleaned_le X k N c F B K h H t (by omega))
      ((vars_le_size _).trans hbase) (lifted_le X k N c F B K h H t (by omega))
      ((nodes_le_size _).trans hbase)
    simp only [sizeAt,sizeRec]
    omega
  | succ r ih =>
    intro t ht
    have hs := (solve_succ_shape r (descend t X).2.2 (candNodes k N c F H) (max B 9) (max K 2)
      (candidate_at X k N c F B K h H t (by omega)) (family_at X k N c F B K h t)).1
    have hc := c_le X k N c F B K h H t (by omega)
    have hseed := seedSize_mono (n := (descend t X).2.2.c) (n' := candBound k N c H) (F' := candNodes k N c F H) (by omega) le_rfl
    have hin : size (inner r (descend t X).2.2).1 ≤ sizeAt k N c F B H r := ih (t+1) (by omega)
    have hl := lowerSize_le_env (descend t X).2.2 (rowLimit N H) (candNodes k N c F H) (max B 9)
      (inner r (descend t X).2.2).1.vars (StoredRelationalFormula.nodes (inner r (descend t X).2.2).1.body)
      (fun i => ns_le X k N c F B K h H t (by omega) i)
    have hm := sizeEnv_mono (k_le X k N c F B K h H t (by omega)) (le_refl (rowLimit N H))
      (cleaned_le X k N c F B K h H t (by omega))
      ((vars_le_size _).trans hin) (lifted_le X k N c F B K h H t (by omega))
      ((nodes_le_size _).trans hin)
    simp only [sizeAt,sizeRec] at hm hin ⊢
    omega

/-- The whole recursion from the initial problem: rank `H` at depth `0`; the
chain of problems goes one step deeper than the rank, for the rank-0
nonemptiness package. -/
theorem solve_size_initial (X : Packed) (k N c F B K : Nat) (h : Bounds X k N c F B K) (H : Nat) :
    size (solve H X.2.2).1 ≤ sizeAt k N c F B (H+1) H :=
  solve_size X k N c F B K h (H+1) H 0 (by omega)

end NSSE.StoredRankHorizon
