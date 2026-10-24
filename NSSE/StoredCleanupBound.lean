import NSSE.StoredCleanupFamily

/-! Uniform cleanup bounds: a product of original-row factors, additive field growth,
and a linear number of uniformly bounded actual subtraction steps. -/
namespace NSSE.StoredCleanupBound
open StoredCleanupStep StoredCleanupList

def stepUpper (c n B K : Nat) := 4+1644*(n+B+K+1)^5+
  953*(3*n+2^(3*n)+StoredEmptyTailGuards.sizeBudget n B+K+1)^6+
  141*(c+2^(3*n)+2)^6

theorem step_budget_bound (c n B K : Nat) : StoredCleanupStep.budget c n B K ≤ stepUpper c n B K := by
  have ha := StoredEmptyTailCompiler.budget_polynomial n B K
  have hb := StoredRowComplementBound.budget_bound (3*n) (StoredEmptyTailGuards.sizeBudget n B) K
  have hc := StoredRowIntersection.budget_polynomial c (2^(3*n)+1)
  have he : c+(2^(3*n)+1)+1=c+2^(3*n)+2 := by omega
  rw [he] at hc
  unfold StoredCleanupStep.budget StoredRowDifference.budget stepUpper
  omega

theorem factor_mono {n N : Nat} (h : n ≤ N) : factor n ≤ factor N := by unfold factor; gcongr; norm_num
theorem factor_one (N : Nat) : 1 ≤ factor N := by unfold factor; exact Nat.le_add_left _ _
theorem increase_mono {n N : Nat} (h : n ≤ N) (B : Nat) : increase n B ≤ increase N B := by
  unfold increase StoredRowComplementGuards.sizeBudget StoredRowComplementGuards.sumSize
    StoredRowComplementGuards.termSize StoredEmptyTailGuards.sizeBudget StoredEmptyTailGuards.switchSize
  gcongr
theorem stepUpper_mono {c C n N : Nat} (hc : c ≤ C) (hn : n ≤ N) (B K : Nat) :
    stepUpper c n B K ≤ stepUpper C N B K := by
  unfold stepUpper StoredEmptyTailGuards.sizeBudget StoredEmptyTailGuards.switchSize
  gcongr <;> norm_num

theorem stateFactor_bound (ns : List Nat) (N : Nat) (h : ∀ n ∈ ns, n ≤ N) :
    stateFactor ns ≤ (factor N)^ns.length := by
  induction ns with
  | nil => simp [stateFactor]
  | cons n ns ih =>
    have ht := ih (fun n hn => h n (by simp [hn]))
    have hf := factor_mono (h n (by simp))
    simp only [stateFactor,List.map_cons,List.prod_cons,List.length_cons,pow_succ]
    have hm := Nat.mul_le_mul hf ht
    unfold stateFactor at hm
    nlinarith

theorem fieldIncrease_bound (ns : List Nat) (N B : Nat) (h : ∀ n ∈ ns, n ≤ N) :
    fieldIncrease ns B ≤ ns.length*increase N B := by
  induction ns with
  | nil => simp [fieldIncrease]
  | cons n ns ih =>
    have ht := ih (fun n hn => h n (by simp [hn]))
    have hf := increase_mono (h n (by simp)) B
    simp only [fieldIncrease,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

def uniform (c l N B K : Nat) := 1+l*(2+stepUpper (c*(factor N)^l) N B K)
theorem budget_uniform (c : Nat) (ns : List Nat) (N B K : Nat) (h : ∀ n ∈ ns, n ≤ N) :
    StoredCleanupList.budget c ns B K ≤ uniform c ns.length N B K := by
  induction ns generalizing c with
  | nil => simp only [StoredCleanupList.budget,uniform,List.length_nil,Nat.zero_mul,Nat.add_zero]; exact le_rfl
  | cons n ns ih =>
    have ht := ih (c*factor n) (fun n hn => h n (by simp [hn]))
    have hf := factor_mono (h n (by simp))
    have hpow : 1 ≤ (factor N)^(ns.length+1) := Nat.one_le_pow _ _ (factor_one N)
    have hc : c ≤ c*(factor N)^(ns.length+1) := by nlinarith
    have hs : (c*factor n)*(factor N)^ns.length ≤ c*(factor N)^(ns.length+1) := by
      rw [pow_succ]
      have hm := Nat.mul_le_mul_left (c*(factor N)^ns.length) hf
      nlinarith
    have ha := (step_budget_bound c n B K).trans (stepUpper_mono hc (h n (by simp)) B K)
    have hb := stepUpper_mono hs (le_refl N) B K
    have hm := Nat.mul_le_mul_left ns.length hb
    simp only [StoredCleanupList.budget,uniform,List.length_cons] at *
    nlinarith

theorem family_bound {R : Nat → Type} {P : Type} {k c : Nat} {ns : Fin k → Nat}
    (rows : StoredRelationArrayPackage.Family R P ns) (C : StoredRelationalRow.Row R P c) (last : P)
    (N B K : Nat) (hn : ∀ i, ns i ≤ N)
    (h : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K) :
    (StoredCleanupFamily.build rows C last).2 ≤ 1+uniform c k N B K := by
  have ha := StoredCleanupFamily.bound rows C last B K h
  have hb := budget_uniform c (List.ofFn ns) N B K (by
    intro n hn'
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn'
    exact hn i)
  rw [List.length_ofFn] at hb
  unfold StoredCleanupFamily.budget at ha
  omega
theorem family_states {R : Nat → Type} {P : Type} {k c : Nat} {ns : Fin k → Nat}
    (rows : StoredRelationArrayPackage.Family R P ns) (C : StoredRelationalRow.Row R P c) (last : P)
    (N : Nat) (hn : ∀ i, ns i ≤ N) :
    (StoredCleanupFamily.build rows C last).1.1 ≤ c*(factor N)^k := by
  have h := stateFactor_bound (List.ofFn ns) N (by
    intro n hn'
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn'
    exact hn i)
  rw [List.length_ofFn] at h
  rw [StoredCleanupFamily.states]
  exact Nat.mul_le_mul_left c h
theorem factor_power_bound (N k : Nat) : (factor N)^k ≤ 2^((3*N+1)*k) := by
  have hf : factor N ≤ 2^(3*N+1) := by
    have hp : 1 ≤ 2^(3*N) := Nat.one_le_pow _ _ (by decide)
    unfold factor
    rw [pow_succ]
    omega
  simpa only [← pow_mul] using Nat.pow_le_pow_left hf k

theorem family_exponential_states {R : Nat → Type} {P : Type} {k c : Nat} {ns : Fin k → Nat}
    (rows : StoredRelationArrayPackage.Family R P ns) (C : StoredRelationalRow.Row R P c) (last : P)
    (N : Nat) (hn : ∀ i, ns i ≤ N) :
    (StoredCleanupFamily.build rows C last).1.1 ≤ c*2^((3*N+1)*k) :=
  (family_states rows C last N hn).trans (Nat.mul_le_mul_left c (factor_power_bound N k))

theorem family_exponential_cost {R : Nat → Type} {P : Type} {k c : Nat} {ns : Fin k → Nat}
    (rows : StoredRelationArrayPackage.Family R P ns) (C : StoredRelationalRow.Row R P c) (last : P)
    (N B K : Nat) (hn : ∀ i, ns i ≤ N)
    (h : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K) :
    (StoredCleanupFamily.build rows C last).2 ≤ 2+k*(2+stepUpper (c*2^((3*N+1)*k)) N B K) := by
  have ha := family_bound rows C last N B K hn h
  have hs := stepUpper_mono (Nat.mul_le_mul_left c (factor_power_bound N k)) (le_refl N) B K
  have hm := Nat.mul_le_mul_left k hs
  unfold uniform at ha
  nlinarith
end NSSE.StoredCleanupBound
