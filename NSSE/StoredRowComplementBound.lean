import NSSE.StoredRowDifference

/-! A polynomial in the expanded state count bounds actual complement construction. -/
namespace NSSE.StoredRowComplementBound
open StoredRowComplementCompiler

def envelope (n p B K : Nat) := 10+14*p+7*(n+1)*p^2+7+
  2*vectorBudget (p+1) (2+(p+1)+StoredRowComplementGuards.budget n B K)+
  matrixBudget (p+1) (3+2*(p+1)+StoredRowComplementGuards.budget n B K)+matrixBudget (p+1) 2

theorem covers (n B K : Nat) : budget n B K ≤ envelope n (2^n) B K := by
  have hp : 3^n ≤ (2^n)^2 := by
    have h := Nat.pow_le_pow_left (show 3 ≤ 2^2 by decide) n
    simpa only [← pow_mul,Nat.mul_comm] using h
  unfold budget StoredRowComplementStates.budget StoredRowComplementStates.entriesBudget
    CountedNaturalPower.budget labelBudget vertexCost edgeCost envelope
  norm_num
  nlinarith [Nat.mul_le_mul_left (7*(n+1)) hp]

theorem diagonal (u : Nat) : envelope u u u u = 129+254*u+270*u^2+189*u^3+84*u^4+24*u^5+3*u^6 := by
  unfold envelope matrixBudget vectorBudget StoredRowComplementGuards.budget StoredRowComplementGuards.sumBudget
    StoredRowComplementGuards.termBudget StoredTruthCell.budget StoredTruthCell.allBudget
    StoredRunTable.anyBudget StoredForwardTableBuild.tabBudget StoredRelationalFormula.weight
  ring

theorem envelope_polynomial (n p B K : Nat) : envelope n p B K ≤ 953*(n+p+B+K+1)^6 := by
  let u := n+p+B+K+1
  have hn : n ≤ u := by dsimp [u]; omega
  have hp : p ≤ u := by dsimp [u]; omega
  have hb : B ≤ u := by dsimp [u]; omega
  have hk : K ≤ u := by dsimp [u]; omega
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hm : envelope n p B K ≤ envelope u u u u := by
    unfold envelope matrixBudget vectorBudget StoredRowComplementGuards.budget StoredRowComplementGuards.sumBudget
      StoredRowComplementGuards.termBudget StoredTruthCell.budget StoredTruthCell.allBudget
      StoredRunTable.anyBudget StoredForwardTableBuild.tabBudget StoredRelationalFormula.weight
    gcongr
  have hs (j : Nat) : u^j ≤ u^(j+1) := by
    simpa only [pow_succ,Nat.one_mul,Nat.mul_comm] using Nat.mul_le_mul_right (u^j) hu
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  have h4 := hs 4
  have h5 := hs 5
  norm_num at h0 h1 h2 h3 h4 h5
  rw [diagonal] at hm
  change envelope n p B K ≤ 953*u^6
  linarith only [hm,h0,h1,h2,h3,h4,h5]

theorem budget_bound (n B K : Nat) : budget n B K ≤ 953*(n+2^n+B+K+1)^6 :=
  (covers n B K).trans (envelope_polynomial n (2^n) B K)
theorem bound {R : Nat → Type} {P : Type} {n : Nat} (A : StoredRelationalRow.Row R P n)
    (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (build A).2 ≤ 953*(n+2^n+B+K+1)^6 :=
  (StoredRowComplementCompiler.bound A B K h).trans (budget_bound n B K)
theorem difference_bound {R : Nat → Type} {P : Type} {n m : Nat}
    (A : StoredRelationalRow.Row R P n) (B : StoredRelationalRow.Row R P m)
    (G K : Nat) (h : StoredRowTransport.Bounds B G K) :
    (StoredRowDifference.build A B).2 ≤
      2+953*(m+2^m+G+K+1)^6+141*(n+2^m+2)^6 := by
  have hd := StoredRowDifference.bound A B G K h
  have hc := budget_bound m G K
  have hi := StoredRowIntersection.budget_polynomial n (2^m+1)
  simp only [StoredRowDifference.budget] at hd
  have he : n+(2^m+1)+1 = n+2^m+2 := by omega
  rw [he] at hi
  omega
end NSSE.StoredRowComplementBound
