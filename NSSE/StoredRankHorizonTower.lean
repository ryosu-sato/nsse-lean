import NSSE.StoredRankCostHorizon
import NSSE.TowerExpression

/-! Tower bounds for the horizon envelopes of the stored rank recursion, in
terms of one number `M` dominating all initial parameters and the horizon.
`rowLimit`, `rowCount`, `stepExp` and the lifted node bound are single
exponentials `2^{poly(M)}`; `candBound`, `cleanedBound` and `candNodes` are
double exponentials `tower 2 (poly(M))`.  This is the stored counterpart of
`DirectRankStateTower`. -/
namespace NSSE.StoredRankHorizonTower
open StoredRankHorizon DirectRankStateTower DirectRankFormulaTower

/-! ### Elementary tools -/

theorem pow_le_two_pow (a e : Nat) (ha : a ≤ 2^e) (n : Nat) : a^n ≤ 2^(e*n) := pow_exp ha n

theorem tower2_pos (x : Nat) : 1 ≤ tower 2 x := Nat.one_le_pow _ _ (by decide)

/-- Multiplying a double exponential by `2^a` costs `a+1` in the argument. -/
theorem tower2_mul_exp (x a : Nat) : tower 2 x*2^a ≤ tower 2 (x+a+1) := by
  change 2^(2^x)*2^a ≤ 2^(2^(x+a+1))
  rw [← pow_add]
  apply exp_mono
  have h1 := exp_add_le x a
  have h2 : 2^(x+a) ≤ 2^(x+a+1) := exp_mono (by omega)
  have h3 : 2^(x+a)+2^(x+a) = 2^(x+a+1) := by rw [pow_succ]; ring
  omega

theorem exp_le_tower2 (e x : Nat) (h : e ≤ x) : 2^e ≤ tower 2 x := by
  change 2^e ≤ 2^(2^x)
  exact exp_mono (h.trans (self_le_exp x))

theorem le_tower2 (a x : Nat) (h : a ≤ x) : a ≤ tower 2 x :=
  h.trans ((self_le_exp x).trans (exp_mono (self_le_exp x)))

/-! ### The horizon constants -/

/-- `rowLimit N H ≤ 2^(3M+1)`. -/
theorem rowLimit_le (M N H : Nat) (hN : N ≤ M) (hH : H ≤ M) : rowLimit N H ≤ 2^(3*M+1) := by
  unfold rowLimit
  have h4 : 4^H = 2^(2*H) := by rw [pow_mul]; rfl
  rw [h4]
  have h1 : N+1 ≤ 2^(M+1) := by
    have := self_le_exp (M+1); omega
  have h2 : 2^(2*H) ≤ 2^(2*M) := exp_mono (by omega)
  calc (N+1)*2^(2*H) ≤ 2^(M+1)*2^(2*M) := Nat.mul_le_mul h1 h2
    _ = 2^(3*M+1) := by rw [← pow_add]; congr 1; ring

def countExp (M : Nat) := M+M*(4*(3*M+1)+2)

/-- `rowCount k N H ≤ 2^(countExp M)`. -/
theorem rowCount_le (M k N H : Nat) (hk : k ≤ M) (hN : N ≤ M) (hH : H ≤ M) :
    rowCount k N H ≤ 2^(countExp M) := by
  unfold rowCount countExp
  have hr := rowLimit_le M N H hN hH
  have hp : (rowLimit N H)^4 ≤ 2^((3*M+1)*4) := pow_exp hr 4
  have hf : 2*(rowLimit N H)^4+1 ≤ 2^(4*(3*M+1)+2) := by
    have h1 : 1 ≤ 2^((3*M+1)*4) := Nat.one_le_pow _ _ (by decide)
    have : 2^(4*(3*M+1)+2) = 4*2^((3*M+1)*4) := by
      rw [show 4*(3*M+1)+2 = (3*M+1)*4+2 by ring, pow_add]; ring
    omega
  have hfH : (2*(rowLimit N H)^4+1)^H ≤ 2^((4*(3*M+1)+2)*M) := by
    calc (2*(rowLimit N H)^4+1)^H ≤ (2^(4*(3*M+1)+2))^H := Nat.pow_le_pow_left hf H
      _ ≤ (2^(4*(3*M+1)+2))^M := Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by decide)) hH
      _ = 2^((4*(3*M+1)+2)*M) := by rw [← pow_mul]
  have hk' : k ≤ 2^M := hk.trans (self_le_exp M)
  calc k*(2*(rowLimit N H)^4+1)^H ≤ 2^M*2^((4*(3*M+1)+2)*M) := Nat.mul_le_mul hk' hfH
    _ = 2^(M+M*(4*(3*M+1)+2)) := by rw [← pow_add]; congr 1; ring

def stepExpExp (M : Nat) := 3*M+1+2+countExp M+1

/-- `stepExp k N H ≤ 2^(stepExpExp M)`. -/
theorem stepExp_le (M k N H : Nat) (hk : k ≤ M) (hN : N ≤ M) (hH : H ≤ M) :
    stepExp k N H ≤ 2^(stepExpExp M) := by
  unfold stepExp stepExpExp
  have hr := rowLimit_le M N H hN hH
  have hc := rowCount_le M k N H hk hN hH
  have h3 : 3*rowLimit N H+1 ≤ 2^(3*M+1+2) := by
    have h1 : 1 ≤ 2^(3*M+1) := Nat.one_le_pow _ _ (by decide)
    have : 2^(3*M+1+2) = 4*2^(3*M+1) := by rw [pow_add]; ring
    omega
  have hm := Nat.mul_le_mul h3 hc
  rw [← pow_add] at hm
  have h1 : 1 ≤ 2^(3*M+1+2+countExp M) := Nat.one_le_pow _ _ (by decide)
  rw [pow_succ]
  omega

def candExp (M : Nat) := M+stepExpExp M+2

/-- `candBound k N c H ≤ tower 2 (candExp M)`. -/
theorem candBound_le (M k N c H : Nat) (hk : k ≤ M) (hN : N ≤ M) (hc : c ≤ M) (hH : H ≤ M) :
    candBound k N c H ≤ tower 2 (candExp M) := by
  unfold candBound candExp
  have hs := stepExp_le M k N H hk hN hH
  have hc1 : c+1 ≤ 2^(M+1) := by have := self_le_exp (M+1); omega
  have hHs : H*stepExp k N H ≤ 2^(M+stepExpExp M) := by
    rw [pow_add]; exact Nat.mul_le_mul (hH.trans (self_le_exp M)) hs
  have hsum : M+1+2^(M+stepExpExp M) ≤ 2^(M+stepExpExp M+2) := by
    have h1 := self_le_exp (M+1)
    have h2 : 2^(M+1) ≤ 2^(M+stepExpExp M) := exp_mono (by unfold stepExpExp; omega)
    have h3 : 2^(M+stepExpExp M+2) = 4*2^(M+stepExpExp M) := by rw [pow_add]; ring
    omega
  calc (c+1)*2^(H*stepExp k N H) ≤ 2^(M+1)*2^(2^(M+stepExpExp M)) :=
        Nat.mul_le_mul hc1 (exp_mono hHs)
    _ = 2^(M+1+2^(M+stepExpExp M)) := by rw [← pow_add]
    _ ≤ 2^(2^(M+stepExpExp M+2)) := exp_mono hsum

def cleanedExp (M : Nat) := candExp M+stepExpExp M+1

theorem cleanedBound_le (M k N c H : Nat) (hk : k ≤ M) (hN : N ≤ M) (hc : c ≤ M) (hH : H ≤ M) :
    cleanedBound k N c H ≤ tower 2 (cleanedExp M) := by
  unfold cleanedBound cleanedExp
  have h1 := candBound_le M k N c H hk hN hc hH
  have h2 := stepExp_le M k N H hk hN hH
  calc candBound k N c H*2^(stepExp k N H) ≤ tower 2 (candExp M)*2^(2^(stepExpExp M)) :=
        Nat.mul_le_mul h1 (exp_mono h2)
    _ ≤ _ := by
        change 2^(2^(candExp M))*2^(2^(stepExpExp M)) ≤ 2^(2^(candExp M+stepExpExp M+1))
        rw [← pow_add]
        exact exp_mono (add_exp le_rfl le_rfl)

def nodesExp (M : Nat) := candExp M+6

theorem tower2_ge_two (x : Nat) : 2 ≤ tower 2 x := by
  change 2 ≤ 2^(2^x)
  have h1 : 1 ≤ 2^x := Nat.one_le_pow _ _ (by decide)
  calc 2 = 2^1 := by norm_num
    _ ≤ 2^(2^x) := Nat.pow_le_pow_right (by decide) h1

theorem candNodes_le (M k N c F H : Nat) (hk : k ≤ M) (hN : N ≤ M) (hc : c ≤ M) (hF : F ≤ M) (hH : H ≤ M) :
    candNodes k N c F H ≤ tower 2 (nodesExp M) := by
  unfold candNodes nodesExp
  have h1 := candBound_le M k N c H hk hN hc hH
  have hM : M ≤ tower 2 (candExp M) := le_tower2 M _ (by unfold candExp; omega)
  have hpos := tower2_ge_two (candExp M)
  have h32 := tower2_mul_exp (candExp M) 5
  have h2 : (2:Nat)^5 = 32 := by norm_num
  rw [h2] at h32
  have hm := tower_mono 2 (show candExp M+5+1 ≤ candExp M+6 by omega)
  apply max_le
  · exact hF.trans (hM.trans (tower_mono 2 (by omega)))
  · omega

/-! ### The lifted node bound -/

/-- `increase z z` is a polynomial in `z`, hence `≤ 2^(9z+9)`... proved via
the explicit unfolding: the largest monomial is `6·z⁴`. -/
theorem increase_diag_le (z : Nat) : StoredCleanupStep.increase z z ≤ 200*(z+1)^4 := by
  unfold StoredCleanupStep.increase StoredRowComplementGuards.sizeBudget StoredRowComplementGuards.sumSize
    StoredRowComplementGuards.termSize StoredEmptyTailGuards.sizeBudget StoredEmptyTailGuards.switchSize
  nlinarith [sq_nonneg z, pow_pos (show 0 < z+1 by omega) 4, Nat.zero_le z]

theorem increase_mono_both {n n' B B' : Nat} (hn : n ≤ n') (hB : B ≤ B') :
    StoredCleanupStep.increase n B ≤ StoredCleanupStep.increase n' B' :=
  (StoredCleanupBound.increase_mono hn B).trans (increase_mono_nodes hB)

def liftedBase (M : Nat) := nodesExp M+countExp M+4*(3*M+1+M+5)+8+M+10
def liftedExp (M : Nat) := liftedBase M+3

theorem liftedEnv_le (M k N c F B H : Nat) (hk : k ≤ M) (hN : N ≤ M) (hc : c ≤ M) (hF : F ≤ M)
    (hB : B ≤ M) (hH : H ≤ M) : liftedEnv k N c F B H ≤ tower 2 (liftedExp M) := by
  unfold liftedEnv liftedExp
  have h1 := candNodes_le M k N c F H hk hN hc hF hH
  have hr := rowLimit_le M N H hN hH
  have hcnt := rowCount_le M k N H hk hN hH
  have hz : rowLimit N H ≤ 2^(3*M+1)+M+9 := by omega
  have hz' : max B 9 ≤ 2^(3*M+1)+M+9 := by have := self_le_exp (3*M+1); omega
  have hb : M+10 ≤ 2^(M+5) := by
    have := Nat.lt_two_pow_self (n := M)
    rw [pow_add]
    omega
  have ha2 : 2 ≤ 2^(3*M+1) := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^(3*M+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hzz : 2^(3*M+1)+M+9+1 ≤ 2^(3*M+1+M+5) := by
    have hm : M ≤ 2^(3*M+1)*M := Nat.le_mul_of_pos_left M (by omega)
    have h4 : 2^(3*M+1)+(M+10) ≤ 2^(3*M+1)*(M+10) := by nlinarith
    calc 2^(3*M+1)+M+9+1 = 2^(3*M+1)+(M+10) := by ring
      _ ≤ 2^(3*M+1)*(M+10) := h4
      _ ≤ 2^(3*M+1)*2^(M+5) := Nat.mul_le_mul_left _ hb
      _ = 2^(3*M+1+M+5) := by rw [← pow_add]; congr 1
  have hinc := (increase_mono_both hz hz').trans (increase_diag_le _)
  have hinc' : StoredCleanupStep.increase (rowLimit N H) (max B 9) ≤ 2^(4*(3*M+1+M+5)+8) := by
    apply hinc.trans
    have := pow_exp hzz 4
    have h200 : 200 ≤ 2^8 := by norm_num
    calc 200*(2^(3*M+1)+M+9+1)^4 ≤ 2^8*2^((3*M+1+M+5)*4) := Nat.mul_le_mul h200 this
      _ = 2^(4*(3*M+1+M+5)+8) := by rw [← pow_add]; congr 1; ring
  have hprod : rowCount k N H*StoredCleanupStep.increase (rowLimit N H) (max B 9) ≤
      2^(countExp M+(4*(3*M+1+M+5)+8)) := by
    rw [pow_add]; exact Nat.mul_le_mul hcnt hinc'
  have hB9 : max B 9 ≤ 2^(M+10) := by have := self_le_exp (M+10); omega
  have e1 : 2^(countExp M+(4*(3*M+1+M+5)+8)) ≤ tower 2 (countExp M+(4*(3*M+1+M+5)+8)) :=
    exp_le_tower2 _ _ le_rfl
  have e2 : 2^(M+10) ≤ tower 2 (M+10) := exp_le_tower2 _ _ le_rfl
  have t1 := tower_mono 2 (show nodesExp M ≤ liftedBase M by unfold liftedBase; omega)
  have t2 := tower_mono 2 (show countExp M+(4*(3*M+1+M+5)+8) ≤ liftedBase M by unfold liftedBase; omega)
  have t3 := tower_mono 2 (show M+10 ≤ liftedBase M by unfold liftedBase; omega)
  have hsum : tower 2 (liftedBase M)*4 ≤ tower 2 (liftedBase M+3) := by
    have := tower2_mul_exp (liftedBase M) 2
    have h4 : (2:Nat)^2 = 4 := by norm_num
    rw [h4] at this
    exact this
  omega

end NSSE.StoredRankHorizonTower
