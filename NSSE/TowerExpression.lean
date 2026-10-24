import NSSE.DirectRankFormulaTower

namespace NSSE.TowerExpression
open DirectRankStateTower DirectRankFormulaTower

theorem height_mono (k l x : Nat) (h : k ≤ l) : tower k x ≤ tower l x := by
  induction h with
  | refl => rfl
  | step h ih => exact ih.trans (self_le_exp _)

theorem double_step (k x : Nat) : 2*tower (k+1) x ≤ tower (k+1) (x+1) := by
  induction k with
  | zero => simp only [tower,pow_succ]; omega
  | succ k ih =>
    have hp : 1 ≤ tower (k+1) x := by simp only [tower]; exact Nat.one_le_pow _ _ (by decide)
    have h := exp_mono (show tower (k+1) x+1 ≤ tower (k+1) (x+1) by omega)
    simpa only [tower,pow_succ,Nat.mul_comm] using h

theorem square_step (k x : Nat) (hk : 2 ≤ k) : tower k x*tower k x ≤ tower k (x+1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := exp_mono (double_step j x)
  rw [two_mul,pow_add] at h
  simpa only [Nat.add_comm 2 j,tower] using h

theorem power_step (k x c : Nat) (hk : 2 ≤ k) : (tower k x)^c ≤ tower k (x+c) := by
  induction c with
  | zero =>
    simp only [pow_zero,Nat.add_zero]
    exact (show 1 ≤ tower 1 x from Nat.one_le_pow _ _ (by decide)).trans (height_mono 1 k x (by omega))
  | succ c ih =>
    have hm := Nat.mul_le_mul ih (tower_mono k (show x ≤ x+c by omega))
    have hs := square_step k (x+c) hk
    simpa only [pow_succ,Nat.add_assoc] using hm.trans hs

inductive Expr where
  | const : Nat → Expr
  | var : Fin 3 → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | powNat : Expr → Nat → Expr
  | exp : Expr → Expr
  | raise : Expr → Expr → Expr
instance (n : Nat) : OfNat Expr n := ⟨.const n⟩
instance : Add Expr := ⟨.add⟩
instance : Mul Expr := ⟨.mul⟩
instance : Pow Expr Nat := ⟨.powNat⟩
def eval (v : Fin 3 → Nat) : Expr → Nat
  | .const n => n
  | .var i => v i
  | .add a b => eval v a+eval v b
  | .mul a b => eval v a*eval v b
  | .powNat a n => eval v a^n
  | .exp a => 2^eval v a
  | .raise a b => eval v a^eval v b

def height : Expr → Nat
  | .const _ | .var _ => 2
  | .add a b | .mul a b => max (height a) (height b)
  | .powNat a _ => height a
  | .exp a => height a+1
  | .raise a b => max (height a) (height b)+1

def weight : Expr → Nat
  | .const n => n
  | .var _ => 0
  | .add a b | .mul a b | .raise a b => max (weight a) (weight b)+1
  | .powNat a n => weight a+n
  | .exp a => weight a

theorem height_ge (e : Expr) : 2 ≤ height e := by
  induction e <;> simp_all [height] <;> omega

theorem lift_bound (a b : Expr) (v : Fin 3 → Nat) (x : Nat)
    (ha : eval v a ≤ tower (height a) (x+weight a)) :
    eval v a ≤ tower (max (height a) (height b)) (x+max (weight a) (weight b)) :=
  ha.trans ((height_mono _ _ _ (Nat.le_max_left _ _)).trans (tower_mono _ (by omega)))

theorem bound (e : Expr) (v : Fin 3 → Nat) (x : Nat) (hv : ∀ i, v i ≤ x) :
    eval v e ≤ tower (height e) (x+weight e) := by
  induction e with
  | const n => exact (show n ≤ x+n by omega).trans (height_mono 0 2 (x+n) (by decide))
  | var i => exact (hv i).trans (height_mono 0 2 x (by decide))
  | add a b ha hb =>
    have h1 := lift_bound a b v x ha
    have h2 := lift_bound b a v x hb
    rw [Nat.max_comm (height b),Nat.max_comm (weight b)] at h2
    have hk := height_ge a
    obtain ⟨k,hk'⟩ := Nat.exists_eq_add_of_le (show 1 ≤ max (height a) (height b) by omega)
    have hs := double_step k (x+max (weight a) (weight b))
    rw [Nat.add_comm 1 k] at hk'
    rw [← hk'] at hs
    simp only [eval,height,weight,← Nat.add_assoc]
    omega
  | mul a b ha hb =>
    have h1 := lift_bound a b v x ha
    have h2 := lift_bound b a v x hb
    rw [Nat.max_comm (height b),Nat.max_comm (weight b)] at h2
    exact (Nat.mul_le_mul h1 h2).trans (square_step _ _ (by have h := height_ge a; omega))
  | powNat a n ha =>
    have h := (Nat.pow_le_pow_left ha n).trans (power_step _ _ n (height_ge a))
    simpa only [eval,height,weight,Nat.add_assoc] using h
  | exp a ha => exact exp_mono ha
  | raise a b ha hb =>
    have h1 := lift_bound a b v x ha
    have h2 := lift_bound b a v x hb
    rw [Nat.max_comm (height b),Nat.max_comm (weight b)] at h2
    have hm := (Nat.mul_le_mul h1 h2).trans (square_step _ _ (by have h := height_ge a; omega))
    exact (pow_exp (self_le_exp (eval v a)) (eval v b)).trans (exp_mono hm)
end NSSE.TowerExpression
