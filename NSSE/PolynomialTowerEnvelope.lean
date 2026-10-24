import NSSE.DirectRankStateTower

/-! # Certified envelopes for explicit polynomial budget expressions -/

namespace NSSE.PolynomialTowerEnvelope

open DirectRankStateTower

inductive Expr where
  | const : Nat → Expr
  | var : Fin 4 → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | max : Expr → Expr → Expr
  | pow : Expr → Nat → Expr

instance (n : Nat) : OfNat Expr n := ⟨.const n⟩
instance : Add Expr := ⟨.add⟩
instance : Mul Expr := ⟨.mul⟩
instance : Max Expr := ⟨.max⟩
instance : Pow Expr Nat := ⟨.pow⟩

def eval (v : Fin 4 → Nat) : Expr → Nat
  | .const n => n
  | .var i => v i
  | .add a b => eval v a+eval v b
  | .mul a b => eval v a*eval v b
  | .max a b => max (eval v a) (eval v b)
  | .pow a n => (eval v a)^n

def weight : Expr → Nat
  | .const n => n+1
  | .var _ => 1
  | .add a b => weight a+weight b+1
  | .mul a b => weight a+weight b
  | .max a b => weight a+weight b
  | .pow a n => weight a*n+1

theorem eval_exp (e : Expr) (v : Fin 4 → Nat) (x : Nat) (hv : ∀ i, v i ≤ tower 2 x) :
    eval v e ≤ 2^(weight e*2^x) := by
  have hx : 1 ≤ 2^x := Nat.one_le_pow _ _ (by decide)
  induction e with
  | const n =>
    exact (self_le_exp n).trans (exp_mono (by change n ≤ (n+1)*2^x; nlinarith))
  | var i => simpa only [eval, weight, Nat.one_mul] using hv i
  | add a b iha ihb =>
    apply (add_exp iha ihb).trans
    apply exp_mono
    change weight a*2^x+weight b*2^x+1 ≤ (weight a+weight b+1)*2^x
    nlinarith
  | mul a b iha ihb =>
    apply (mul_exp iha ihb).trans
    apply exp_mono
    change weight a*2^x+weight b*2^x ≤ (weight a+weight b)*2^x
    nlinarith
  | max a b iha ihb =>
    apply max_le
    · apply iha.trans
      apply exp_mono
      change weight a*2^x ≤ (weight a+weight b)*2^x
      exact Nat.mul_le_mul_right _ (by omega)
    · apply ihb.trans
      apply exp_mono
      change weight b*2^x ≤ (weight a+weight b)*2^x
      exact Nat.mul_le_mul_right _ (by omega)
  | pow a n ih =>
    apply (pow_exp ih n).trans
    apply exp_mono
    change weight a*2^x*n ≤ (weight a*n+1)*2^x
    nlinarith

theorem eval_tower (e : Expr) (v : Fin 4 → Nat) (x : Nat) (hv : ∀ i, v i ≤ tower 2 x) :
    eval v e ≤ tower 2 (x+weight e) := by
  apply (eval_exp e v x hv).trans
  apply exp_mono
  have hh := mul_exp (self_le_exp (weight e)) (le_rfl : 2^x ≤ 2^x)
  simpa only [Nat.add_comm] using hh

end NSSE.PolynomialTowerEnvelope
