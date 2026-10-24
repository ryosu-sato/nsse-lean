import NSSE.CountedSubtypeSupport

/-! Unary arithmetic and rule construction. The recursive arithmetic is
charged; meta-counter arithmetic and input child lookup remain separate. -/
namespace NSSE.CountedSupportRule
open SubtypeConstraints
variable {n d : Nat}

def add : Nat → Nat → Nat × Nat
  | 0, b => (b,1)
  | a+1, b => let r := add a b; (r.1+1,r.2+1)
theorem add_value (a b : Nat) : (add a b).1 = a+b := by
  induction a <;> simp [add, *, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
theorem add_cost (a b : Nat) : (add a b).2 = a+1 := by
  induction a <;> simp [add, *]
def mul (a : Nat) : Nat → Nat × Nat
  | 0 => (0,1)
  | b+1 => let r := mul a b; let s := add a r.1; (s.1,1+r.2+s.2)
theorem mul_value (a b : Nat) : (mul a b).1 = a*b := by
  induction b <;> simp [mul, add_value, *, Nat.mul_succ, Nat.add_comm]
theorem mul_cost (a b : Nat) : (mul a b).2 = 1+b*(a+2) := by
  induction b with
  | zero => simp [mul]
  | succ b ih => simp only [mul, add_cost, ih]; ring

def pair (x y : Fin n) : Nat × Nat :=
  let m := mul n x.val
  let a := add y.val m.1
  (a.1,1+m.2+a.2)
theorem pair_value (x y : Fin n) : (pair x y).1 = FiniteSubtypeSupport.pairId x y := by
  simp [pair, mul_value, add_value, FiniteSubtypeSupport.pairId, finProdFinEquiv]
def pairBudget (n : Nat) := 3+n*(n+2)+n
theorem pair_bound (x y : Fin n) : (pair x y).2 ≤ pairBudget n := by
  have hx := Nat.mul_le_mul_right (n+2) (Nat.le_of_lt x.isLt)
  have hy := y.isLt
  simp only [pair, mul_cost, add_cost, pairBudget]
  omega

def trans (x y z : Fin n) : HornRule × Nat :=
  let p := pair x z
  let a := pair x y
  let b := pair y z
  (⟨p.1,[a.1,b.1]⟩,4+p.2+a.2+b.2)
theorem trans_value (x y z : Fin n) : (trans x y z).1 = FiniteSubtypeSupport.transRule x y z := by
  simp only [trans, pair_value, FiniteSubtypeSupport.transRule]
theorem trans_bound (x y z : Fin n) : (trans x y z).2 ≤ 4+3*pairBudget n := by
  have h1 := pair_bound x z
  have h2 := pair_bound x y
  have h3 := pair_bound y z
  simp only [trans]; omega

def decomp (a b : BoundLiteral n d) (i : Fin d) : HornRule × Nat :=
  let p := pair (a.2 i) (b.2 i)
  let c := pair a.1 b.1
  (⟨p.1,[c.1]⟩,3+p.2+c.2)
theorem decomp_value (a b : BoundLiteral n d) (i : Fin d) :
    (decomp a b i).1 = FiniteSubtypeSupport.decompRule a b i := by
  simp only [decomp, pair_value, FiniteSubtypeSupport.decompRule]
theorem decomp_bound (a b : BoundLiteral n d) (i : Fin d) :
    (decomp a b i).2 ≤ 3+2*pairBudget n := by
  have h1 := pair_bound (a.2 i) (b.2 i)
  have h2 := pair_bound a.1 b.1
  simp only [decomp]; omega
end NSSE.CountedSupportRule
