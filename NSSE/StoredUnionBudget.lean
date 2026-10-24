import NSSE.StoredDFAUnions
import NSSE.ExplicitCapTerminalTower

/-! Polynomial envelopes for the actual stored union construction. A safe
product is used so that zero-state entries cannot invalidate suffix bounds. -/
namespace NSSE.StoredUnionBudget
open DirectRankStateTower DirectRankFormulaTower

def safeProduct (ns : List Nat) := (ns.map (fun n => n+1)).prod

theorem safeProduct_pos (ns : List Nat) : 1 ≤ safeProduct ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [safeProduct,List.map_cons,List.prod_cons] at *
    nlinarith

theorem prod_le (ns : List Nat) : ns.prod ≤ safeProduct ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [safeProduct,List.map_cons,List.prod_cons] at *
    exact Nat.mul_le_mul (by omega) ih

theorem tail_le (n : Nat) (ns : List Nat) : safeProduct ns ≤ safeProduct (n::ns) := by
  change safeProduct ns ≤ (n+1)*safeProduct ns
  nlinarith

theorem head_le (n : Nat) (ns : List Nat) : n ≤ safeProduct (n::ns) := by
  have h := safeProduct_pos ns
  change n ≤ (n+1)*safeProduct ns
  nlinarith

theorem product_mono {n n' m m' d d' : Nat} (hn : n ≤ n') (hm : m ≤ m') (hd : d ≤ d') :
    StoredDFAProductBuild.budget n m d ≤ StoredDFAProductBuild.budget n' m' d' := by
  unfold StoredDFAProductBuild.budget StoredDFAProductCells.stepBudget
    StoredDFAProductCells.encodeBudget StoredProductTable.budget StoredForwardTableBuild.tabBudget
  gcongr

def envelope (d k P : Nat) := StoredDFAUnions.constantBudget d+k*(1+StoredDFAProductBuild.budget P P d)

theorem budget_bound (d : Nat) (ns : List Nat) :
    StoredDFAUnions.budget d ns ≤ envelope d ns.length (safeProduct ns) := by
  induction ns with
  | nil => simp [StoredDFAUnions.budget,envelope]
  | cons n ns ih =>
    have ht := tail_le n ns
    have hp := product_mono (head_le n ns) ((prod_le ns).trans ht) (le_rfl : d ≤ d)
    have hb := product_mono ht ht (le_rfl : d ≤ d)
    have hm := Nat.mul_le_mul_left ns.length (Nat.add_le_add_left hb 1)
    simp only [StoredDFAUnions.budget,List.length_cons,envelope] at *
    nlinarith

/-- The safe product adds at most one bit per factor to a known exponential bound. -/
theorem safeProduct_exp {α : Type} (xs : List α) (f e : α → Nat)
    (h : ∀ a ∈ xs, f a ≤ 2^(e a)) :
    safeProduct (xs.map f) ≤ 2^((xs.map e).sum+xs.length) := by
  induction xs with
  | nil => simp [safeProduct]
  | cons a xs ih =>
    have hn := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    have hp : f a+1 ≤ 2^(e a+1) := by
      have : 1 ≤ 2^(e a) := Nat.one_le_pow _ _ (by decide)
      rw [pow_succ]; omega
    have hm := mul_exp hp ht
    change (f a+1)*safeProduct (xs.map f) ≤ _
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hm

/-- Exact polynomial expression for the uniform union budget. -/
def expression : PolynomialTowerEnvelope.Expr :=
  let p : PolynomialTowerEnvelope.Expr := .var 0
  let d : PolynomialTowerEnvelope.Expr := .var 1
  let k : PolynomialTowerEnvelope.Expr := .var 2
  let tab := fun n c => 2+(n+1)^2+n*(1+c)
  let table := fun n m c => 2+(n+1)^2+n*(2+tab m c+m)
  let enc := 3+p*(p+2)+p
  let step := 4+p+p+2*d+enc
  let prod := 2+p*(p+2)+enc+table p p (tab d step)+table p p (1+p+p)
  (4+tab 1 (tab d 1))+k*(1+prod)

theorem expression_value (d k P : Nat) :
    PolynomialTowerEnvelope.eval ![P,d,k,0] expression = envelope d k P := rfl

/-- Single exponential in the log-size bounds of all dimensions; no extra
exponential is introduced by the sequential union fold. -/
theorem budget_exp (d : Nat) (ns : List Nat) (x : Nat) (hx : 1 ≤ x)
    (hp : safeProduct ns ≤ 2^x) (hd : d ≤ 2^x) (hk : ns.length ≤ 2^x) :
    StoredDFAUnions.budget d ns ≤ 2^(PolynomialTowerEnvelope.weight expression*x) := by
  have h := ExplicitCapTerminalTower.eval_exp_linear expression ![safeProduct ns,d,ns.length,0] x hx (by
    intro i; fin_cases i
    · exact hp
    · exact hd
    · exact hk
    · exact Nat.zero_le _)
  rw [expression_value] at h
  exact (budget_bound d ns).trans h

end NSSE.StoredUnionBudget
