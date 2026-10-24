import NSSE.StoredPackageDisjunction

/-! Counted actual state-elimination recursion in the concrete unary language.
All three recursive branches and complete package joins are charged. -/
namespace NSSE.StoredPackageElimination
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open ExistentialFormulaPackage
variable {P : Type} {n : Nat}

theorem parts (A : Package language P) (S : Nat) (h : nodes A.toFormula ≤ S) :
    nodes A.body ≤ S ∧ A.vars ≤ S := by
  simp only [Package.toFormula,nodes_closeColumn] at h
  omega

def joinBudget (S : Nat) := 2*S^2+21*S+9
theorem conj_bound (A B : Package language P) (S : Nat)
    (ha : nodes A.toFormula ≤ S) (hb : nodes B.toFormula ≤ S) :
    (StoredPackageConstruction.conj A B).2 ≤ joinBudget S := by
  obtain ⟨ha,hv⟩ := parts A S ha
  obtain ⟨hb,_⟩ := parts B S hb
  have h := StoredPackageConstruction.conj_bound A B
  apply h.trans
  calc
    _ ≤ S+9+9*S+(11+2*S)*S := by gcongr
    _ = _ := by unfold joinBudget; ring
theorem disj_bound (A B : Package language P) (S : Nat)
    (ha : nodes A.toFormula ≤ S) (hb : nodes B.toFormula ≤ S) :
    (StoredPackageConstruction.disj A B).2 ≤ joinBudget S := by
  obtain ⟨ha,hv⟩ := parts A S ha
  obtain ⟨hb,_⟩ := parts B S hb
  have h := StoredPackageConstruction.disj_bound A B
  apply h.trans
  calc
    _ ≤ S+7+9*S+(11+2*S)*S := by gcongr
    _ ≤ _ := by unfold joinBudget; nlinarith

def build (W : Fin n → Fin n → Package language P × Nat) :
    List (Fin n) → Fin n → Fin n → Package language P × Nat
  | [],a,b => W a b
  | t::ts,a,b =>
    let x := build W ts a b
    let y := build W ts a t
    let z := build W ts t b
    let c := StoredPackageConstruction.conj y.1 z.1
    let r := StoredPackageConstruction.disj x.1 c.1
    (r.1,5+x.2+y.2+z.2+c.2+r.2)
theorem value (W : Fin n → Fin n → Package language P × Nat) (ts : List (Fin n)) (a b : Fin n) :
    (build W ts a b).1 = ExistentialRowNonempty.eliminate (fun a b => (W a b).1) ts a b := by
  induction ts generalizing a b with
  | nil => rfl
  | cons t ts ih =>
    simp only [build,StoredPackageConstruction.disj_value,StoredPackageConstruction.conj_value,ih,
      ExistentialRowNonempty.eliminate]

theorem size_bound (W : Fin n → Fin n → Package language P × Nat) (B : Nat)
    (hb : ∀ a b, nodes (W a b).1.toFormula ≤ B) (ts : List (Fin n)) (a b : Fin n) :
    nodes (build W ts a b).1.toFormula+4 ≤ (B+4)*3^ts.length := by
  rw [value]
  exact ExistentialRowNonemptySize.eliminate_le _ hb ts a b

def budget (c B l : Nat) := (c+100*(B+4)^2)*9^l

theorem bound (W : Fin n → Fin n → Package language P × Nat) (c B : Nat)
    (hc : ∀ a b, (W a b).2 ≤ c) (hb : ∀ a b, nodes (W a b).1.toFormula ≤ B)
    (ts : List (Fin n)) (a b : Fin n) : (build W ts a b).2 ≤ budget c B ts.length := by
  induction ts generalizing a b with
  | nil =>
    have h := hc a b
    simp only [build,budget,List.length_nil,pow_zero,Nat.mul_one]; omega
  | cons t ts ih =>
    let S := (B+4)*3^ts.length
    have hp : 1 ≤ 3^ts.length := Nat.one_le_pow _ _ (by decide)
    have hS : 4 ≤ S := by dsimp [S]; nlinarith
    have hx := size_bound W B hb ts a b
    have hy := size_bound W B hb ts a t
    have hz := size_bound W B hb ts t b
    change _ ≤ S at hx hy hz
    have hj := conj_bound (build W ts a t).1 (build W ts t b).1 (2*S+5) (by omega) (by omega)
    have hn : nodes (StoredPackageConstruction.conj (build W ts a t).1 (build W ts t b).1).1.toFormula ≤ 2*S+5 := by
      rw [StoredPackageConstruction.conj_value,Package.nodes_conj]; omega
    have hd := disj_bound (build W ts a b).1
      (StoredPackageConstruction.conj (build W ts a t).1 (build W ts t b).1).1 (2*S+5) (by omega) hn
    have hjd : 5+2*joinBudget (2*S+5) ≤ 100*S^2 := by unfold joinBudget; nlinarith
    have h1 := ih a b; have h2 := ih a t; have h3 := ih t b
    have he : S^2 = (B+4)^2*9^ts.length := by
      dsimp [S]
      rw [mul_pow,← pow_mul, Nat.mul_comm ts.length 2,pow_mul]
      rfl
    have ht : (build W (t::ts) a b).2 ≤ 3*budget c B ts.length+100*S^2 := by
      simp only [build]; omega
    rw [he] at ht
    apply ht.trans
    simp only [budget,List.length_cons,pow_succ,pow_zero]
    have hc0 := Nat.zero_le (c*9^ts.length)
    have hb0 := Nat.zero_le ((B+4)^2*9^ts.length)
    nlinarith only [hc0,hb0]
end NSSE.StoredPackageElimination
