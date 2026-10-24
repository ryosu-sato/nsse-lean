import NSSE.StoredRelationalDisjunction

/-! Actual stored state elimination at arbitrary finite relation arities. -/
namespace NSSE.StoredRelationalElimination
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalClosure
variable {R : Nat → Type} {P : Type} {n : Nat}

def size (A : Package R P) := nodes A.body+5*A.vars
theorem size_value (A : Package R P) : size A = ExactReachabilitySize.nodes A.original.toFormula := by
  simp only [size,Package.original,ExistentialFormulaPackage.Package.toFormula,
    ExactReachabilitySize.nodes_closeColumn,denote_nodes]
theorem parts (A : Package R P) (S : Nat) (h : size A ≤ S) :
    nodes A.body ≤ S ∧ A.vars ≤ S := by unfold size at h; omega

def joinBudget (S K : Nat) := (K+1)*(2*S^2+26*S+9)
theorem conj_bound (A B : Package R P) (S K : Nat)
    (ha : size A ≤ S) (hb : size B ≤ S) (hka : arity A.body ≤ K) (hkb : arity B.body ≤ K) :
    (StoredRelationalPackages.conj A B).2 ≤ joinBudget S K := by
  obtain ⟨ha,hv⟩ := parts A S ha
  obtain ⟨hb,_⟩ := parts B S hb
  have h := StoredRelationalPackages.conj_bound A B K hka hkb
  apply h.trans
  calc
    _ ≤ S+9+weight K 2*S+weight K (S+3)*S := by unfold weight; gcongr
    _ ≤ _ := by unfold joinBudget weight; nlinarith [Nat.zero_le (K*S^2),Nat.zero_le (K*S)]
theorem disj_bound (A B : Package R P) (S K : Nat)
    (ha : size A ≤ S) (hb : size B ≤ S) (hka : arity A.body ≤ K) (hkb : arity B.body ≤ K) :
    (StoredRelationalPackages.disj A B).2 ≤ joinBudget S K := by
  obtain ⟨ha,hv⟩ := parts A S ha
  obtain ⟨hb,_⟩ := parts B S hb
  have h := StoredRelationalPackages.disj_bound A B K hka hkb
  apply h.trans
  calc
    _ ≤ S+7+weight K 2*S+weight K (S+3)*S := by unfold weight; gcongr
    _ ≤ _ := by unfold joinBudget weight; nlinarith [Nat.zero_le (K*S^2),Nat.zero_le (K*S)]

def build (W : Fin n → Fin n → Package R P × Nat) :
    List (Fin n) → Fin n → Fin n → Package R P × Nat
  | [],a,b => W a b
  | t::ts,a,b =>
    let x := build W ts a b
    let y := build W ts a t
    let z := build W ts t b
    let c := StoredRelationalPackages.conj y.1 z.1
    let r := StoredRelationalPackages.disj x.1 c.1
    (r.1,5+x.2+y.2+z.2+c.2+r.2)
theorem value (W : Fin n → Fin n → Package R P × Nat) (ts : List (Fin n)) (a b : Fin n) :
    (build W ts a b).1.original = ExistentialRowNonempty.eliminate (fun a b => (W a b).1.original) ts a b := by
  induction ts generalizing a b with
  | nil => rfl
  | cons t ts ih =>
    simp only [build,StoredRelationalPackages.disj_original,StoredRelationalPackages.conj_original,ih,
      ExistentialRowNonempty.eliminate]

theorem size_bound (W : Fin n → Fin n → Package R P × Nat) (B : Nat)
    (hb : ∀ a b, ExactReachabilitySize.nodes (W a b).1.original.toFormula ≤ B) (ts : List (Fin n)) (a b : Fin n) :
    ExactReachabilitySize.nodes (build W ts a b).1.original.toFormula+4 ≤ (B+4)*3^ts.length := by
  rw [value]
  exact ExistentialRowNonemptySize.eliminate_le _ hb ts a b

theorem arity_bound (W : Fin n → Fin n → Package R P × Nat) (K : Nat)
    (hk : ∀ a b, arity (W a b).1.body ≤ K) (ts : List (Fin n)) (a b : Fin n) :
    arity (build W ts a b).1.body ≤ K := by
  induction ts generalizing a b with
  | nil => exact hk a b
  | cons t ts ih =>
    have hc := (StoredRelationalPackages.conj_shape (build W ts a t).1 (build W ts t b).1).2.2
    have hd := (StoredRelationalPackages.disj_shape (build W ts a b).1
      (StoredRelationalPackages.conj (build W ts a t).1 (build W ts t b).1).1).2.2
    simp only [build]
    rw [hd,hc]
    exact max_le (ih a b) (max_le (ih a t) (ih t b))

def budget (c B K l : Nat) := (c+100*(K+1)*(B+4)^2)*9^l

theorem bound (W : Fin n → Fin n → Package R P × Nat) (c B K : Nat)
    (hc : ∀ a b, (W a b).2 ≤ c) (hb : ∀ a b, size (W a b).1 ≤ B)
    (hk : ∀ a b, arity (W a b).1.body ≤ K)
    (ts : List (Fin n)) (a b : Fin n) : (build W ts a b).2 ≤ budget c B K ts.length := by
  have hb' : ∀ a b, ExactReachabilitySize.nodes (W a b).1.original.toFormula ≤ B := by
    intro a b; rw [← size_value]; exact hb a b
  induction ts generalizing a b with
  | nil =>
    have h := hc a b
    simp only [build,budget,List.length_nil,pow_zero,Nat.mul_one]; omega
  | cons t ts ih =>
    let S := (B+4)*3^ts.length
    have hp : 1 ≤ 3^ts.length := Nat.one_le_pow _ _ (by decide)
    have hS : 4 ≤ S := by dsimp [S]; nlinarith
    have hx := size_bound W B hb' ts a b
    have hy := size_bound W B hb' ts a t
    have hz := size_bound W B hb' ts t b
    rw [← size_value] at hx hy hz
    change _ ≤ S at hx hy hz
    have kx := arity_bound W K hk ts a b
    have ky := arity_bound W K hk ts a t
    have kz := arity_bound W K hk ts t b
    have hj := conj_bound (build W ts a t).1 (build W ts t b).1 (2*S+5) K (by omega) (by omega) ky kz
    have hn : size (StoredRelationalPackages.conj (build W ts a t).1 (build W ts t b).1).1 ≤ 2*S+5 := by
      rw [size_value,StoredRelationalPackages.conj_original,ExistentialFormulaPackage.Package.nodes_conj]
      rw [← size_value,← size_value]; omega
    have kn : arity (StoredRelationalPackages.conj (build W ts a t).1 (build W ts t b).1).1.body ≤ K := by
      rw [(StoredRelationalPackages.conj_shape _ _).2.2]; exact max_le ky kz
    have hd := disj_bound (build W ts a b).1
      (StoredRelationalPackages.conj (build W ts a t).1 (build W ts t b).1).1 (2*S+5) K (by omega) hn kx kn
    have hbase : 5+2*(2*(2*S+5)^2+26*(2*S+5)+9) ≤ 100*S^2 := by nlinarith
    have hmul := Nat.mul_le_mul_left (K+1) hbase
    have hjd : 5+2*joinBudget (2*S+5) K ≤ 100*(K+1)*S^2 := by
      unfold joinBudget; nlinarith only [hmul,Nat.zero_le K]
    have h1 := ih a b; have h2 := ih a t; have h3 := ih t b
    have he : S^2 = (B+4)^2*9^ts.length := by
      dsimp [S]
      rw [mul_pow,← pow_mul,Nat.mul_comm ts.length 2,pow_mul]
      rfl
    have ht : (build W (t::ts) a b).2 ≤ 3*budget c B K ts.length+100*(K+1)*S^2 := by
      simp only [build]; omega
    rw [he] at ht
    apply ht.trans
    simp only [budget,List.length_cons,pow_succ]
    have hc0 := Nat.zero_le (c*9^ts.length)
    have hb0 := Nat.zero_le ((K+1)*(B+4)^2*9^ts.length)
    nlinarith only [hc0,hb0]
end NSSE.StoredRelationalElimination
