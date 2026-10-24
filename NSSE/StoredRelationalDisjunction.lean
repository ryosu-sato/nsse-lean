import NSSE.StoredRelationalPackages

/-! Counted finite disjunction of stored arbitrary-arity Packages. -/
namespace NSSE.StoredRelationalDisjunction
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalClosure
variable {R : Nat → Type} {P : Type}

def fold : List (Package R P) → Package R P × Nat
  | [] => StoredRelationalPackages.atom .falsum .falsum
  | A::as => let t := fold as; let r := StoredRelationalPackages.disj A t.1
    (r.1,1+t.2+r.2)
def original (as : List (Package R P)) :=
  (as.map Package.original).foldr ExistentialFormulaPackage.Package.disj
    (ExistentialFormulaPackage.Package.atom ⊥ BoundedFormula.isQF_bot)
theorem value (as : List (Package R P)) : (fold as).1.original = original as := by
  induction as with
  | nil => exact StoredRelationalPackages.atom_original _ _
  | cons A as ih =>
    simp only [fold,StoredRelationalPackages.disj_original,ih,original,List.map_cons,List.foldr_cons]

theorem shape (as : List (Package R P)) (V B K : Nat)
    (hv : ∀ A ∈ as, A.vars ≤ V) (hb : ∀ A ∈ as, nodes A.body ≤ B)
    (hk : ∀ A ∈ as, arity A.body ≤ K) :
    (fold as).1.vars ≤ as.length*V ∧
    nodes (fold as).1.body ≤ 1+as.length*(3+B) ∧ arity (fold as).1.body ≤ K := by
  induction as with
  | nil => simp [fold,StoredRelationalPackages.atom,rename,nodes,arity]
  | cons A as ih =>
    have ha := hv A (by simp)
    have hn := hb A (by simp)
    have hka := hk A (by simp)
    have ht := ih (fun A hA => hv A (by simp [hA]))
      (fun A hA => hb A (by simp [hA])) (fun A hA => hk A (by simp [hA]))
    have hs := StoredRelationalPackages.disj_shape A (fold as).1
    simp only [fold,List.length_cons]
    constructor
    · rw [hs.1]; nlinarith [ht.1]
    constructor
    · rw [hs.2.1]; nlinarith [ht.2.1]
    · rw [hs.2.2]; exact max_le hka ht.2.2

def stepBudget (L V B K : Nat) := V+8+weight K 2*B+weight K (V+3)*(1+L*(3+B))
def budget (L V B K : Nat) := 2+L*stepBudget L V B K

theorem fold_bound (as : List (Package R P)) (L V B K : Nat) (hl : as.length ≤ L)
    (hv : ∀ A ∈ as, A.vars ≤ V) (hb : ∀ A ∈ as, nodes A.body ≤ B)
    (hk : ∀ A ∈ as, arity A.body ≤ K) :
    (fold as).2 ≤ 2+as.length*stepBudget L V B K := by
  induction as with
  | nil => simp [fold,StoredRelationalPackages.atom,rename]
  | cons A as ih =>
    have hA := hv A (by simp)
    have hB := hb A (by simp)
    have hK := hk A (by simp)
    have hlt : as.length ≤ L := by simp only [List.length_cons] at hl; omega
    have ht := ih hlt (fun A hA => hv A (by simp [hA]))
      (fun A hA => hb A (by simp [hA])) (fun A hA => hk A (by simp [hA]))
    have hshape := shape as V B K (fun A hA => hv A (by simp [hA]))
      (fun A hA => hb A (by simp [hA])) (fun A hA => hk A (by simp [hA]))
    have hn : nodes (fold as).1.body ≤ 1+L*(3+B) := by
      apply hshape.2.1.trans
      gcongr
    have hs := StoredRelationalPackages.disj_bound A (fold as).1 K hK hshape.2.2
    have hs' : (StoredRelationalPackages.disj A (fold as).1).2 ≤
        V+7+weight K 2*B+weight K (V+3)*(1+L*(3+B)) := by
      apply hs.trans
      unfold weight
      gcongr
    simp only [fold,List.length_cons,stepBudget] at *
    nlinarith

def any (n : Nat) (f : Fin n → Package R P × Nat) : Package R P × Nat :=
  let a := CountedFinEnumeration.tabulate n f
  let b := fold a.1
  (b.1,1+a.2+b.2)
theorem any_value (n : Nat) (f : Fin n → Package R P × Nat) :
    (any n f).1.original = ExistentialRowNonempty.anyPackage n (fun i => (f i).1.original) := by
  simp only [any,value,original,CountedFinEnumeration.tabulate_value,ExistentialRowNonempty.anyPackage]
  rw [List.map_ofFn,List.ofFn_eq_map]
  rfl

theorem any_bound (n : Nat) (f : Fin n → Package R P × Nat) (c V B K : Nat)
    (hc : ∀ i, (f i).2 ≤ c) (hv : ∀ i, (f i).1.vars ≤ V)
    (hb : ∀ i, nodes (f i).1.body ≤ B) (hk : ∀ i, arity (f i).1.body ≤ K) :
    (any n f).2 ≤ 1+StoredForwardTableBuild.tabBudget n c+budget n V B K := by
  have ha := CountedFinEnumeration.tabulate_bound n f c hc
  have hlen : (CountedFinEnumeration.tabulate n f).1.length = n := by
    simp only [CountedFinEnumeration.tabulate_value,List.length_ofFn]
  have ht := fold_bound (CountedFinEnumeration.tabulate n f).1 n V B K (by omega)
    (by intro A hA; rw [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at hA
        obtain ⟨i,rfl⟩ := hA; exact hv i)
    (by intro A hA; rw [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at hA
        obtain ⟨i,rfl⟩ := hA; exact hb i)
    (by intro A hA; rw [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at hA
        obtain ⟨i,rfl⟩ := hA; exact hk i)
  rw [hlen] at ht
  simp only [any,budget,StoredForwardTableBuild.tabBudget]
  omega

theorem any_shape (n : Nat) (f : Fin n → Package R P × Nat) (V B K : Nat)
    (hv : ∀ i, (f i).1.vars ≤ V) (hb : ∀ i, nodes (f i).1.body ≤ B)
    (hk : ∀ i, arity (f i).1.body ≤ K) :
    (any n f).1.vars ≤ n*V ∧ nodes (any n f).1.body ≤ 1+n*(3+B) ∧
    arity (any n f).1.body ≤ K := by
  have hs := shape (List.ofFn (fun i => (f i).1)) V B K
    (by intro A hA; rw [List.mem_ofFn] at hA; obtain ⟨i,rfl⟩ := hA; exact hv i)
    (by intro A hA; rw [List.mem_ofFn] at hA; obtain ⟨i,rfl⟩ := hA; exact hb i)
    (by intro A hA; rw [List.mem_ofFn] at hA; obtain ⟨i,rfl⟩ := hA; exact hk i)
  dsimp only [any]
  rw [CountedFinEnumeration.tabulate_value]
  simpa only [List.length_ofFn] using hs
def closed (n : Nat) (f : Fin n → Package R P × Nat) : Data R P 0 × Nat :=
  let a := any n f
  let b := StoredRelationalClosure.build a.1
  (b.1,1+a.2+b.2)
theorem closed_value (n : Nat) (f : Fin n → Package R P × Nat) :
    denote (closed n f).1 =
      (ExistentialRowNonempty.anyPackage n (fun i => (f i).1.original)).toFormula := by
  simp only [closed,StoredRelationalClosure.build_value,any_value]
theorem closed_bound (n : Nat) (f : Fin n → Package R P × Nat) (c V B K : Nat)
    (hc : ∀ i, (f i).2 ≤ c) (hv : ∀ i, (f i).1.vars ≤ V)
    (hb : ∀ i, nodes (f i).1.body ≤ B) (hk : ∀ i, arity (f i).1.body ≤ K) :
    (closed n f).2 ≤ 4+StoredForwardTableBuild.tabBudget n c+budget n V B K+
      (5+3*K)*(1+n*(3+B))+6*(n*V) := by
  have ha := any_bound n f c V B K hc hv hb hk
  have hs := any_shape n f V B K hv hb hk
  have hclose := StoredRelationalClosure.build_bound (any n f).1 K hs.2.2
  have hb' : (StoredRelationalClosure.build (any n f).1).2 ≤
      2+(5+3*K)*(1+n*(3+B))+6*(n*V) := by
    apply hclose.trans
    gcongr
    · exact hs.2.1
    · exact hs.1
  simp only [closed]; omega
end NSSE.StoredRelationalDisjunction
