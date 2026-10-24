import NSSE.StoredRelationalElimination

/-! Stored reflexive reachability with all construction calls counted. -/
namespace NSSE.StoredRelationalReachability
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalClosure FiniteValuationLookup
variable {R : Nat → Type} {P : Type} {n : Nat}

def literal : Bool → Data R P 0 × Nat
  | false => (.falsum,1)
  | true => (.imp .falsum .falsum,3)
theorem literal_qf (b : Bool) : (denote (literal (R := R) (P := P) b).1).IsQF := by
  cases b
  · exact .falsum
  · exact .imp .falsum .falsum
theorem literal_shape (b : Bool) :
    (literal (R := R) (P := P) b).2 ≤ 3 ∧ nodes (literal (R := R) (P := P) b).1 ≤ 3 ∧
    arity (literal (R := R) (P := P) b).1 = 0 := by
  cases b <;> simp [literal,nodes,arity]

def edge (W : Fin n → Fin n → Package R P × Nat) (a b : Fin n) : Package R P × Nat :=
  let e := equalNat a.val b.val
  let t := literal (R := R) (P := P) e.1
  let p := StoredRelationalPackages.atom t.1 (literal_qf _)
  let w := W a b
  let r := StoredRelationalPackages.disj p.1 w.1
  (r.1,5+e.2+t.2+p.2+w.2+r.2)
def edgeSpec (W : Fin n → Fin n → ExistentialFormulaPackage.Package (UniformWordLowering.wordLanguage R) P)
    (a b : Fin n) :=
  ExistentialFormulaPackage.Package.disj (ExistentialFormulaPackage.Package.atom (if a=b then ⊤ else ⊥)
    (by split; exact BoundedFormula.IsQF.top; exact BoundedFormula.isQF_bot)) (W a b)
theorem edge_value (W : Fin n → Fin n → Package R P × Nat) (a b : Fin n) :
    (edge W a b).1.original = edgeSpec (fun a b => (W a b).1.original) a b := by
  have he : (equalNat a.val b.val).1 = decide (a=b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [equalNat_correct,decide_eq_true_eq,Fin.ext_iff]
  simp only [edge,StoredRelationalPackages.disj_original,StoredRelationalPackages.atom_original,he,edgeSpec]
  by_cases h : a=b <;> simp [h,literal,denote] <;> rfl

theorem edge_size (W : Fin n → Fin n → Package R P × Nat) (B : Nat)
    (hb : ∀ a b, StoredRelationalElimination.size (W a b).1 ≤ B) (a b : Fin n) :
    StoredRelationalElimination.size (edge W a b).1 ≤ B+6 := by
  rw [StoredRelationalElimination.size_value,edge_value]
  simp only [edgeSpec,ExistentialFormulaPackage.Package.nodes_disj,ExistentialFormulaPackage.Package.nodes_atom]
  have h := hb a b
  rw [StoredRelationalElimination.size_value] at h
  split <;> simp only [ExactReachabilitySize.nodes,BoundedFormula.not] <;> omega

theorem edge_arity (W : Fin n → Fin n → Package R P × Nat) (K : Nat)
    (hk : ∀ a b, arity (W a b).1.body ≤ K) (a b : Fin n) : arity (edge W a b).1.body ≤ K := by
  dsimp only [edge]
  rw [(StoredRelationalPackages.disj_shape _ _).2.2,
    (StoredRelationalPackages.atom_shape _ _).2.2,(literal_shape _).2.2]
  exact max_le (Nat.zero_le _) (hk a b)

def edgeBudget (n c B K : Nat) := 24+n+c+StoredRelationalElimination.joinBudget (B+6) K

theorem edge_bound (W : Fin n → Fin n → Package R P × Nat) (c B K : Nat)
    (hc : ∀ a b, (W a b).2 ≤ c) (hb : ∀ a b, StoredRelationalElimination.size (W a b).1 ≤ B)
    (hk : ∀ a b, arity (W a b).1.body ≤ K) (a b : Fin n) :
    (edge W a b).2 ≤ edgeBudget n c B K := by
  let e := equalNat a.val b.val
  let t := literal (R := R) (P := P) e.1
  let p := StoredRelationalPackages.atom t.1 (literal_qf _)
  have he := equalFin_bound a b
  have ht := literal_shape (R := R) (P := P) e.1
  have hp := StoredRelationalPackages.atom_bound t.1 (literal_qf _) 0 (by exact le_of_eq ht.2.2)
  have hps := StoredRelationalPackages.atom_shape t.1 (literal_qf _)
  have hsize : StoredRelationalElimination.size p.1 ≤ B+6 := by
    dsimp only [p,StoredRelationalElimination.size]
    rw [hps.2.1,hps.1]
    have hn : nodes t.1 ≤ 3 := ht.2.1
    omega
  have hpk : arity p.1.body ≤ K := by
    dsimp only [p]; rw [hps.2.2]; exact (le_of_eq ht.2.2).trans (Nat.zero_le K)
  have hs := StoredRelationalElimination.disj_bound p.1 (W a b).1 (B+6) K hsize
    ((hb a b).trans (by omega)) hpk (hk a b)
  have hw := hc a b
  change e.2 ≤ n at he
  change t.2 ≤ 3 ∧ nodes t.1 ≤ 3 ∧ arity t.1 = 0 at ht
  change p.2 ≤ 1+weight 0 1*nodes t.1 at hp
  simp only [weight] at hp
  change 5+e.2+t.2+p.2+(W a b).2+(StoredRelationalPackages.disj p.1 (W a b).1).2 ≤ _
  unfold edgeBudget
  omega

def build (W : Fin n → Fin n → Package R P × Nat) (a b : Fin n) : Package R P × Nat :=
  let e := CountedFinEnumeration.enumerate n
  let r := StoredRelationalElimination.build (edge W) e.1 a b
  (r.1,1+e.2+r.2)
theorem value (W : Fin n → Fin n → Package R P × Nat) (a b : Fin n) :
    (build W a b).1.original = ExistentialRowNonempty.reachPackage (fun a b => (W a b).1.original) a b := by
  simp only [build,StoredRelationalElimination.value,CountedFinEnumeration.value,edge_value,
    edgeSpec,ExistentialRowNonempty.reachPackage]
def budget (n c B K : Nat) :=
  1+(n+1)^2+StoredRelationalElimination.budget (edgeBudget n c B K) (B+6) K n
theorem bound (W : Fin n → Fin n → Package R P × Nat) (c B K : Nat)
    (hc : ∀ a b, (W a b).2 ≤ c) (hb : ∀ a b, StoredRelationalElimination.size (W a b).1 ≤ B)
    (hk : ∀ a b, arity (W a b).1.body ≤ K) (a b : Fin n) :
    (build W a b).2 ≤ budget n c B K := by
  have he := CountedFinEnumeration.bound n
  have hr := StoredRelationalElimination.bound (edge W) (edgeBudget n c B K) (B+6) K
    (edge_bound W c B K hc hb hk) (edge_size W B hb) (edge_arity W K hk)
    (CountedFinEnumeration.enumerate n).1 a b
  rw [CountedFinEnumeration.value,List.length_finRange] at hr
  simp only [build,budget,CountedFinEnumeration.value]
  omega
theorem size_bound (W : Fin n → Fin n → Package R P × Nat) (B : Nat)
    (hb : ∀ a b, StoredRelationalElimination.size (W a b).1 ≤ B) (a b : Fin n) :
    StoredRelationalElimination.size (build W a b).1+4 ≤ (B+10)*3^n := by
  have he : ∀ a b, ExactReachabilitySize.nodes (edge W a b).1.original.toFormula ≤ B+6 := by
    intro a b; rw [← StoredRelationalElimination.size_value]; exact edge_size W B hb a b
  have h := StoredRelationalElimination.size_bound (edge W) (B+6) he
    (CountedFinEnumeration.enumerate n).1 a b
  rw [← StoredRelationalElimination.size_value,CountedFinEnumeration.value,List.length_finRange] at h
  simpa only [build,CountedFinEnumeration.value,Nat.add_assoc] using h

theorem arity_bound (W : Fin n → Fin n → Package R P × Nat) (K : Nat)
    (hk : ∀ a b, arity (W a b).1.body ≤ K) (a b : Fin n) :
    arity (build W a b).1.body ≤ K :=
  StoredRelationalElimination.arity_bound (edge W) K (edge_arity W K hk) _ a b
end NSSE.StoredRelationalReachability
