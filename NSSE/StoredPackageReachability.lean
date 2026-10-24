import NSSE.StoredPackageElimination

/-! Counted reflexive edges and finite-state package reachability. The
supplied edge generator has a counter; all recursive calls are charged. -/
namespace NSSE.StoredPackageReachability
open FirstOrder FirstOrder.Language ExplicitUnaryTableLanguage ExactReachabilitySize
open ExistentialFormulaPackage FiniteValuationLookup
variable {P : Type} {n : Nat}

def literal : Bool → language.Formula P × Nat
  | false => (.falsum,1)
  | true => (.imp .falsum .falsum,3)
theorem literal_value (b : Bool) : (literal (P := P) b).1 = truth b := by cases b <;> rfl
theorem literal_bound (b : Bool) : (literal (P := P) b).2 ≤ 3 := by cases b <;> simp [literal]
theorem literal_nodes (b : Bool) : nodes (truth (P := P) b) ≤ 3 := by cases b <;> simp [truth,nodes]

def edge (W : Fin n → Fin n → Package language P × Nat) (a b : Fin n) : Package language P × Nat :=
  let e := equalNat a.val b.val
  let t := literal (P := P) e.1
  let p := StoredPackageConstruction.atom t.1 (by rw [literal_value]; exact truth_qf _)
  let w := W a b
  let r := StoredPackageConstruction.disj p.1 w.1
  (r.1,5+e.2+t.2+p.2+w.2+r.2)

def edgeSpec (W : Fin n → Fin n → Package language P) (a b : Fin n) : Package language P :=
  Package.disj (Package.atom (if a=b then ⊤ else ⊥)
    (by split; exact BoundedFormula.IsQF.top; exact BoundedFormula.isQF_bot)) (W a b)

theorem edge_value (W : Fin n → Fin n → Package language P × Nat) (a b : Fin n) :
    (edge W a b).1 = edgeSpec (fun a b => (W a b).1) a b := by
  have he : (equalNat a.val b.val).1 = decide (a=b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [equalNat_correct,decide_eq_true_eq,Fin.ext_iff]
  simp only [edge,StoredPackageConstruction.disj_value,StoredPackageConstruction.atom_value,literal_value,he,edgeSpec]
  by_cases h : a=b <;> simp [h,truth]

theorem edge_size (W : Fin n → Fin n → Package language P × Nat) (B : Nat)
    (hb : ∀ a b, nodes (W a b).1.toFormula ≤ B) (a b : Fin n) :
    nodes (edge W a b).1.toFormula ≤ B+6 := by
  rw [edge_value]
  simp only [edgeSpec,Package.nodes_disj,Package.nodes_atom]
  have h := hb a b
  split <;> simp only [nodes,BoundedFormula.not] <;> omega

theorem edge_bound (W : Fin n → Fin n → Package language P × Nat) (c B : Nat)
    (hc : ∀ a b, (W a b).2 ≤ c) (hb : ∀ a b, nodes (W a b).1.toFormula ≤ B) (a b : Fin n) :
    (edge W a b).2 ≤ 64+n+c+11*B := by
  let e := equalNat a.val b.val
  let t := literal (P := P) e.1
  let p := StoredPackageConstruction.atom t.1 (by rw [literal_value]; exact truth_qf _)
  have he := equalFin_bound a b
  have ht := literal_bound (P := P) e.1
  have hn := literal_nodes (P := P) e.1
  have hp := StoredPackageConstruction.atom_bound t.1 (by rw [literal_value]; exact truth_qf _)
  have hw := hc a b
  have hs := StoredPackageConstruction.disj_bound p.1 (W a b).1
  have hwb := (StoredPackageElimination.parts (W a b).1 B (hb a b)).1
  have hpn : nodes p.1.body ≤ 3 := by
    dsimp only [p]
    rw [StoredPackageConstruction.atom_value]
    simpa only [Package.atom,nodes_relabel,t,literal_value] using hn
  have hpv : p.1.vars = 0 := by simp only [p,StoredPackageConstruction.atom_value,Package.atom]
  have hz : p.1.vars*nodes (W a b).1.body = 0 := by rw [hpv]; omega
  have hs' : (StoredPackageConstruction.disj p.1 (W a b).1).2 ≤ 34+11*B := by
    apply hs.trans
    nlinarith only [hpn,hwb,hpv,hz]
  change (StoredPackageConstruction.atom t.1 _).2 ≤ _ at hp
  have htn : nodes t.1 ≤ 3 := by simpa only [t,literal_value] using hn
  change e.2 ≤ n at he
  change t.2 ≤ 3 at ht
  change p.2 ≤ 1+7*nodes t.1 at hp
  change 5+e.2+t.2+p.2+(W a b).2+(StoredPackageConstruction.disj p.1 (W a b).1).2 ≤ _
  omega

def build (W : Fin n → Fin n → Package language P × Nat) (a b : Fin n) : Package language P × Nat :=
  let e := CountedFinEnumeration.enumerate n
  let r := StoredPackageElimination.build (edge W) e.1 a b
  (r.1,1+e.2+r.2)
theorem value (W : Fin n → Fin n → Package language P × Nat) (a b : Fin n) :
    (build W a b).1 = ExistentialRowNonempty.reachPackage (fun a b => (W a b).1) a b := by
  simp only [build,StoredPackageElimination.value,CountedFinEnumeration.value,edge_value,
    edgeSpec,ExistentialRowNonempty.reachPackage]

def budget (n c B : Nat) :=
  1+(n+1)^2+StoredPackageElimination.budget (64+n+c+11*B) (B+6) n

theorem bound (W : Fin n → Fin n → Package language P × Nat) (c B : Nat)
    (hc : ∀ a b, (W a b).2 ≤ c) (hb : ∀ a b, nodes (W a b).1.toFormula ≤ B) (a b : Fin n) :
    (build W a b).2 ≤ budget n c B := by
  have he := CountedFinEnumeration.bound n
  have hr := StoredPackageElimination.bound (edge W) (64+n+c+11*B) (B+6)
    (edge_bound W c B hc hb) (edge_size W B hb) (CountedFinEnumeration.enumerate n).1 a b
  rw [CountedFinEnumeration.value,List.length_finRange] at hr
  simp only [build,budget,CountedFinEnumeration.value]
  omega
end NSSE.StoredPackageReachability
