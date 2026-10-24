import NSSE.StoredRelationArrayPackage

/-! Actual array atom callbacks for stored signed scalar lowering. -/
namespace NSSE.StoredArraySignedAtoms
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {k c q T : Nat} {ns : Fin k → Nat}

def index : Empty ⊕ Fin q → Fin q × Nat
  | .inl e => nomatch e
  | .inr i => (i,1)
theorem index_bound (x : Empty ⊕ Fin q) : (index x).2 ≤ 1 := by cases x with | inl e => cases e | inr i => rfl
theorem arity_two {a : Nat} (r : UnifiedBlockPresentation.Rel ns c a) : a ≤ 2 := by
  cases r with
  | row i r => cases r <;> decide
  | candidate r => cases r <;> decide
  | noA => decide

def falsum (positive : Bool) : StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let f := StoredRelationalReachability.literal (!positive)
  let a := StoredRelationalPackages.atom f.1 (StoredRelationalReachability.literal_qf _)
  (a.1,2+f.2+a.2)
theorem falsum_shape (positive : Bool) :
    (falsum (R := R) (P := P) (q := q) (T := T) positive).2 ≤ 22 ∧
    StoredRelationalElimination.size (falsum (R := R) (P := P) (q := q) (T := T) positive).1 ≤ 3 ∧
    arity (falsum (R := R) (P := P) (q := q) (T := T) positive).1.body = 0 := by
  have hl := StoredRelationalReachability.literal_shape (R := R) (P := Params P q T) (!positive)
  have ha := StoredRelationalPackages.atom_shape
    (StoredRelationalReachability.literal (R := R) (P := Params P q T) (!positive)).1 (StoredRelationalReachability.literal_qf _)
  have hc := StoredRelationalPackages.atom_bound
    (StoredRelationalReachability.literal (R := R) (P := Params P q T) (!positive)).1 (StoredRelationalReachability.literal_qf _) 0 (by omega)
  simp only [weight] at hc
  simp only [falsum,StoredRelationalElimination.size]
  omega

def equal (zero one : P) (x y : Empty ⊕ Fin q) (positive : Bool) :
    StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let a := index x
  let b := index y
  let f := StoredArrayEquality.package zero one q T a.1 b.1 positive
  (f.1,3+a.2+b.2+f.2)
def equalBudget (q T : Nat) := 10+StoredArrayEquality.matrixBudget q T+5*(5+24*T)
theorem equal_bound (zero one : P) (x y : Empty ⊕ Fin q) (positive : Bool) :
    (equal (R := R) (T := T) zero one x y positive).2 ≤ equalBudget q T := by
  have hx := index_bound x
  have hy := index_bound y
  have hf := StoredArrayEquality.package_bound (R := R) (T := T) zero one (index x).1 (index y).1 positive
  simp only [equal,equalBudget]; omega

theorem equality_shape (zero one : P) (i j : Fin q) (positive : Bool) :
    StoredRelationalElimination.size (StoredArrayEquality.package (R := R) zero one q T i j positive).1 ≤ 5+24*T ∧
    arity (StoredArrayEquality.package (R := R) zero one q T i j positive).1.body = 0 := by
  have ha := StoredRelationalPackages.atom_shape (StoredArrayEquality.compile (R := R) one q T i j positive).1
    (StoredArrayEquality.compile_qf zero one i j positive)
  have hn := StoredArrayEquality.compile_nodes (R := R) (T := T) zero one i j positive
  have hk := StoredArrayEquality.compile_arity (R := R) (T := T) one i j positive
  simp only [StoredArrayEquality.package,StoredRelationalElimination.size]
  omega

def rel (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    {a : Nat} (r : UnifiedBlockPresentation.Rel ns c a) (xs : StoredRelationTuple.Data (Empty ⊕ Fin q) a) (positive : Bool) :
    StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let args := StoredRelationTuple.map index xs
  let f := StoredRelationArrayPackage.build rows C seed last zero one q T r args.1 positive
  (f.1,2+args.2+f.2)

def atoms (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P) :
    StoredSignedLowering.Atoms (UnifiedBlockPresentation.Rel ns c) R Empty (Params P q T) q where
  falsum := falsum
  equal := equal zero one
  rel _ r xs p := rel rows C seed last zero one r xs p

def costBudget (ns : Fin k → Nat) (c q T B K : Nat) :=
  30+equalBudget q T+StoredRelationArrayPackage.budget ns c q T B K
def sizeBudget (ns : Fin k → Nat) (c T B : Nat) :=
  8+24*T+StoredRelationArrayPackage.sizeBudget ns c T B

theorem bounds (rows : StoredRelationArrayPackage.Family R P ns) (C : Row R P c) (seed last zero one : P)
    (B K : Nat) (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read rows i).1 B K)
    (hc : StoredRowTransport.Bounds C B K) :
    StoredSignedLowering.Bounds (atoms (q := q) (T := T) rows C seed last zero one)
      (costBudget ns c q T B K) (sizeBudget ns c T B) K := by
  constructor
  · intro p
    have h := falsum_shape (R := R) (P := P) (q := q) (T := T) p
    simp only [atoms,costBudget,sizeBudget]; omega
  · intro x y p
    have hb := equal_bound (R := R) (T := T) zero one x y p
    have hs := equality_shape (R := R) (T := T) zero one (index x).1 (index y).1 p
    refine ⟨?_,?_,?_⟩
    · change (equal zero one x y p).2 ≤ _; unfold costBudget; omega
    · change StoredRelationalElimination.size (equal zero one x y p).1 ≤ _
      simp only [equal,sizeBudget]; omega
    · change arity (equal zero one x y p).1.body ≤ K
      simp only [equal,hs.2]; omega
  · intro a r xs p
    have ha := StoredRelationTuple.map_bound index xs 1 index_bound
    have hn := arity_two r
    have hb := StoredRelationArrayPackage.bound (T := T) rows C seed last zero one r (StoredRelationTuple.map index xs).1 p B K hr hc
    have hs := StoredRelationArrayPackage.shape (T := T) rows C seed last zero one r (StoredRelationTuple.map index xs).1 p B K hr hc
    refine ⟨?_,?_,hs.2⟩
    · change (rel rows C seed last zero one r xs p).2 ≤ _
      simp only [rel,costBudget]; omega
    · change StoredRelationalElimination.size (rel rows C seed last zero one r xs p).1 ≤ _
      simp only [rel,sizeBudget]; omega
end NSSE.StoredArraySignedAtoms
