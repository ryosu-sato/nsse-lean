import NSSE.StoredBlockArrayPackage

/-! Actual stored dependent row lookup and unified relation package dispatch. -/
namespace NSSE.StoredRelationArrayPackage
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {k c q T : Nat} {ns : Fin k → Nat}

/-- Dimension certificates erase; the row data is a real stored list. -/
structure Family (R : Nat → Type) (P : Type) {k : Nat} (ns : Fin k → Nat) where
  entries : StoredRelationTuple.Data (Sigma (Row R P)) k
  dimensions : ∀ i, (StoredRelationTuple.read entries i).1.1 = ns i

def read (A : Family R P ns) (i : Fin k) : Row R P (ns i) × Nat :=
  let a := StoredRelationTuple.read A.entries i
  (cast (congrArg (Row R P) (A.dimensions i)) a.1.2,1+a.2)
theorem read_bound (A : Family R P ns) (i : Fin k) : (read A i).2 ≤ 1+k := by
  have h := StoredRelationTuple.read_bound A.entries i
  simp only [read]; omega

def Family.original (A : Family R P ns) (i : Fin k) := (read A i).1.original

def build (rows : Family R P ns) (C : Row R P c) (seed last zero one : P) (q T : Nat) :
    {a : Nat} → UnifiedBlockPresentation.Rel ns c a → StoredRelationTuple.Data (Fin q) a → Bool →
      StoredRelationalClosure.Package R (Params P q T) × Nat
  | _, .row i r, args, positive =>
    let a := read rows i
    let f := StoredBlockArrayPackage.build a.1 seed last zero one q T r args positive
    (f.1,2+a.2+f.2)
  | _, .candidate r, args, positive =>
    let f := StoredBlockArrayPackage.build C seed last zero one q T r args positive
    (f.1,1+f.2)
  | _, .noA, args, positive =>
    let f := StoredArrayAbsence.noA last zero one q T args positive
    (f.1,1+f.2)

theorem value (rows : Family R P ns) (C : Row R P c) (seed last zero one : P) {a : Nat}
    (r : UnifiedBlockPresentation.Rel ns c a) (args : StoredRelationTuple.Data (Fin q) a) (positive : Bool) :
    (build rows C seed last zero one q T r args positive).1.original.toFormula =
      (ArrayAtomExistentialPackages.relation rows.original C.original (fun i => (read rows i).1.qfree) C.qfree
        seed last zero one q T r (fun i => (StoredRelationTuple.read args i).1) positive).toFormula := by
  cases r with
  | row i r => exact StoredBlockArrayPackage.value (read rows i).1 seed last zero one r args positive
  | candidate r => exact StoredBlockArrayPackage.value C seed last zero one r args positive
  | noA =>
    simp only [build,StoredArrayAbsence.noA_value rows.original C.original (fun i => (read rows i).1.qfree) C.qfree seed]

def budget (ns : Fin k → Nat) (c q T B K : Nat) := 4+k+
  (∑ i, StoredBlockArrayPackage.budget (ns i) q T B K)+StoredBlockArrayPackage.budget c q T B K+
  StoredArrayAbsence.packageBudget q T

theorem bound (rows : Family R P ns) (C : Row R P c) (seed last zero one : P) {a : Nat}
    (r : UnifiedBlockPresentation.Rel ns c a) (args : StoredRelationTuple.Data (Fin q) a) (positive : Bool)
    (B K : Nat) (hr : ∀ i, StoredRowTransport.Bounds (read rows i).1 B K) (hc : StoredRowTransport.Bounds C B K) :
    (build rows C seed last zero one q T r args positive).2 ≤ budget ns c q T B K := by
  cases r with
  | row i r =>
    have ha := read_bound rows i
    have hb := StoredBlockArrayPackage.bound (T := T) (read rows i).1 seed last zero one r args positive B K (hr i)
    have hs : StoredBlockArrayPackage.budget (ns i) q T B K ≤ ∑ j, StoredBlockArrayPackage.budget (ns j) q T B K :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (StoredBlockArrayPackage.budget (ns j) q T B K)) (Finset.mem_univ i)
    simp only [build,budget]; omega
  | candidate r =>
    have hb := StoredBlockArrayPackage.bound (T := T) C seed last zero one r args positive B K hc
    simp only [build,budget]; omega
  | noA =>
    have hb := StoredArrayAbsence.noA_bound (R := R) (T := T) last zero one args positive
    simp only [build,budget]; omega

def sizeBudget (ns : Fin k → Nat) (c T B : Nat) :=
  (∑ i, StoredBlockArrayPackage.sizeBudget (ns i) T B)+StoredBlockArrayPackage.sizeBudget c T B+5+10*T

theorem shape (rows : Family R P ns) (C : Row R P c) (seed last zero one : P) {a : Nat}
    (r : UnifiedBlockPresentation.Rel ns c a) (args : StoredRelationTuple.Data (Fin q) a) (positive : Bool)
    (B K : Nat) (hr : ∀ i, StoredRowTransport.Bounds (read rows i).1 B K) (hc : StoredRowTransport.Bounds C B K) :
    StoredRelationalElimination.size (build rows C seed last zero one q T r args positive).1 ≤ sizeBudget ns c T B ∧
    arity (build rows C seed last zero one q T r args positive).1.body ≤ K := by
  cases r with
  | row i r =>
    have h := StoredBlockArrayPackage.shape (T := T) (read rows i).1 seed last zero one r args positive B K (hr i)
    have hs : StoredBlockArrayPackage.sizeBudget (ns i) T B ≤ ∑ j, StoredBlockArrayPackage.sizeBudget (ns j) T B :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (StoredBlockArrayPackage.sizeBudget (ns j) T B)) (Finset.mem_univ i)
    exact ⟨by have := h.1; simp only [build,sizeBudget]; omega,h.2⟩
  | candidate r =>
    have h := StoredBlockArrayPackage.shape (T := T) C seed last zero one r args positive B K hc
    exact ⟨by have := h.1; simp only [build,sizeBudget]; omega,h.2⟩
  | noA =>
    have h := StoredArrayAbsence.noA_shape (R := R) (T := T) last zero one args positive
    constructor
    · have := h.1; simp only [build,sizeBudget]; omega
    · simpa only [build,h.2] using Nat.zero_le K

theorem correct (rows : Family R P ns) (C : Row R P c) (seed last zero one : P) {a : Nat}
    (r : UnifiedBlockPresentation.Rel ns c a) (args : StoredRelationTuple.Data (Fin q) a) (positive : Bool)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : Params P q T → D) :
    Formula.Realize (build rows C seed last zero one q T r args positive).1.original.toFormula p ↔
      Formula.Realize (FiniteArrayRelationCompiler.compile rows.original C.original seed last zero one q T r
        (fun i => (StoredRelationTuple.read args i).1) positive) p := by
  rw [value]
  exact ArrayAtomExistentialPackages.relation_correct rows.original C.original (fun i => (read rows i).1.qfree)
    C.qfree seed last zero one q T r _ positive p
end NSSE.StoredRelationArrayPackage
