import NSSE.StoredArrayAbsence

/-! Counted initial/final scalar atoms of stored rows. -/
namespace NSSE.StoredArrayParameterAtoms
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {n q T : Nat}

def seedName (seed : P) : P ⊕ Fin 1 → P × Nat
  | .inl p => (p,1)
  | .inr _ => (seed,1)
theorem seedName_value (seed : P) (x : P ⊕ Fin 1) :
    (seedName seed x).1 = Sum.elim id (fun _ => seed) x := by cases x <;> rfl
theorem seedName_bound (seed : P) (x : P ⊕ Fin 1) : (seedName seed x).2 ≤ 1 := by cases x <;> rfl

def initialTerm (A : Row R P n) (seed : P) (s z : Fin n) : Data R P 0 × Nat :=
  let a := StoredRelationTuple.read A.initial z
  let b := readPair A.data z s
  let c := rename (seedName seed) b.1.formula
  (StoredArrayEquality.conj a.1.formula c.1,8+a.2+b.2+c.2)
theorem initialTerm_value (A : Row R P n) (seed : P) (s z : Fin n) :
    denote (initialTerm A seed s z).1 = A.original.initial z ⊓
      SymbolicGuardedBlocks.dataAt (A.original.data z s) id seed := by
  simp only [initialTerm,StoredArrayEquality.conj,denote,formula_value,seedName_value,
    SymbolicGuardedBlocks.dataAt,Row.original]
  rfl
theorem initialTerm_nodes (A : Row R P n) (seed : P) (s z : Fin n) :
    nodes (initialTerm A seed s z).1 = 5+nodes (StoredRelationTuple.read A.initial z).1.formula+
      nodes (readPair A.data z s).1.formula := by
  simp only [initialTerm,StoredArrayEquality.conj,nodes,rename_nodes]; omega
theorem initialTerm_arity (A : Row R P n) (seed : P) (s z : Fin n) :
    arity (initialTerm A seed s z).1 = max (arity (StoredRelationTuple.read A.initial z).1.formula)
      (arity (readPair A.data z s).1.formula) := by
  simp only [initialTerm,StoredArrayEquality.conj,arity,rename_arity,Nat.max_zero]
def termBudget (n B K : Nat) := 9+3*n+weight K 1*B
theorem initialTerm_bound (A : Row R P n) (seed : P) (s z : Fin n) (B K : Nat)
    (hb : nodes (readPair A.data z s).1.formula ≤ B)
    (hk : arity (readPair A.data z s).1.formula ≤ K) :
    (initialTerm A seed s z).2 ≤ termBudget n B K := by
  have ha := StoredRelationTuple.read_bound A.initial z
  have hd := readPair_bound A.data z s
  have hc := rename_bound (seedName seed) 1 K (seedName_bound seed) (readPair A.data z s).1.formula hk
  simp only [initialTerm,termBudget]; nlinarith

def fold : List (Data R P 0) → Data R P 0 × Nat
  | [] => (.falsum,1)
  | a::as => let b := fold as; (.imp (.imp a .falsum) b.1,4+b.2)
theorem fold_value (as : List (Data R P 0)) :
    denote (fold as).1 = (as.map denote).foldr (fun f g => f ⊔ g) ⊥ := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [fold,denote,List.map_cons,List.foldr_cons,← ih]; rfl
theorem fold_cost (as : List (Data R P 0)) : (fold as).2 = 1+4*as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [fold,List.length_cons,ih]; omega
theorem fold_shape (as : List (Data R P 0)) (B K : Nat)
    (hb : ∀ a ∈ as, nodes a ≤ B) (hk : ∀ a ∈ as, arity a ≤ K) :
    nodes (fold as).1 ≤ 1+as.length*(3+B) ∧ arity (fold as).1 ≤ K := by
  induction as with
  | nil => simp [fold,nodes,arity]
  | cons a as ih =>
    have ha := hb a (by simp)
    have hka := hk a (by simp)
    have ht := ih (fun a h => hb a (by simp [h])) (fun a h => hk a (by simp [h]))
    simp only [fold,nodes,arity,Nat.max_zero,List.length_cons]
    exact ⟨by nlinarith, max_le hka ht.2⟩

def initial (A : Row R P n) (seed : P) (s : Fin n) : Data R P 0 × Nat :=
  let a := CountedFinEnumeration.tabulate n (initialTerm A seed s)
  let b := fold a.1
  (b.1,1+a.2+b.2)
theorem initial_value (A : Row R P n) (seed : P) (s : Fin n) :
    denote (initial A seed s).1 = BlockRelationPresentation.initialFormula A.original seed s := by
  simp only [initial,fold_value,CountedFinEnumeration.tabulate_value,List.map_ofFn,
    BlockRelationPresentation.initialFormula,SymbolicReachability.any]
  rw [List.ofFn_eq_map]
  congr 2
  funext z
  exact initialTerm_value A seed s z
structure Bounds (A : Row R P n) (B K : Nat) : Prop where
  initial : ∀ z, nodes (StoredRelationTuple.read A.initial z).1.formula ≤ B
  final : ∀ z, nodes (StoredRelationTuple.read A.final z).1.formula ≤ B
  data : ∀ z s, nodes (readPair A.data z s).1.formula ≤ B
  initial_arity : ∀ z, arity (StoredRelationTuple.read A.initial z).1.formula ≤ K
  final_arity : ∀ z, arity (StoredRelationTuple.read A.final z).1.formula ≤ K
  data_arity : ∀ z s, arity (readPair A.data z s).1.formula ≤ K

def initialBudget (n B K : Nat) := 2+StoredForwardTableBuild.tabBudget n (termBudget n B K)+4*n
theorem initial_bound (A : Row R P n) (seed : P) (s : Fin n) (B K : Nat) (h : Bounds A B K) :
    (initial A seed s).2 ≤ initialBudget n B K := by
  have ht := CountedFinEnumeration.tabulate_bound n (initialTerm A seed s) (termBudget n B K)
    (fun z => initialTerm_bound A seed s z B K (h.data z s) (h.data_arity z s))
  simp only [initial,fold_cost,CountedFinEnumeration.tabulate_value,List.length_ofFn,initialBudget,StoredForwardTableBuild.tabBudget] at *
  omega
theorem initial_shape (A : Row R P n) (seed : P) (s : Fin n) (B K : Nat) (h : Bounds A B K) :
    nodes (initial A seed s).1 ≤ 1+n*(8+2*B) ∧ arity (initial A seed s).1 ≤ K := by
  have ht := fold_shape (CountedFinEnumeration.tabulate n (initialTerm A seed s)).1 (5+2*B) K
  simp only [CountedFinEnumeration.tabulate_value,List.length_ofFn,List.mem_ofFn] at ht
  simp only [show 3+(5+2*B)=8+2*B by omega] at ht
  simp only [initial,CountedFinEnumeration.tabulate_value]
  apply ht
  · intro f hf
    obtain ⟨z,rfl⟩ := hf
    rw [initialTerm_nodes]
    have hi := h.initial z; have hd := h.data z s; omega
  · intro f hf
    obtain ⟨z,rfl⟩ := hf
    rw [initialTerm_arity]
    exact max_le (h.initial_arity z) (h.data_arity z s)

def initialQF (A : Row R P n) (seed : P) (s : Fin n) : QF R P :=
  ⟨(initial A seed s).1,by rw [initial_value]; exact ArrayAtomExistentialPackages.initial_qf A.original A.qfree seed s⟩

def signedLift (f : QF R P) (q T : Nat) (positive : Bool) : Data R (Params P q T) 0 × Nat :=
  let a := rename (fun p => ((Sum.inl p : Params P q T),1)) f.formula
  (if positive then a.1 else .imp a.1 .falsum,3+a.2)
theorem signedLift_value (f : QF R P) (positive : Bool) :
    denote (signedLift f q T positive).1 = ExactReachabilityTable.signed positive
      (Formula.relabel (Sum.inl : P → Params P q T) (denote f.formula)) := by
  cases positive <;> simp only [signedLift,Bool.false_eq_true,↓reduceIte,denote,formula_value,
    ExactReachabilityTable.signed]
  all_goals rfl
theorem signedLift_qf (f : QF R P) (positive : Bool) : (denote (signedLift f q T positive).1).IsQF := by
  rw [signedLift_value]
  exact ExactReachabilityTable.signed_qf _ _ (ExactReachabilityTable.relabel_qf _ f.qfree _)
theorem signedLift_shape (f : QF R P) (positive : Bool) :
    nodes (signedLift f q T positive).1 ≤ nodes f.formula+2 ∧
      arity (signedLift f q T positive).1 = arity f.formula := by
  cases positive <;> simp only [signedLift,Bool.false_eq_true,↓reduceIte,nodes,arity,rename_nodes,rename_arity,Nat.max_zero]
  all_goals exact ⟨by omega,True.intro⟩
theorem signedLift_bound (f : QF R P) (positive : Bool) (K : Nat) (hk : arity f.formula ≤ K) :
    (signedLift f q T positive).2 ≤ 3+weight K 1*nodes f.formula := by
  have h := rename_bound (fun p => ((Sum.inl p : Params P q T),1)) 1 K (fun _ => by rfl) f.formula hk
  simp only [signedLift]; omega

def atom (f : QF R P) (q T : Nat) (positive : Bool) : StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let a := signedLift f q T positive
  let b := StoredRelationalPackages.atom a.1 (signedLift_qf f positive)
  (b.1,1+a.2+b.2)
theorem atom_value (f : QF R P) (positive : Bool) :
    (atom f q T positive).1.original = ExistentialFormulaPackage.Package.atom
      (ExactReachabilityTable.signed positive (Formula.relabel (Sum.inl : P → Params P q T) (denote f.formula)))
      (ExactReachabilityTable.signed_qf _ _ (ExactReachabilityTable.relabel_qf _ f.qfree _)) := by
  simp only [atom,StoredRelationalPackages.atom_original,signedLift_value]
def atomBudget (B K : Nat) := 5+weight K 1*B+weight K 1*(B+2)
theorem atom_bound (f : QF R P) (positive : Bool) (B K : Nat)
    (hb : nodes f.formula ≤ B) (hk : arity f.formula ≤ K) :
    (atom f q T positive).2 ≤ atomBudget B K := by
  have h := signedLift_bound (q := q) (T := T) f positive K hk
  have hs := signedLift_shape (q := q) (T := T) f positive
  have ha := StoredRelationalPackages.atom_bound (signedLift f q T positive).1
    (signedLift_qf f positive) K (by rw [hs.2]; exact hk)
  simp only [atom,atomBudget]; nlinarith

theorem atom_shape (f : QF R P) (positive : Bool) :
    (atom f q T positive).1.vars = 0 ∧
    StoredRelationalElimination.size (atom f q T positive).1 ≤ nodes f.formula+2 ∧
    arity (atom f q T positive).1.body = arity f.formula := by
  have ha := StoredRelationalPackages.atom_shape (signedLift f q T positive).1 (signedLift_qf f positive)
  have hs := signedLift_shape (q := q) (T := T) f positive
  refine ⟨ha.1,?_,ha.2.2.trans hs.2⟩
  change nodes (StoredRelationalPackages.atom (signedLift f q T positive).1 (signedLift_qf f positive)).1.body+
    5*(StoredRelationalPackages.atom (signedLift f q T positive).1 (signedLift_qf f positive)).1.vars ≤ _
  rw [ha.2.1,ha.1]
  simpa only [Nat.mul_zero,Nat.add_zero] using hs.1

def initialPackage (A : Row R P n) (seed : P) (s : Fin n) (q T : Nat) (positive : Bool) :
    StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let a := initial A seed s
  let b := atom ⟨a.1,(initialQF A seed s).qfree⟩ q T positive
  (b.1,1+a.2+b.2)
def finalPackage (A : Row R P n) (s : Fin n) (q T : Nat) (positive : Bool) :
    StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let a := StoredRelationTuple.read A.final s
  let b := atom a.1 q T positive
  (b.1,1+a.2+b.2)
theorem initialPackage_value (A : Row R P n) (seed last zero one : P) (s : Fin n) (positive : Bool) :
    (initialPackage A seed s q T positive).1.original =
      ArrayAtomExistentialPackages.block A.original A.qfree seed last zero one q T (.initial s) Fin.elim0 positive := by
  simp only [initialPackage,atom_value,initialQF,initial_value,ArrayAtomExistentialPackages.block]
theorem finalPackage_value (A : Row R P n) (seed last zero one : P) (s : Fin n) (positive : Bool) :
    (finalPackage A s q T positive).1.original =
      ArrayAtomExistentialPackages.block A.original A.qfree seed last zero one q T (.final s) Fin.elim0 positive := by
  simp only [finalPackage,atom_value,ArrayAtomExistentialPackages.block,Row.original]
theorem initialPackage_bound (A : Row R P n) (seed : P) (s : Fin n) (positive : Bool) (B K : Nat) (h : Bounds A B K) :
    (initialPackage A seed s q T positive).2 ≤ 1+initialBudget n B K+atomBudget (1+n*(8+2*B)) K := by
  have hi := initial_bound A seed s B K h
  have hs := initial_shape A seed s B K h
  have ha := atom_bound (q := q) (T := T) (initialQF A seed s) positive (1+n*(8+2*B)) K hs.1 hs.2
  simp only [initialQF] at ha
  simp only [initialPackage]; omega
theorem finalPackage_bound (A : Row R P n) (s : Fin n) (positive : Bool) (B K : Nat) (h : Bounds A B K) :
    (finalPackage A s q T positive).2 ≤ 1+n+atomBudget B K := by
  have hi := StoredRelationTuple.read_bound A.final s
  have ha := atom_bound (q := q) (T := T) (StoredRelationTuple.read A.final s).1 positive B K (h.final s) (h.final_arity s)
  simp only [finalPackage]; omega
theorem initialPackage_shape (A : Row R P n) (seed : P) (s : Fin n) (positive : Bool) (B K : Nat) (h : Bounds A B K) :
    StoredRelationalElimination.size (initialPackage A seed s q T positive).1 ≤ 3+n*(8+2*B) ∧
    arity (initialPackage A seed s q T positive).1.body ≤ K := by
  have ha := atom_shape (q := q) (T := T) (initialQF A seed s) positive
  have hi := initial_shape A seed s B K h
  simp only [initialQF] at ha
  constructor
  · change StoredRelationalElimination.size (atom _ q T positive).1 ≤ _
    omega
  · change arity (atom _ q T positive).1.body ≤ K
    rw [ha.2.2]
    exact hi.2
theorem finalPackage_shape (A : Row R P n) (s : Fin n) (positive : Bool) (B K : Nat) (h : Bounds A B K) :
    StoredRelationalElimination.size (finalPackage A s q T positive).1 ≤ B+2 ∧
    arity (finalPackage A s q T positive).1.body ≤ K := by
  have ha := atom_shape (q := q) (T := T) (StoredRelationTuple.read A.final s).1 positive
  have hf := h.final s
  constructor
  · change StoredRelationalElimination.size (atom _ q T positive).1 ≤ _
    omega
  · change arity (atom _ q T positive).1.body ≤ K
    rw [ha.2.2]
    exact h.final_arity s
end NSSE.StoredArrayParameterAtoms
