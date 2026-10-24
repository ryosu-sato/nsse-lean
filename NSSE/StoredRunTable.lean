import NSSE.StoredArrayParameterAtoms

/-! Counted stored exact reachability certificates, for signed dynamic runs.
Initial/final/step callbacks return actual stored QF formulas and their costs.
Construction of those callbacks is accounted for separately at the call site. -/
namespace NSSE.StoredRunTable
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n T : Nat}
abbrev Params (P : Type) (n T : Nat) := P ⊕ Fin ((T+1)*n)
abbrev Vertex (R : Nat → Type) (P : Type) (n : Nat) := Fin n → QF R P × Nat
abbrev Step (R : Nat → Type) (P : Type) (n : Nat) := Nat → Fin n → Fin n → QF R P × Nat

def any (m : Nat) (f : Fin m → Data R P 0 × Nat) : Data R P 0 × Nat :=
  let a := CountedFinEnumeration.tabulate m f
  let b := StoredArrayParameterAtoms.fold a.1
  (b.1,1+a.2+b.2)
theorem any_value (m : Nat) (f : Fin m → Data R P 0 × Nat) :
    denote (any m f).1 = SymbolicReachability.any m (fun i => denote (f i).1) := by
  simp only [any,StoredArrayParameterAtoms.fold_value,CountedFinEnumeration.tabulate_value,
    List.map_ofFn,SymbolicReachability.any]
  rw [List.ofFn_eq_map]
  rfl

def bit (one : P) (t : Fin (T+1)) (q : Fin n) : Data R (Params P n T) 0 × Nat :=
  let a := StoredArrayCoordinates.offset t q
  (.equal (.inl (.inr a.1)) (.inl (.inl one)),4+a.2)
theorem bit_value (one : P) (t : Fin (T+1)) (q : Fin n) :
    denote (bit (R := R) one t q).1 = ExactReachabilityTable.bit one t q := by
  simp only [bit,denote,StoredArrayCoordinates.offset_value,ExactReachabilityTable.bit]
  rfl

def lift (f : QF R P × Nat) (n T : Nat) : Data R (Params P n T) 0 × Nat :=
  let a := rename (fun p => ((Sum.inl p : Params P n T),1)) f.1.formula
  (a.1,1+f.2+a.2)
theorem lift_value (f : QF R P × Nat) :
    denote (lift f n T).1 = Formula.relabel (Sum.inl : P → Params P n T) (denote f.1.formula) := by
  simp only [lift,formula_value]

def initialCell (I : Vertex R P n) (one : P) (T : Nat) (q : Fin n) : Data R (Params P n T) 0 × Nat :=
  let a := bit one (0 : Fin (T+1)) q
  let b := lift (I q) n T
  (StoredArrayEquality.iff a.1 b.1,10+a.2+b.2)
theorem initialCell_value (I : Vertex R P n) (one : P) (q : Fin n) :
    denote (initialCell I one T q).1 = (ExactReachabilityTable.bit one (0 : Fin (T+1)) q).iff
      (Formula.relabel Sum.inl (denote (I q).1.formula)) := by
  simp only [initialCell,StoredArrayEquality.iff,StoredArrayEquality.conj,denote,bit_value,lift_value]
  rfl

def incoming (S : Step R P n) (one : P) (t : Fin T) (r q : Fin n) : Data R (Params P n T) 0 × Nat :=
  let a := bit one t.castSucc r
  let b := lift (S t.val r q) n T
  (StoredArrayEquality.conj a.1 b.1,7+a.2+b.2)
theorem incoming_value (S : Step R P n) (one : P) (t : Fin T) (r q : Fin n) :
    denote (incoming S one t r q).1 = ExactReachabilityTable.bit one t.castSucc r ⊓
      Formula.relabel Sum.inl (denote (S t.val r q).1.formula) := by
  simp only [incoming,StoredArrayEquality.conj,denote,bit_value,lift_value]
  rfl

def successor (S : Step R P n) (one : P) (t : Fin T) (q : Fin n) : Data R (Params P n T) 0 × Nat :=
  let a := bit one t.succ q
  let b := any n (fun r => incoming S one t r q)
  (StoredArrayEquality.iff a.1 b.1,10+a.2+b.2)
theorem successor_value (S : Step R P n) (one : P) (t : Fin T) (q : Fin n) :
    denote (successor S one t q).1 = (ExactReachabilityTable.bit one t.succ q).iff
      (SymbolicReachability.any n (fun r => ExactReachabilityTable.bit one t.castSucc r ⊓
        Formula.relabel Sum.inl (denote (S t.val r q).1.formula))) := by
  simp only [successor,StoredArrayEquality.iff,StoredArrayEquality.conj,denote,bit_value,any_value,incoming_value]
  rfl

def matrix (I : Vertex R P n) (S : Step R P n) (one : P) (T : Nat) : Data R (Params P n T) 0 × Nat :=
  let a := StoredArrayValidity.every n (initialCell I one T)
  let b := StoredArrayValidity.every T (fun t => StoredArrayValidity.every n (successor S one t))
  (StoredArrayEquality.conj a.1 b.1,7+a.2+b.2)
theorem matrix_value (I : Vertex R P n) (S : Step R P n) (one : P) :
    denote (matrix I S one T).1 = ExactReachabilityTable.matrix (fun q => denote (I q).1.formula)
      (fun t r q => denote (S t r q).1.formula) one T := by
  simp only [matrix,StoredArrayEquality.conj,denote,StoredArrayValidity.every_value,initialCell_value,
    successor_value,ExactReachabilityTable.matrix]
  rfl

def finalCell (F : Vertex R P n) (one : P) (T : Nat) (q : Fin n) : Data R (Params P n T) 0 × Nat :=
  let a := bit one (Fin.last T) q
  let b := lift (F q) n T
  (StoredArrayEquality.conj a.1 b.1,7+a.2+b.2)
theorem finalCell_value (F : Vertex R P n) (one : P) (q : Fin n) :
    denote (finalCell F one T q).1 = ExactReachabilityTable.bit one (Fin.last T) q ⊓
      Formula.relabel Sum.inl (denote (F q).1.formula) := by
  simp only [finalCell,StoredArrayEquality.conj,denote,bit_value,lift_value]
  rfl

def output (F : Vertex R P n) (one : P) (T : Nat) : Data R (Params P n T) 0 × Nat :=
  any n (finalCell F one T)
theorem output_value (F : Vertex R P n) (one : P) :
    denote (output F one T).1 = ExactReachabilityTable.output (fun q => denote (F q).1.formula) one T := by
  simp only [output,any_value,finalCell_value,ExactReachabilityTable.output]

def body (I F : Vertex R P n) (S : Step R P n) (one : P) (T : Nat) (positive : Bool) : Data R (Params P n T) 0 × Nat :=
  let a := matrix I S one T
  let b := output F one T
  let c := if positive then b.1 else Data.imp b.1 .falsum
  (StoredArrayEquality.conj a.1 c,10+a.2+b.2)
theorem body_value (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) :
    denote (body I F S one T positive).1 =
      ExactReachabilityTable.matrix (fun q => denote (I q).1.formula) (fun t r q => denote (S t r q).1.formula) one T ⊓
      ExactReachabilityTable.signed positive (ExactReachabilityTable.output (fun q => denote (F q).1.formula) one T) := by
  cases positive <;> simp only [body,Bool.false_eq_true,↓reduceIte,StoredArrayEquality.conj,denote,
    matrix_value,output_value,ExactReachabilityTable.signed]
  all_goals rfl
theorem body_qf (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) :
    (denote (body I F S one T positive).1).IsQF := by
  rw [body_value]
  exact ExactReachabilityTable.compile_matrix_qf _ _ _ one T positive
    (fun q => (I q).1.qfree) (fun q => (F q).1.qfree) (fun t _ r q => (S t r q).1.qfree)

def package (I F : Vertex R P n) (S : Step R P n) (one : P) (T : Nat) (positive : Bool) :
    StoredRelationalClosure.Package R P × Nat :=
  let a := body I F S one T positive
  let b := CountedSupportRule.mul (T+1) n
  (StoredRelationalPackages.assemble b.1 ((T+1)*n) (CountedSupportRule.mul_value _ _)
    a.1 (body_qf I F S one positive),2+a.2+b.2)
theorem package_value (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) :
    (package I F S one T positive).1.original =
      ⟨(T+1)*n,
        ExactReachabilityTable.matrix (fun q => denote (I q).1.formula) (fun t r q => denote (S t r q).1.formula) one T ⊓
        ExactReachabilityTable.signed positive (ExactReachabilityTable.output (fun q => denote (F q).1.formula) one T),
        ExactReachabilityTable.compile_matrix_qf _ _ _ one T positive
          (fun q => (I q).1.qfree) (fun q => (F q).1.qfree) (fun t _ r q => (S t r q).1.qfree)⟩ := by
  dsimp only [package]
  rw [StoredRelationalPackages.assemble_value]
  simp only [StoredRelationalClosure.Package.original,body_value]
theorem package_formula (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) :
    (package I F S one T positive).1.original.toFormula =
      ExactReachabilityTable.compile (fun q => denote (I q).1.formula) (fun q => denote (F q).1.formula)
        (fun t r q => denote (S t r q).1.formula) one T positive := by
  rw [package_value]
  rfl
theorem package_correct (I F : Vertex R P n) (S : Step R P n) (zero one : P) (positive : Bool)
    {D : Type*} [(UniformWordLowering.wordLanguage R).Structure D] (p : P → D) (h01 : p zero ≠ p one) :
    (package I F S one T positive).1.original.toFormula.Realize p ↔
      ((∃ q, ExactReachabilityTable.reachable (fun q => denote (I q).1.formula)
        (fun t r q => denote (S t r q).1.formula) p T q ∧ (Formula.Realize (denote (F q).1.formula) p)) ↔ positive = true) := by
  rw [package_formula]
  exact ExactReachabilityTable.compile_correct _ _ _ zero one T positive p h01
end NSSE.StoredRunTable
