import NSSE.StoredArrayValidity

/-! Counted stored separator-absence atoms for actual scalar lowering. -/
namespace NSSE.StoredArrayAbsence
open FirstOrder FirstOrder.Language StoredRelationalFormula FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {q T : Nat}

def step (last one : P) (i : Fin q) (t : Fin T) : Data R (Params P q T) 0 × Nat :=
  let f := StoredArrayCoordinates.flag (P := P) t.castSucc i
  let l := StoredArrayCoordinates.letter (P := P) t.castSucc i
  (.imp (.equal (.inl f.1) (.inl (.inl one)))
    (.imp (.equal (.inl l.1) (.inl (.inl last))) .falsum),10+f.2+l.2)
theorem step_value (last zero one : P) (i : Fin q) (t : Fin T) :
    denote (step (R := R) last one i t).1 =
      (DynamicColumnSelection.flag (.inl one) (flags zero q T t i)).imp
        (((Term.var (letters zero q T t i)).equal (Term.var (.inl last))).not) := by
  simp only [step,denote,StoredArrayCoordinates.flag_value zero,
    StoredArrayCoordinates.letter_value zero,Fin.coe_castSucc,DynamicColumnSelection.flag]
  rfl

def stepBudget (q T : Nat) := 10+StoredArrayCoordinates.flagBudget q T+StoredArrayCoordinates.letterBudget q T
theorem step_bound (last one : P) (i : Fin q) (t : Fin T) :
    (step (R := R) last one i t).2 ≤ stepBudget q T := by
  have hf := StoredArrayCoordinates.flag_bound (P := P) t.castSucc i
  have hl := StoredArrayCoordinates.letter_bound (P := P) t.castSucc i
  simp only [step,stepBudget]; omega

def matrix (last one : P) (q T : Nat) (i : Fin q) : Data R (Params P q T) 0 × Nat :=
  StoredArrayValidity.every T (fun t => step last one i t)
theorem matrix_value (last zero one : P) (i : Fin q) :
    denote (matrix (R := R) last one q T i).1 = FiniteArrayAbsenceFormula.matrix last zero one q T i := by
  simp only [matrix,StoredArrayValidity.every_value,step_value last zero,FiniteArrayAbsenceFormula.matrix]
def matrixBudget (q T : Nat) := StoredArrayValidity.everyBudget T (stepBudget q T)
theorem matrix_bound (last one : P) (i : Fin q) :
    (matrix (R := R) last one q T i).2 ≤ matrixBudget q T :=
  StoredArrayValidity.every_bound T _ _ (fun t => step_bound last one i t)

def compile (last one : P) (q T : Nat) (i : Fin q) (positive : Bool) : Data R (Params P q T) 0 × Nat :=
  let a := matrix last one q T i
  (if positive then a.1 else .imp a.1 .falsum,3+a.2)
theorem compile_value (last zero one : P) (i : Fin q) (positive : Bool) :
    denote (compile (R := R) last one q T i positive).1 =
      FiniteArrayAbsenceFormula.compile last zero one q T i positive := by
  cases positive <;> simp only [compile,Bool.false_eq_true,↓reduceIte,denote,matrix_value last zero,
    FiniteArrayAbsenceFormula.compile,ExactReachabilityTable.signed]
  all_goals rfl
theorem compile_bound (last one : P) (i : Fin q) (positive : Bool) :
    (compile (R := R) last one q T i positive).2 ≤ 3+matrixBudget q T := by
  have h := matrix_bound (R := R) (T := T) last one i
  simp only [compile]; omega
theorem compile_qf (last zero one : P) (i : Fin q) (positive : Bool) :
    (denote (compile (R := R) last one q T i positive).1).IsQF := by
  rw [compile_value last zero]
  exact ExactReachabilityTable.signed_qf _ _ (FiniteArrayAbsenceFormula.matrix_qf last zero one q T i)
theorem compile_nodes (last zero one : P) (i : Fin q) (positive : Bool) :
    nodes (compile (R := R) last one q T i positive).1 ≤ 5+10*T := by
  rw [← denote_nodes,compile_value last zero]
  unfold FiniteArrayAbsenceFormula.compile
  cases positive <;> simp [ExactReachabilityTable.signed,ExactReachabilitySize.nodes_not,
    FiniteArrayAbsenceFormula.nodes_matrix]
  all_goals omega
theorem compile_arity (last one : P) (i : Fin q) (positive : Bool) :
    arity (compile (R := R) last one q T i positive).1 = 0 := by
  have h : arity (matrix (R := R) last one q T i).1 = 0 :=
    StoredArrayValidity.every_arity T _ (fun _ => rfl)
  cases positive <;> simp only [compile,Bool.false_eq_true,↓reduceIte,arity,h,Nat.max_self]

def package (last zero one : P) (q T : Nat) (i : Fin q) (positive : Bool) :
    StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let a := compile last one q T i positive
  let b := StoredRelationalPackages.atom a.1 (compile_qf last zero one i positive)
  (b.1,1+a.2+b.2)
theorem package_value (last zero one : P) (i : Fin q) (positive : Bool) :
    (package (R := R) last zero one q T i positive).1.original =
      ExistentialFormulaPackage.Package.atom
        (FiniteArrayAbsenceFormula.compile last zero one q T i positive)
        (ExactReachabilityTable.signed_qf _ _ (FiniteArrayAbsenceFormula.matrix_qf _ _ _ _ _ _)) := by
  simp only [package,StoredRelationalPackages.atom_original,compile_value last zero]
def packageBudget (q T : Nat) := 5+matrixBudget q T+5*(5+10*T)
theorem package_bound (last zero one : P) (i : Fin q) (positive : Bool) :
    (package (R := R) last zero one q T i positive).2 ≤ packageBudget q T := by
  have hc := compile_bound (R := R) (T := T) last one i positive
  have hn := compile_nodes (R := R) (T := T) last zero one i positive
  have ha := StoredRelationalPackages.atom_bound (compile (R := R) last one q T i positive).1
    (compile_qf last zero one i positive) 0 (by rw [compile_arity])
  simp only [weight] at ha
  simp only [package,packageBudget]; omega

def noA (last zero one : P) (q T : Nat) (args : StoredRelationTuple.Data (Fin q) 1) (positive : Bool) :
    StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let a := StoredRelationTuple.read args 0
  let b := package last zero one q T a.1 positive
  (b.1,1+a.2+b.2)
theorem noA_value {k c : Nat} {ns : Fin k → Nat}
    (rows : (j : Fin k) → SymbolicGuardedBlocks.Row (UniformWordLowering.wordLanguage R) P (ns j))
    (C : SymbolicGuardedBlocks.Row (UniformWordLowering.wordLanguage R) P c)
    (hr : ∀ j, ArrayAtomExistentialPackages.RowQF (rows j)) (hc : ArrayAtomExistentialPackages.RowQF C)
    (seed last zero one : P) (args : StoredRelationTuple.Data (Fin q) 1) (positive : Bool) :
    (noA (R := R) last zero one q T args positive).1.original =
      ArrayAtomExistentialPackages.relation rows C hr hc seed last zero one q T
        .noA (fun j => (StoredRelationTuple.read args j).1) positive := by
  simp only [noA,package_value,ArrayAtomExistentialPackages.relation]
theorem noA_bound (last zero one : P) (args : StoredRelationTuple.Data (Fin q) 1) (positive : Bool) :
    (noA (R := R) last zero one q T args positive).2 ≤ 2+packageBudget q T := by
  have ha := StoredRelationTuple.read_bound args 0
  have hb := package_bound (R := R) (T := T) last zero one (StoredRelationTuple.read args 0).1 positive
  simp only [noA]; omega

theorem package_correct (last zero one : P) (i : Fin q) (positive : Bool)
    {D : Type*} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (bs : Fin (count q T) → D) :
    (package (R := R) last zero one q T i positive).1.original.toFormula.Realize (Sum.elim p bs) ↔
      (p last ∉ FiniteWordArrayRepresentation.words p zero one bs i ↔ positive = true) := by
  rw [package_value,ExistentialFormulaPackage.Package.atom_correct]
  exact FiniteArrayAbsenceFormula.compile_correct last zero one i positive p bs
theorem package_shape (last zero one : P) (i : Fin q) (positive : Bool) :
    StoredRelationalElimination.size (package (R := R) last zero one q T i positive).1 ≤ 5+10*T ∧
    arity (package (R := R) last zero one q T i positive).1.body = 0 := by
  have ha := StoredRelationalPackages.atom_shape (compile (R := R) last one q T i positive).1
    (compile_qf last zero one i positive)
  constructor
  · dsimp only [package,StoredRelationalElimination.size]
    rw [ha.2.1,ha.1]
    simpa only [Nat.mul_zero,Nat.add_zero] using compile_nodes (R := R) (T := T) last zero one i positive
  · exact ha.2.2.trans (compile_arity last one i positive)
theorem noA_shape (last zero one : P) (args : StoredRelationTuple.Data (Fin q) 1) (positive : Bool) :
    StoredRelationalElimination.size (noA (R := R) last zero one q T args positive).1 ≤ 5+10*T ∧
    arity (noA (R := R) last zero one q T args positive).1.body = 0 :=
  package_shape last zero one (StoredRelationTuple.read args 0).1 positive
end NSSE.StoredArrayAbsence
