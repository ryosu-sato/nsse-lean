import NSSE.StoredArrayCoordinates

/-! Actual stored scalar formulas for bounded-word equality. -/
namespace NSSE.StoredArrayEquality
open FirstOrder FirstOrder.Language StoredRelationalFormula FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {q T : Nat}
def conj (φ ψ : Data R P 0) : Data R P 0 := .imp (.imp φ (.imp ψ .falsum)) .falsum
def iff (φ ψ : Data R P 0) : Data R P 0 := conj (.imp φ ψ) (.imp ψ φ)
def atPosition (one : P) (i j : Fin q) (t : Fin (T+1)) : Data R (Params P q T) 0 × Nat :=
  let fi := StoredArrayCoordinates.flag (P := P) t i
  let fj := StoredArrayCoordinates.flag (P := P) t j
  let li := StoredArrayCoordinates.letter (P := P) t i
  let lj := StoredArrayCoordinates.letter (P := P) t j
  let a := Data.equal (Sum.inl fi.1) (Sum.inl (Sum.inl one))
  let b := Data.equal (Sum.inl fj.1) (Sum.inl (Sum.inl one))
  (conj (iff a b) (.imp a (.equal (Sum.inl li.1) (Sum.inl lj.1))),30+fi.2+fj.2+li.2+lj.2)
theorem atPosition_value (zero one : P) (i j : Fin q) (t : Fin (T+1)) :
    denote (atPosition (R := R) one i j t).1 =
      FiniteArrayEqualityFormula.atPosition zero one q T i j t.val := by
  simp only [atPosition,conj,iff,denote,StoredArrayCoordinates.flag_value zero,StoredArrayCoordinates.letter_value zero,
    FiniteArrayEqualityFormula.atPosition,DynamicColumnSelection.flag]
  rfl
def positionBudget (q T : Nat) := 30+2*StoredArrayCoordinates.flagBudget q T+2*StoredArrayCoordinates.letterBudget q T
theorem atPosition_bound (one : P) (i j : Fin q) (t : Fin (T+1)) :
    (atPosition (R := R) one i j t).2 ≤ positionBudget q T := by
  have hi := StoredArrayCoordinates.flag_bound (P := P) t i
  have hj := StoredArrayCoordinates.flag_bound (P := P) t j
  have hli := StoredArrayCoordinates.letter_bound (P := P) t i
  have hlj := StoredArrayCoordinates.letter_bound (P := P) t j
  simp only [atPosition,positionBudget]; omega

def fold : List (Data R P 0) → Data R P 0 × Nat
  | [] => (.imp .falsum .falsum,3)
  | φ::xs => let a := fold xs; (conj φ a.1,6+a.2)
theorem fold_value (xs : List (Data R P 0)) :
    denote (fold xs).1 = (xs.map denote).foldr (fun φ ψ => φ ⊓ ψ) ⊤ := by
  induction xs with
  | nil => rfl
  | cons φ xs ih => simp only [fold,conj,denote,List.map_cons,List.foldr_cons,← ih]; rfl
theorem fold_cost (xs : List (Data R P 0)) : (fold xs).2 = 3+6*xs.length := by
  induction xs with
  | nil => rfl
  | cons φ xs ih => simp only [fold,List.length_cons,ih]; omega

def matrix (one : P) (q T : Nat) (i j : Fin q) : Data R (Params P q T) 0 × Nat :=
  let a := CountedFinEnumeration.tabulate T (fun t => atPosition one i j t.castSucc)
  let b := fold a.1
  (b.1,1+a.2+b.2)
theorem matrix_value (zero one : P) (i j : Fin q) :
    denote (matrix (R := R) one q T i j).1 = FiniteArrayEqualityFormula.matrix zero one q T i j := by
  simp only [matrix,fold_value,CountedFinEnumeration.tabulate_value,List.map_ofFn,Function.comp_apply,
    atPosition_value zero,Fin.coe_castSucc,FiniteArrayEqualityFormula.matrix,ExactReachabilityTable.every]
  rw [List.ofFn_eq_map]
  congr 2
  funext t
  exact atPosition_value zero one i j t.castSucc

def matrixBudget (q T : Nat) := 4+StoredForwardTableBuild.tabBudget T (positionBudget q T)+6*T
theorem matrix_bound (one : P) (i j : Fin q) :
    (matrix (R := R) one q T i j).2 ≤ matrixBudget q T := by
  have h := CountedFinEnumeration.tabulate_bound T (fun t : Fin T => atPosition (R := R) one i j t.castSucc)
    (positionBudget q T) (fun t => atPosition_bound one i j t.castSucc)
  simp only [matrix,fold_cost,CountedFinEnumeration.tabulate_value,List.length_ofFn,matrixBudget,
    StoredForwardTableBuild.tabBudget] at *
  omega

def compile (one : P) (q T : Nat) (i j : Fin q) (positive : Bool) : Data R (Params P q T) 0 × Nat :=
  let a := matrix one q T i j
  (if positive then a.1 else .imp a.1 .falsum,3+a.2)
theorem compile_value (zero one : P) (i j : Fin q) (positive : Bool) :
    denote (compile (R := R) one q T i j positive).1 =
      FiniteArrayEqualityFormula.compile zero one q T i j positive := by
  cases positive <;> simp only [compile,Bool.false_eq_true,↓reduceIte,denote,matrix_value zero,
    FiniteArrayEqualityFormula.compile,ExactReachabilityTable.signed]
  all_goals rfl
theorem compile_bound (one : P) (i j : Fin q) (positive : Bool) :
    (compile (R := R) one q T i j positive).2 ≤ 3+matrixBudget q T := by
  have h := matrix_bound (R := R) (T := T) one i j
  simp only [compile]; omega
theorem compile_qf (zero one : P) (i j : Fin q) (positive : Bool) :
    (denote (compile (R := R) one q T i j positive).1).IsQF := by
  rw [compile_value zero]
  exact ExactReachabilityTable.signed_qf _ _ (FiniteArrayEqualityFormula.matrix_qf zero one q T i j)
theorem compile_nodes (zero one : P) (i j : Fin q) (positive : Bool) :
    nodes (compile (R := R) one q T i j positive).1 ≤ 5+24*T := by
  rw [← denote_nodes,compile_value zero]
  unfold FiniteArrayEqualityFormula.compile
  cases positive <;> simp [ExactReachabilityTable.signed,ExactReachabilitySize.nodes_not,
    FiniteArrayEqualityFormula.nodes_matrix]
  all_goals omega

theorem fold_arity (xs : List (Data R P 0)) (h : ∀ φ ∈ xs, arity φ = 0) : arity (fold xs).1 = 0 := by
  induction xs with
  | nil => rfl
  | cons φ xs ih =>
    have ha := h φ (by simp)
    have hb := ih (fun ψ hψ => h ψ (by simp [hψ]))
    simp only [fold,conj,arity,ha,hb,Nat.max_self]
theorem compile_arity (one : P) (i j : Fin q) (positive : Bool) :
    arity (compile (R := R) one q T i j positive).1 = 0 := by
  have h : arity (matrix (R := R) one q T i j).1 = 0 := by
    apply fold_arity
    intro φ hφ
    rw [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at hφ
    obtain ⟨t,rfl⟩ := hφ
    rfl
  cases positive <;> simp only [compile,Bool.false_eq_true,↓reduceIte,arity,h,Nat.max_self]
def package (zero one : P) (q T : Nat) (i j : Fin q) (positive : Bool) :
    StoredRelationalClosure.Package R (Params P q T) × Nat :=
  let a := compile one q T i j positive
  let b := StoredRelationalPackages.atom a.1 (compile_qf zero one i j positive)
  (b.1,1+a.2+b.2)
theorem package_value (zero one : P) (i j : Fin q) (positive : Bool) :
    (package (R := R) zero one q T i j positive).1.original =
      ArrayAtomExistentialPackages.equality zero one q T i j positive := by
  simp only [package,StoredRelationalPackages.atom_original,compile_value zero,ArrayAtomExistentialPackages.equality]
theorem package_bound (zero one : P) (i j : Fin q) (positive : Bool) :
    (package (R := R) zero one q T i j positive).2 ≤ 5+matrixBudget q T+5*(5+24*T) := by
  have hc := compile_bound (R := R) (T := T) one i j positive
  have hn := compile_nodes (R := R) (T := T) zero one i j positive
  have hk := compile_arity (R := R) (T := T) one i j positive
  have ha := StoredRelationalPackages.atom_bound (compile (R := R) one q T i j positive).1
    (compile_qf zero one i j positive) 0 (by omega)
  simp only [weight] at ha
  simp only [package]; omega
end NSSE.StoredArrayEquality
