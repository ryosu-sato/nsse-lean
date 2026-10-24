import NSSE.FiniteArrayAbsenceFormula

/-! # Word equality and disequality as linear-size scalar array formulas -/

namespace NSSE.FiniteArrayEqualityFormula

open FirstOrder FirstOrder.Language ConvolutionShapes ExactReachabilityTable
open FiniteWordCoordinates FiniteWordArrayRepresentation CanonicalConvolution

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {q T : Nat}

theorem empty_column_eq {D : Type*} {k : Nat} (c : CanonicalConvolution.Column D k)
    (hc : present c = false) (i j : Fin k) : c i = c j := by
  have hn (i : Fin k) : c i = none := by
    cases hi : c i with
    | none => rfl
    | some x =>
      have hp : present c = true := (present_iff c).mpr ⟨i, by simp [active, hi]⟩
      simp [hc] at hp
  rw [hn, hn]

theorem columns_eq_iff {D : Type*} {k : Nat} (w : List (CanonicalConvolution.Column D k))
    (hc : Canonical (w.filter present)) (i j : Fin k) :
    (∀ c ∈ w, c i = c j) ↔ CanonicalConvolution.decode w i = CanonicalConvolution.decode w j := by
  constructor
  · exact WordEqualityAutomaton.decode_eq_of_column_eq w i j
  · intro he c hcw
    cases hp : present c
    · exact empty_column_eq c hp i j
    · have he' : CanonicalConvolution.decode (w.filter present) i = CanonicalConvolution.decode (w.filter present) j := by
        simpa only [SkipEmptyColumns.decode_filter] using he
      exact WordEqualityAutomaton.column_eq_of_decode_eq hc i j he' c (List.mem_filter.mpr ⟨hcw, hp⟩)

def atPosition (zero one : P) (q T : Nat) (i j : Fin q) (t : Nat) : L.Formula (Params P q T) :=
  let fi := DynamicColumnSelection.flag (.inl one) (flags zero q T t i)
  let fj := DynamicColumnSelection.flag (.inl one) (flags zero q T t j)
  fi.iff fj ⊓ fi.imp ((Term.var (letters zero q T t i)).equal (Term.var (letters zero q T t j)))

theorem atPosition_correct (zero one : P) (i j : Fin q) (t : Nat)
    {D : Type*} [L.Structure D] (p : P → D) (bs : Fin (count q T) → D) :
    (atPosition (L := L) zero one q T i j t).Realize (Sum.elim p bs) ↔
      toDense (DynamicColumnSelection.column (Sum.elim p bs) (flags zero q T t) (letters zero q T t) (.inl one)) i =
      toDense (DynamicColumnSelection.column (Sum.elim p bs) (flags zero q T t) (letters zero q T t) (.inl one)) j := by
  classical
  simp only [atPosition, Formula.realize_inf, Formula.realize_iff, Formula.realize_imp,
    DynamicColumnSelection.realize_flag, Formula.realize_equal, Term.realize,
    DynamicColumnSelection.dense_column, Sum.elim_inl, Sum.elim_inr]
  by_cases hi : Sum.elim p bs (flags zero q T t i) = p one <;>
    by_cases hj : Sum.elim p bs (flags zero q T t j) = p one <;> simp [hi, hj]

def matrix (zero one : P) (q T : Nat) (i j : Fin q) : L.Formula (Params P q T) :=
  every T (fun t => atPosition zero one q T i j t)

theorem matrix_correct (zero one : P) (i j : Fin q) {D : Type*} [L.Structure D]
    (p : P → D) (bs : Fin (count q T) → D)
    (hv : (valid (L := L) zero one q T).Realize (Sum.elim p bs)) :
    (matrix (L := L) zero one q T i j).Realize (Sum.elim p bs) ↔ words p zero one bs i = words p zero one bs j := by
  have hc := PrefixArrayValidity.canonical_input (Sum.elim p bs) (flags zero q T) (letters zero q T) (.inl one) T hv
  rw [matrix, realize_every]
  simp only [atPosition_correct]
  unfold words
  rw [List.reverse_inj]
  rw [← columns_eq_iff _ hc i j]
  simp only [DynamicColumnRunFormula.inputWord, List.forall_mem_map, List.mem_ofFn]
  constructor
  · rintro h c ⟨t, rfl⟩
    exact h t
  · intro h t
    exact h _ ⟨t, rfl⟩

def compile (zero one : P) (q T : Nat) (i j : Fin q) (positive : Bool) : L.Formula (Params P q T) :=
  signed positive (matrix zero one q T i j)

theorem compile_correct (zero one : P) (i j : Fin q) (positive : Bool) {D : Type*} [L.Structure D]
    (p : P → D) (bs : Fin (count q T) → D)
    (hv : (valid (L := L) zero one q T).Realize (Sum.elim p bs)) :
    (compile (L := L) zero one q T i j positive).Realize (Sum.elim p bs) ↔
      (words p zero one bs i = words p zero one bs j ↔ positive = true) := by
  rw [compile, realize_signed, matrix_correct zero one i j p bs hv]

theorem matrix_qf (zero one : P) (q T : Nat) (i j : Fin q) :
    (matrix (L := L) zero one q T i j).IsQF := by
  apply every_qf
  intro t
  have hi : (DynamicColumnSelection.flag (L := L) (.inl one) (flags zero q T t i)).IsQF :=
    BoundedFormula.IsAtomic.isQF (.equal _ _)
  have hj : (DynamicColumnSelection.flag (L := L) (.inl one) (flags zero q T t j)).IsQF :=
    BoundedFormula.IsAtomic.isQF (.equal _ _)
  exact (iff_qf _ _ hi hj).inf (hi.imp (BoundedFormula.IsAtomic.isQF (.equal _ _)))

theorem nodes_matrix (zero one : P) (q T : Nat) (i j : Fin q) :
    ExactReachabilitySize.nodes (matrix (L := L) zero one q T i j) = 3+24*T := by
  simp [matrix, atPosition, ExactReachabilitySize.nodes_every, ExactReachabilitySize.nodes_inf,
    ExactReachabilitySize.nodes_iff, ExactReachabilitySize.nodes, DynamicColumnSelection.flag,
    Term.equal, Term.bdEqual, Nat.mul_comm]

end NSSE.FiniteArrayEqualityFormula
