import NSSE.FiniteArrayBlockFormula

/-! # Exact signed separator-absence tests on finite arrays -/

namespace NSSE.FiniteArrayAbsenceFormula

open FirstOrder FirstOrder.Language ConvolutionShapes ExactReachabilityTable
open FiniteWordCoordinates FiniteWordArrayRepresentation

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {q T : Nat}

theorem mem_words {D : Type*} (p : P → D) (zero one : P) (bs : Fin (count q T) → D)
    (i : Fin q) (x : D) :
    x ∈ words p zero one bs i ↔ ∃ t : Fin T,
      Sum.elim p bs (flags zero q T t i) = p one ∧ Sum.elim p bs (letters zero q T t i) = x := by
  classical
  unfold words
  rw [List.mem_reverse]
  unfold CanonicalConvolution.decode DynamicColumnRunFormula.inputWord
  rw [List.map_ofFn]
  simp only [List.mem_filterMap, List.mem_ofFn]
  constructor
  · rintro ⟨c, ⟨t, rfl⟩, hc⟩
    simp only [Function.comp_apply, DynamicColumnSelection.dense_column] at hc
    split_ifs at hc with h
    · exact ⟨t, h, Option.some.inj hc⟩
  · rintro ⟨t, ht, hx⟩
    refine ⟨_, ⟨t, rfl⟩, ?_⟩
    simp only [Function.comp_apply, DynamicColumnSelection.dense_column]
    simp [ht, hx]

def matrix (last zero one : P) (q T : Nat) (i : Fin q) : L.Formula (Params P q T) :=
  every T (fun t => (DynamicColumnSelection.flag (.inl one) (flags zero q T t i)).imp
    (((Term.var (letters zero q T t i)).equal (Term.var (.inl last))).not))

theorem matrix_correct (last zero one : P) (i : Fin q) {D : Type*} [L.Structure D]
    (p : P → D) (bs : Fin (count q T) → D) :
    (matrix (L := L) last zero one q T i).Realize (Sum.elim p bs) ↔
      p last ∉ words p zero one bs i := by
  rw [mem_words]
  simp [matrix, realize_every]

def compile (last zero one : P) (q T : Nat) (i : Fin q) (positive : Bool) : L.Formula (Params P q T) :=
  signed positive (matrix last zero one q T i)

theorem compile_correct (last zero one : P) (i : Fin q) (positive : Bool) {D : Type*} [L.Structure D]
    (p : P → D) (bs : Fin (count q T) → D) :
    (compile (L := L) last zero one q T i positive).Realize (Sum.elim p bs) ↔
      (p last ∉ words p zero one bs i ↔ positive = true) := by
  rw [compile, realize_signed, matrix_correct]

theorem matrix_qf (last zero one : P) (q T : Nat) (i : Fin q) :
    (matrix (L := L) last zero one q T i).IsQF := by
  apply every_qf
  intro t
  exact (BoundedFormula.IsAtomic.isQF (.equal _ _)).imp
    (BoundedFormula.IsAtomic.isQF (.equal _ _)).not

theorem nodes_matrix (last zero one : P) (q T : Nat) (i : Fin q) :
    ExactReachabilitySize.nodes (matrix (L := L) last zero one q T i) = 3+10*T := by
  simp [matrix, ExactReachabilitySize.nodes_every, ExactReachabilitySize.nodes_not,
    ExactReachabilitySize.nodes, DynamicColumnSelection.flag, Term.equal, Term.bdEqual, Nat.mul_comm]

end NSSE.FiniteArrayAbsenceFormula
