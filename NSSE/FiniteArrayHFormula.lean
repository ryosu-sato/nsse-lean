import NSSE.FiniteWordArrayRepresentation
import NSSE.RowParameterTransport

/-! # Signed original H atoms on explicitly allocated finite arrays -/

namespace NSSE.FiniteArrayHFormula

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ConvolutionShapes
open FiniteWordCoordinates FiniteWordArrayRepresentation

universe u v w w'
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {P' : Type w'} {n q T : Nat}

theorem literalH_map (f : P → P') (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    {D : Type*} [L.Structure D] (p : P' → D) (U V : List D) :
    (RowParameterTransport.mapRow f R).LiteralH e (f seed) (f last) first p U V ↔
      R.LiteralH e seed last first (p ∘ f) U V := by
  have he : fallback (f seed) (f last) first = f (fallback seed last first) := by
    cases first <;> rfl
  simp only [Row.LiteralH, RowParameterTransport.markedNFA_map]
  simp only [RowParameterTransport.mapRow,
    Formula.realize_relabel, RowParameterTransport.valuation_comp, he, Function.comp_apply]

theorem select_decode {D : Type*} (p : P → D) {k m : Nat}
    (flags letters : Nat → Fin k → P) (one : P) (T : Nat) (args : Fin m → Fin k) (i : Fin m) :
    CanonicalConvolution.decode
      ((DynamicColumnRunFormula.inputWord p (fun t j => flags t (args j))
        (fun t j => letters t (args j)) one T).map toDense) i =
      CanonicalConvolution.decode
        ((DynamicColumnRunFormula.inputWord p flags letters one T).map toDense) (args i) := by
  unfold DynamicColumnRunFormula.inputWord
  simp only [List.map_ofFn, CanonicalConvolution.decode]
  conv_lhs => rw [filterMap_ofFn]
  conv_rhs => rw [filterMap_ofFn]
  apply congrArg (fun f : Fin T → Option D => (List.ofFn f).filterMap id)
  funext t
  simp only [Function.comp_apply, DynamicColumnSelection.dense_column]

theorem select_valid {D : Type*} [L.Structure D] (p : P → D) {k m : Nat}
    (flags : Nat → Fin k → P) (one : P) (T : Nat) (args : Fin m → Fin k)
    (h : (PrefixArrayValidity.formula (L := L) flags one T).Realize p) :
    (PrefixArrayValidity.formula (L := L) (fun t j => flags t (args j)) one T).Realize p := by
  rw [PrefixArrayValidity.realize_formula] at h ⊢
  exact fun t ht i => h t ht (args i)

def compile (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    (zero one : P) (q T : Nat) (args : Fin 2 → Fin q) (positive : Bool) : L.Formula (Params P q T) :=
  DynamicColumnRunFormula.compileH (RowParameterTransport.mapRow Sum.inl R) e (.inl seed) (.inl last) first
    (fun t i => flags zero q T t (args i)) (fun t i => letters zero q T t (args i)) (.inl one) T positive

theorem compile_correct (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : Fin 2 → Fin q) (positive : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one) (bs : Fin (count q T) → D)
    (hv : (valid (L := L) zero one q T).Realize (Sum.elim p bs)) :
    (compile R e seed last first zero one q T args positive).Realize (Sum.elim p bs) ↔
      (R.LiteralH e seed last first p (words p zero one bs (args 0)) (words p zero one bs (args 1)) ↔
        positive = true) := by
  have hv' := select_valid (Sum.elim p bs) (flags zero q T) (.inl one) T args hv
  rw [compile, PrefixArrayValidity.compileH_literal
    (RowParameterTransport.mapRow Sum.inl R) e (.inl seed) (.inl last) first
    (fun t i => flags zero q T t (args i)) (fun t i => letters zero q T t (args i))
    (.inl zero) (.inl one) T positive (Sum.elim p bs) h01 hv', literalH_map]
  simp only [select_decode]
  rfl

theorem mapRow_qf (f : P → P') (R : Row L P n) (h : ExactGuardedRunFormula.RowQF R) :
    ExactGuardedRunFormula.RowQF (RowParameterTransport.mapRow f R) where
  data q r := ExactReachabilityTable.relabel_qf _ (h.data q r) _
  left q r := ExactReachabilityTable.relabel_qf _ (h.left q r) _
  right q r := ExactReachabilityTable.relabel_qf _ (h.right q r) _
  guard := ExactReachabilityTable.relabel_qf _ h.guard _

theorem mapRow_size {B : Nat} (f : P → P') (R : Row L P n) (h : ExactGuardedRunSize.RowSize R B) :
    ExactGuardedRunSize.RowSize (RowParameterTransport.mapRow f R) B := by
  constructor
  · intro q r
    simpa only [RowParameterTransport.mapRow, ExactReachabilitySize.nodes_relabel] using h.data q r
  · intro q r
    simpa only [RowParameterTransport.mapRow, ExactReachabilitySize.nodes_relabel] using h.left q r
  · intro q r
    simpa only [RowParameterTransport.mapRow, ExactReachabilitySize.nodes_relabel] using h.right q r
  · simpa only [RowParameterTransport.mapRow, ExactReachabilitySize.nodes_relabel] using h.guard

theorem nodes_compile_le {B : Nat} (R : Row L P n) (h : ExactGuardedRunSize.RowSize R B)
    (e : Ends n) (seed last : P) (first : Bool) (zero one : P)
    (q T : Nat) (args : Fin 2 → Fin q) (positive : Bool) :
    let N := 2*n*n
    let H := 109+5*ExactGuardedRunSize.guardBound n B
    ExactReachabilitySize.nodes (compile R e seed last first zero one q T args positive) ≤
      19+N*(14+2*H)+T*(8+N*(16+2*N*(9+H)))+N*(9+H)+5*((T+1)*N) :=
  DynamicColumnRunFormula.nodes_compileH_le _ (mapRow_size Sum.inl R h) _ _ _ _ _ _ _ _ _

end NSSE.FiniteArrayHFormula
