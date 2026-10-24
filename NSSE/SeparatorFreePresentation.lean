import NSSE.WordEqualityAutomaton

/-! # Actual unary word presentation for absence of a fixed separator -/

namespace NSSE.SeparatorFreePresentation

open FirstOrder FirstOrder.Language SymbolicAutomata ConvolutionShapes

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w}

def guard (last : P) (s : Shape 1) : L.Formula (P ⊕ Fin (arity 1 s)) :=
  if hi : mask s 0 = true then
    (Term.equal (Term.var (Sum.inr (slot (mask s) 0 hi))) (Term.var (Sum.inl last))).not
  else ⊤

theorem guard_correct {D : Type*} [L.Structure D] (p : P → D) (last : P) (c : Sparse D 1) :
    (guard (L := L) last c.1).Realize (Sum.elim p c.2) ↔ toDense c 0 ≠ some (p last) := by
  by_cases hi : mask c.1 0 = true <;> simp [guard, hi, toDense, expand]

def compile (last : P) :=
  enforcePadding (WordEqualityAutomaton.localColumns (guard (L := L) last))

theorem column_absence {D : Type*} {k : Nat} (a : D)
    (cs : List (CanonicalConvolution.Column D k)) (i : Fin k) :
    (∀ c ∈ cs, c i ≠ some a) ↔ a ∉ CanonicalConvolution.decode cs i := by
  simp only [CanonicalConvolution.decode, List.mem_filterMap, not_exists, not_and]

theorem compile_correct {D : Type*} [L.Structure D] (p : P → D) (last : P) (U : List D) :
    tupleAccepts (compile (L := L) last) p ![U.reverse] ↔ p last ∉ U := by
  rw [compile, enforcePadding_tuple]
  unfold tupleAccepts denseAccepts
  rw [WordEqualityAutomaton.localColumns_correct]
  simp only [List.forall_mem_map, guard_correct, toDense_fromDense]
  rw [column_absence, CanonicalConvolution.decode_encode]
  simp

end NSSE.SeparatorFreePresentation
