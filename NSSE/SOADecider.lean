import NSSE.ConcreteSOA
import NSSE.FiniteFixpoint

/-!
# Certified finite compiler to an SOA decision procedure

The final executable wrapper.  A concrete guarded compiler supplies its
finite update and the three semantic certificates exposed by the earlier
modules.  The resulting Boolean function decides existence of an SOA
avoider, and therefore of a critical word.
-/

namespace NSSE

universe u

structure CertifiedSOACompiler
    {α : Type u} (I : SOAInstance α) where
  update : List Bool → List Bool
  initial : List Bool
  semantic : List Bool
  rootIndex : Nat
  inflationary : ∀ mask, MaskLe mask (update mask)
  monotone : MaskMonotone update
  semantic_lfp :
    LeastFixedPointSpec update initial semantic
  root_correct :
    maskBit semantic rootIndex = true ↔
      ∃ word, I.Avoider word

namespace CertifiedSOACompiler

def decideAvoider
    {I : SOAInstance α} (compiler : CertifiedSOACompiler I) : Bool :=
  decideLeastFixedPoint compiler.update compiler.initial
    compiler.rootIndex

theorem decideAvoider_correct
    {I : SOAInstance α} (compiler : CertifiedSOACompiler I) :
    compiler.decideAvoider = true ↔
      ∃ word, I.Avoider word := by
  rw [decideAvoider,
    decideLeastFixedPoint_correct compiler.update
      compiler.inflationary compiler.monotone compiler.initial
      compiler.semantic compiler.semantic_lfp compiler.rootIndex]
  exact compiler.root_correct

theorem decideCritical_correct
    {I : SOAInstance α} (compiler : CertifiedSOACompiler I) :
    compiler.decideAvoider = true ↔
      ∃ word, I.Critical word := by
  rw [compiler.decideAvoider_correct]
  exact I.exists_critical_iff_exists_avoider.symm

theorem decideNoAvoider_correct
    {I : SOAInstance α} (compiler : CertifiedSOACompiler I) :
    compiler.decideAvoider = false ↔
      ¬ ∃ word, I.Avoider word := by
  rw [← compiler.decideAvoider_correct]
  cases compiler.decideAvoider <;> simp

end CertifiedSOACompiler

end NSSE
