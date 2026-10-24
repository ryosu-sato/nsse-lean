import NSSE.HornCompiler
import NSSE.SOADecider

/-!
# From a finite Horn root theorem to the certified SOA decider

All Boolean-mask and least-fixed-point obligations are discharged by the
generic Horn kernel.  A concrete SOA compiler now needs only the genuine
semantic theorem identifying its root Horn derivations with avoiders.
-/

namespace NSSE

universe u

structure HornSOARootCertificate
    {α : Type u} (I : SOAInstance α) where
  compiler : FiniteHornCompiler
  root : Nat
  root_lt : root < compiler.stateCount
  root_correct :
    HornDerives compiler root ↔ ∃ word, I.Avoider word

namespace HornSOARootCertificate

def toCertifiedSOACompiler
    {I : SOAInstance α} (certificate : HornSOARootCertificate I) :
    CertifiedSOACompiler I where
  update := hornUpdate certificate.compiler
  initial := hornInitial certificate.compiler
  semantic := hornSemantic certificate.compiler
  rootIndex := certificate.root
  inflationary := hornUpdate_inflationary certificate.compiler
  monotone := hornUpdate_monotone certificate.compiler
  semantic_lfp := hornSemantic_lfp certificate.compiler
  root_correct := by
    rw [hornSemantic_bit_iff_derives
      certificate.compiler certificate.root certificate.root_lt]
    exact certificate.root_correct

def decideAvoider
    {I : SOAInstance α} (certificate : HornSOARootCertificate I) : Bool :=
  decideHornState certificate.compiler certificate.root

theorem decideAvoider_correct
    {I : SOAInstance α} (certificate : HornSOARootCertificate I) :
    certificate.decideAvoider = true ↔
      ∃ word, I.Avoider word := by
  rw [decideAvoider,
    decideHornState_correct certificate.compiler certificate.root
      certificate.root_lt]
  exact certificate.root_correct

theorem decideCritical_correct
    {I : SOAInstance α} (certificate : HornSOARootCertificate I) :
    certificate.decideAvoider = true ↔
      ∃ word, I.Critical word := by
  rw [certificate.decideAvoider_correct]
  exact I.exists_critical_iff_exists_avoider.symm

end HornSOARootCertificate

end NSSE
