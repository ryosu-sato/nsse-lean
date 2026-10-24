import NSSE.HornSOACompiler

/-!
# Finite aggregation of verified Horn compiler families

Each family member supplies a finite compiler and an in-range root.
The aggregator accepts exactly when at least one member root is
derivable, and exposes that disjunction as one finite Horn root.
-/

namespace NSSE

universe u

structure HornFamily where
  compiler : FiniteHornCompiler
  root : Nat
  root_lt : root < compiler.stateCount

def decideHornFamilies (families : List HornFamily) : Bool :=
  families.any fun family =>
    decideHornState family.compiler family.root

theorem decideHornFamilies_correct (families : List HornFamily) :
    decideHornFamilies families = true ↔
      ∃ family ∈ families,
        HornDerives family.compiler family.root := by
  induction families with
  | nil =>
      simp [decideHornFamilies]
  | cons family families ih =>
      simp only [decideHornFamilies, List.any_cons, Bool.or_eq_true]
      rw [decideHornState_correct
        family.compiler family.root family.root_lt]
      change
        (HornDerives family.compiler family.root ∨
          decideHornFamilies families = true) ↔ _
      rw [ih]
      constructor
      · rintro (hhead | htail)
        · exact ⟨family, by simp, hhead⟩
        · obtain ⟨member, hmem, hderive⟩ := htail
          exact ⟨member, by simp [hmem], hderive⟩
      · rintro ⟨member, hmem, hderive⟩
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact Or.inl hderive
        · exact Or.inr ⟨member, hmem, hderive⟩

def familyRootRule : HornRule where
  parent := 1
  children := [0]

def hornFamilyCompiler (families : List HornFamily) :
    FiniteHornCompiler where
  stateCount := 2
  terminal := fun state =>
    if state = 0 then decideHornFamilies families else false
  rules := [familyRootRule]

theorem decideHornFamilyTerminal (families : List HornFamily) :
    decideHornState (hornFamilyCompiler families) 0 =
      decideHornFamilies families := by
  simp [decideHornState, hornFamilyCompiler, hornInitial,
    iterateMask, hornUpdate, hornBuild, hornNewBit, hornFires,
    allMaskBits, familyRootRule, maskBit, decideLeastFixedPoint]

theorem decideHornFamilyRoot (families : List HornFamily) :
    decideHornState (hornFamilyCompiler families) 1 =
      decideHornFamilies families := by
  simp [decideHornState, hornFamilyCompiler, hornInitial,
    iterateMask, hornUpdate, hornBuild, hornNewBit, hornFires,
    allMaskBits, familyRootRule, maskBit, decideLeastFixedPoint]

theorem hornFamilyRoot_derives_iff (families : List HornFamily) :
    HornDerives (hornFamilyCompiler families) 1 ↔
      ∃ family ∈ families,
        HornDerives family.compiler family.root := by
  rw [← decideHornFamilies_correct,
    ← decideHornFamilyRoot,
    decideHornState_correct
      (hornFamilyCompiler families) 1 (by
        simp [hornFamilyCompiler])]

structure HornFamilySOACertificate
    {α : Type u} (I : SOAInstance α) where
  families : List HornFamily
  root_correct :
    (∃ family ∈ families,
      HornDerives family.compiler family.root) ↔
      ∃ word, I.Avoider word

namespace HornFamilySOACertificate

def toHornRootCertificate
    {I : SOAInstance α} (certificate : HornFamilySOACertificate I) :
    HornSOARootCertificate I where
  compiler := hornFamilyCompiler certificate.families
  root := 1
  root_lt := by simp [hornFamilyCompiler]
  root_correct := by
    rw [hornFamilyRoot_derives_iff]
    exact certificate.root_correct

def toCertifiedSOACompiler
    {I : SOAInstance α} (certificate : HornFamilySOACertificate I) :
    CertifiedSOACompiler I :=
  certificate.toHornRootCertificate.toCertifiedSOACompiler

def decideAvoider
    {I : SOAInstance α} (certificate : HornFamilySOACertificate I) :
    Bool :=
  decideHornFamilies certificate.families

theorem decideAvoider_correct
    {I : SOAInstance α} (certificate : HornFamilySOACertificate I) :
    certificate.decideAvoider = true ↔
      ∃ word, I.Avoider word := by
  rw [decideAvoider, decideHornFamilies_correct]
  exact certificate.root_correct

end HornFamilySOACertificate

end NSSE
