import NSSE.StoredNonliveDFA

namespace NSSE.StoredResidualDFA
variable {d : Nat}

def build (G R : StoredOrdinaryDFABuild.Data) : StoredOrdinaryDFABuild.Data × Nat :=
  let g := StoredNonliveDFA.build (d := d) G
  let r := StoredDFAComplement.build R
  let p := StoredDFAProductBuild.build (d := d) g.1 r.1 (· && ·)
  (p.1,2+g.2+r.2+p.2)

def budget (n m d : Nat) := 2+StoredNonliveDFA.budget n d+
  StoredDFAComplement.budget m+StoredDFAProductBuild.budget n m d

theorem value (G R : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot G) (StoredOrdinaryDFABuild.snapshot R)).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteCapTerminal.residual G R) := by
  simp only [build,StoredNonliveDFA.value,StoredDFAComplement.value,StoredDFAProductBuild.inter_value]
  simp only [StoredOrdinaryDFABuild.snapshot,FiniteDFAOperations.inter,FiniteDFAOperations.product,
    FiniteDFAOperations.productRaw,FiniteCapTerminal.residual,FiniteCapTerminal.residualRaw,
    FiniteCapTerminal.reindex,StoredNonliveDFA.original,FiniteDFAOperations.complement,
    Bool.decide_coe,Bool.decide_and,decide_not]
  rfl

theorem bound (G R : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot G) (StoredOrdinaryDFABuild.snapshot R)).2 ≤
      budget G.count R.count d := by
  have hg := StoredNonliveDFA.bound_snapshot G
  have hr := StoredDFAComplement.bound (StoredOrdinaryDFABuild.snapshot R)
  change _ ≤ StoredDFAComplement.budget R.count at hr
  have hp := StoredDFAProductBuild.bound (d := d)
    (StoredNonliveDFA.build (d := d) (StoredOrdinaryDFABuild.snapshot G)).1
    (StoredDFAComplement.build (StoredOrdinaryDFABuild.snapshot R)).1 (· && ·)
    (by rw [StoredNonliveDFA.value]; exact StoredDFAProductCells.valid_snapshot _)
    (by rw [StoredDFAComplement.value]; exact StoredDFAProductCells.valid_snapshot _)
  change _ ≤ StoredDFAProductBuild.budget G.count R.count d at hp
  simp only [build,budget]; omega

theorem count (G R : StoredOrdinaryDFABuild.Data) :
    (build (d := d) G R).1.count = G.count*R.count := by
  simp only [build,StoredDFAProductBuild.count]
  rfl
end NSSE.StoredResidualDFA
