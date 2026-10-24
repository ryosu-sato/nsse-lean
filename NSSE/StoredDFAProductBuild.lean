import NSSE.StoredDFAProductCells

namespace NSSE.StoredDFAProductBuild
open StoredDFAProductCells StoredOrdinaryDFABuild StoredForwardTableBuild
variable {d : Nat}

-- f is one primitive Boolean gate; instantiate by OR or AND in applications.
def build (A B : StoredOrdinaryDFABuild.Data) (f : Bool → Bool → Bool) : StoredOrdinaryDFABuild.Data × Nat :=
  let k := CountedSupportRule.mul A.count B.count
  let s := encode B.count A.start B.start
  let t := StoredProductTable.build A.count B.count (fun q r =>
    CountedFinEnumeration.tabulate d (fun i => StoredDFAProductCells.step A B q r i))
  let fs := StoredProductTable.build A.count B.count (StoredDFAProductCells.final A B f)
  (⟨k.1,s.1,t.1,fs.1⟩,1+k.2+s.2+t.2+fs.2)

def budget (n m d : Nat) := 2+m*(n+2)+encodeBudget n m+
  StoredProductTable.budget n m (tabBudget d (stepBudget n m d))+
  StoredProductTable.budget n m (1+n+m)

theorem bound (A B : StoredOrdinaryDFABuild.Data) (f : Bool → Bool → Bool)
    (ha : Valid (d := d) A) (hb : Valid (d := d) B) :
    (build (d := d) A B f).2 ≤ budget A.count B.count d := by
  have hs := encode_bound A.count B.count _ _ ha.start hb.start
  have ht := StoredProductTable.bound A.count B.count
    (tabBudget d (stepBudget A.count B.count d))
    (fun q r => CountedFinEnumeration.tabulate d (fun i => StoredDFAProductCells.step A B q r i))
    (fun q r => CountedFinEnumeration.tabulate_bound d _ _ (fun i => step_bound A B ha hb q r i))
  have hf := StoredProductTable.bound A.count B.count (1+A.count+B.count)
    (StoredDFAProductCells.final A B f) (final_bound A B f)
  simp only [build,budget,CountedSupportRule.mul_cost]; omega

theorem value (A B : FiniteSOARankDecision.InputDFA (Fin d)) (f : Bool → Bool → Bool) :
    (build (d := d) (snapshot A) (snapshot B) f).1 = snapshot (FiniteDFAOperations.product A B f) := by
  simp only [build,StoredProductTable.value,CountedFinEnumeration.tabulate_value,
    StoredDFAProductCells.step_value,StoredDFAProductCells.final_value,
    CountedSupportRule.mul_value,encode_value]
  simp only [StoredOrdinaryDFABuild.snapshot,FiniteDFAOperations.product,FiniteCapTerminal.reindex,
    FiniteDFAOperations.productRaw,Bool.decide_coe]
  rfl

theorem bound_snapshot (A B : FiniteSOARankDecision.InputDFA (Fin d)) (f : Bool → Bool → Bool) :
    (build (d := d) (snapshot A) (snapshot B) f).2 ≤ budget A.count B.count d :=
  bound _ _ f (valid_snapshot A) (valid_snapshot B)

theorem budget_mono (n m N M d : Nat) (hn : n≤N) (hm : m≤M) :
    budget n m d ≤ budget N M d := by
  unfold budget StoredProductTable.budget StoredForwardTableBuild.tabBudget
    stepBudget encodeBudget
  gcongr

theorem count (A B : StoredOrdinaryDFABuild.Data) (f : Bool → Bool → Bool) :
    (build (d := d) A B f).1.count = A.count*B.count := CountedSupportRule.mul_value _ _

theorem union_value (A B : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (snapshot A) (snapshot B) (· || ·)).1 =
      snapshot (FiniteDFAOperations.union A B) := value A B _

theorem inter_value (A B : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (snapshot A) (snapshot B) (· && ·)).1 =
      snapshot (FiniteDFAOperations.inter A B) := value A B _
end NSSE.StoredDFAProductBuild
