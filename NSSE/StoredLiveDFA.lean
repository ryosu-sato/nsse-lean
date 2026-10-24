import NSSE.StoredNonliveDFA

/-! Construct the live-state final table by counted backward extension.
No arbitrary-length extension oracle is evaluated by this builder. -/
namespace NSSE.StoredLiveDFA
variable {d : Nat}

def original (A : FiniteSOARankDecision.InputDFA (Fin d)) : FiniteSOARankDecision.InputDFA (Fin d) :=
  ⟨A.count,NonliveBorderRank.liveDFA A.automaton,inferInstance⟩

def build (A : StoredOrdinaryDFABuild.Data) : StoredOrdinaryDFABuild.Data × Nat :=
  let e := StoredDFAExtensions.build (d := d) A A.count
  ({A with final := e.1},1+e.2)

def budget (n d : Nat) := 1+StoredDFAExtensions.budget n d n

theorem bound (A : StoredOrdinaryDFABuild.Data)
    (h : StoredDFAProductCells.Valid (d := d) A) :
    (build (d := d) A).2 ≤ budget A.count d := by
  have he := StoredDFAExtensions.bound A h A.count
  simp only [build,budget]
  omega

theorem value (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A)).1 =
      StoredOrdinaryDFABuild.snapshot (original A) := by
  simp only [build,StoredDFAExtensions.value]
  have hf : (fun q => decide (StoredDFAExtensions.possible A A.count q)) =
      (fun q => decide ((NonliveBorderRank.liveDFA A.automaton).accept q)) := by
    funext q
    exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using StoredNonliveDFA.possible_live A q)
  change {StoredOrdinaryDFABuild.snapshot A with final := List.ofFn (fun q => decide (StoredDFAExtensions.possible A A.count q))} = _
  rw [hf]
  rfl

theorem bound_snapshot (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A)).2 ≤ budget A.count d :=
  bound _ (StoredDFAProductCells.valid_snapshot A)
end NSSE.StoredLiveDFA
