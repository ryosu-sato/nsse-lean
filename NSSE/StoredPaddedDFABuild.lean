import NSSE.StoredPaddedDFA

namespace NSSE.StoredPaddedDFABuild
open StoredOrdinaryDFABuild StoredForwardTableBuild
variable {d : Nat}

def build (A : StoredOrdinaryDFABuild.Data) : StoredOrdinaryDFABuild.Data × Nat :=
  let t := StoredOrdinaryDFABuild.rows (A.count+1) (d+2) (fun q i => StoredPaddedDFA.step A q i)
  let f := CountedFinEnumeration.tabulate (A.count+1) (StoredPaddedDFA.final A)
  (⟨A.count+1,A.start,t.1,f.1⟩,4+t.2+f.2)

def budget (n d : Nat) := 4+tabBudget (n+1) (tabBudget (d+2) (2*n+2*d+9))+
  tabBudget (n+1) (2*n+3)

theorem bound (A : StoredOrdinaryDFABuild.Data) : (build (d := d) A).2 ≤ budget A.count d := by
  have ht := StoredOrdinaryDFABuild.rows_bound (A.count+1) (d+2) (2*A.count+2*d+9)
    (fun q i => StoredPaddedDFA.step A q i) (fun q i => StoredPaddedDFA.step_bound A q i)
  have hf := CountedFinEnumeration.tabulate_bound (A.count+1) (StoredPaddedDFA.final A) (2*A.count+3)
    (StoredPaddedDFA.final_bound A)
  simp only [build,budget]
  dsimp only [tabBudget] at *
  omega

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (snapshot D)).1 = snapshot (PaddedAlphabetDFA.lift D) := by
  have hf (q : Fin (D.count+1)) : (StoredPaddedDFA.final (snapshot D) q).1 =
      decide ((PaddedAlphabetDFA.lift D).automaton.accept q) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredPaddedDFA.final_value D q
  simp only [build,StoredOrdinaryDFABuild.rows_value,CountedFinEnumeration.tabulate_value,
    StoredPaddedDFA.step_value,hf,StoredOrdinaryDFABuild.snapshot]
  congr 1
  · simp [PaddedAlphabetDFA.lift,FiniteCapTerminal.reindex,PaddedAlphabetDFA.raw,Fin.succAbove_last]
  · exact congrArg List.ofFn (funext (fun q => congrArg List.ofFn (funext (fun i => StoredPaddedDFA.step_value D q i))))
  · exact congrArg List.ofFn (funext hf)
end NSSE.StoredPaddedDFABuild
