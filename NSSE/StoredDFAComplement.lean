import NSSE.StoredDFAAccess

namespace NSSE.StoredDFAComplement
open StoredOrdinaryDFABuild
variable {d : Nat}

def build (A : Data) : Data × Nat :=
  let f := CountedFinEnumeration.tabulate A.count (fun q =>
    let r := StoredDFAAccess.final A q
    (!r.1,1+r.2))
  ({A with final := f.1},1+f.2)

def budget (k : Nat) := 1+StoredForwardTableBuild.tabBudget k (k+1)

theorem bound (A : Data) : (build A).2 ≤ budget A.count := by
  have hf := CountedFinEnumeration.tabulate_bound A.count
    (fun q => let r := StoredDFAAccess.final A q; (!r.1,1+r.2)) (A.count+1)
    (fun q => by have h := StoredDFAAccess.final_bound A q; dsimp only; omega)
  exact Nat.add_le_add_left hf 1

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (snapshot D)).1 = snapshot (FiniteDFAOperations.complement D) := by
  have hf (q : Fin D.count) : (!(StoredDFAAccess.final (snapshot D) q).1) =
      decide (¬ D.automaton.accept q) := by
    simp only [StoredDFAAccess.final,snapshot,StoredForwardLookup.get_ofFn,decide_not]
  simp only [build,CountedFinEnumeration.tabulate_value,hf,snapshot,FiniteDFAOperations.complement,StoredDFAAccess.final,
    StoredForwardLookup.get_ofFn,decide_not]

theorem final_length (A : Data) : (build A).1.final.length = A.count := by
  simp only [build,CountedFinEnumeration.tabulate_value,List.length_ofFn]
end NSSE.StoredDFAComplement
