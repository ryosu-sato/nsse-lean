import NSSE.StoredPaddedDFABuild
import NSSE.PaddedCapInput

namespace NSSE.StoredForeignDFA
variable {d : Nat}

def step (q : Fin 2) (x : Fin (d+2)) : Nat × Nat :=
  let b := FiniteValuationLookup.equalNat q.val 1
  let l := StoredPaddingDecode.classify d x.val
  (if b.1 || l.1.isNone then 1 else 0,2+b.2+l.2)

theorem step_bound (q : Fin 2) (x : Fin (d+2)) : (step q x).2 ≤ d+6 := by
  have hb := (FiniteValuationLookup.equalNat_bound q.val 1).trans q.isLt
  have hl := StoredPaddingDecode.classify_bound d x.val
  simp only [step]; omega

theorem step_value (q : Fin 2) (x : Fin (d+2)) : (step q x).1 =
    ((PaddedCapInput.foreignDFA (d := d)).automaton.step q x).val := by
  cases hl : PaddedAlphabetDFA.letter x <;> fin_cases q <;>
    simp [step,FiniteValuationLookup.equalNat,StoredPaddingDecode.letter_value,
      PaddedCapInput.foreignDFA,FiniteCapTerminal.reindex,PaddedCapInput.foreignRaw,hl] <;> rfl

def build (d : Nat) : StoredOrdinaryDFABuild.Data × Nat :=
  let t := StoredOrdinaryDFABuild.rows 2 (d+2) (fun q x => step q x)
  (⟨2,0,t.1,[false,true]⟩,6+t.2)

def budget (d : Nat) := 6+StoredForwardTableBuild.tabBudget 2
  (StoredForwardTableBuild.tabBudget (d+2) (d+6))

theorem bound (d : Nat) : (build d).2 ≤ budget d :=
  Nat.add_le_add_left (StoredOrdinaryDFABuild.rows_bound 2 (d+2) (d+6) (fun q x => step q x) step_bound) 6

theorem value (d : Nat) : (build d).1 =
    StoredOrdinaryDFABuild.snapshot (PaddedCapInput.foreignDFA (d := d)) := by
  simp only [build,StoredOrdinaryDFABuild.rows_value,step_value,StoredOrdinaryDFABuild.snapshot]
  rfl
end NSSE.StoredForeignDFA
