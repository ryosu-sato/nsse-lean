import NSSE.StoredCapRegular

namespace NSSE.StoredRouteIdeal
variable {d : Nat}

def build (A : StoredOrdinaryDFABuild.Data) : StoredOrdinaryDFABuild.Data × Nat :=
  let t := StoredPaddingDecode.less A.start A.count
  if h : t.1 = true then
    let r := StoredRightIdealBuild.build (d := d) A ((StoredPaddingDecode.less_value _ _).mp h)
    (r.1,1+t.2+r.2)
  else
    let r := StoredDFAUnions.constant d false
    (r.1,1+t.2+r.2)

def budget (n d : Nat) := n+2+StoredRightIdealBuild.budget n d

theorem value (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A)).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteCapFrontEnd.rightIdeal A) := by
  unfold build
  dsimp only
  split
  · exact StoredRightIdealBuild.value A
  · rename_i h
    exact False.elim (h ((StoredPaddingDecode.less_value _ _).mpr A.automaton.start.isLt))

theorem bound (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A)).2 ≤ budget A.count d := by
  have ht := StoredPaddingDecode.less_bound A.automaton.start.val A.count
  have hr := StoredRightIdealBuild.bound (d := d) (StoredOrdinaryDFABuild.snapshot A) A.automaton.start.isLt
  change _ ≤ StoredRightIdealBuild.budget A.count d at hr
  unfold build
  dsimp only
  split
  · dsimp only
    unfold budget
    change (StoredPaddingDecode.less (StoredOrdinaryDFABuild.snapshot A).start
      (StoredOrdinaryDFABuild.snapshot A).count).2 ≤ A.count+1 at ht
    omega
  · rename_i h
    exact False.elim (h ((StoredPaddingDecode.less_value _ _).mpr A.automaton.start.isLt))

theorem count (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A)).1.count = 2^(A.count+1) := by
  unfold build
  dsimp only
  split
  · exact StoredRightIdealBuild.count _ _
  · rename_i h
    exact False.elim (h ((StoredPaddingDecode.less_value _ _).mpr A.automaton.start.isLt))

theorem original_count (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    (FiniteCapFrontEnd.rightIdeal A).count = 2^(A.count+1) := by
  have h := count A
  rw [value] at h
  exact h
end NSSE.StoredRouteIdeal
