import NSSE.P0SuffixConflict
import NSSE.P0SuffixRankMap
import NSSE.P0DZCutSafety

/-! Full Entry makes actual D/Z cut suffix ranks nonincreasing. The
link-preservation premise of the abstract chain map is discharged by
four-rail comparison simulation and the exact suffix-conflict identity. -/
namespace NSSE.P0DZCutRank
open P0DZBranch P0DZTrace P0DZCutTrace P0DZCutSafety P0WordCuts
open P0SuffixRank P0SuffixConflict
variable {Q Z A H : Type*} {w : List A} {n : Nat}

theorem linked_transport (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (hl : Loops C J) (he : FullEntry C J)
    (a b : Nat) (hab : Linked J C.word a b) : Linked J w (C.lift a) (C.lift b) := by
  have horder := hab.1
  have hbn : b < n := by simpa using hab.2.1
  have han : a < n := by omega
  have hlt := C.increasing a b hab.1 (by omega)
  have hbound := C.lift_lt b hbn
  have hstate : properAt J w (C.lift a) = properAt J w (C.lift b) := by
    rw [← proper_transport C J hl a han,← proper_transport C J hl b hbn]
    exact hab.2.2.1
  apply (conflict_iff_linked J w hc hends (C.lift a) (C.lift b) hlt hbound hstate).mp
  intro hold
  have hnew : AllCompatible J C.word a b := fun s t =>
    compatible_transport C J hc hl he a b (by omega) s t (hold s t)
  exact nested_conflict J C.word (complete_cut C J hc hl) hends a b hab.1
    (Nat.le_of_lt hab.2.1) hab.2.2.2 hnew

variable [DecidableEq Q] [DecidableEq A]

theorem pointwise (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (hl : Loops C J) (he : FullEntry C J)
    (a : Nat) (ha : a ≤ n) : rank J C.word a ≤ rank J w (C.lift a) := by
  by_cases hap : a < n
  · apply P0SuffixRankMap.pointwise J C.word w C.lift
      (fun i hi => C.lift_lt i (by simpa using hi))
      (fun i j hij hj => C.increasing i j hij (by simpa using Nat.le_of_lt hj))
      (linked_transport C J hc hends hl he) a (by simpa using hap)
  · have hae : a = n := by omega
    subst a
    rw [rank_zero J C.word n (by simp),C.terminal,rank_zero J w w.length (by omega)]

theorem maximum (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (hl : Loops C J) (he : FullEntry C J) :
    maxRank J C.word ≤ maxRank J w := by
  exact P0SuffixRankMap.maximum J C.word w C.lift
    (fun i hi => C.lift_lt i (by simpa using hi))
    (fun i j hij hj => C.increasing i j hij (by simpa using Nat.le_of_lt hj))
    (linked_transport C J hc hends hl he)

theorem family_rank (J : Branch Q Z A H) (w : List A)
    (F : P0IntervalFamily.Family w.length) (hc : Complete J w)
    (hends : J.endX ≠ J.endY)
    (hl : ∀ b ∈ F.intervals, stateAt J w b.1 = stateAt J w b.2)
    (he : FullEntry (P0FamilyWordCut.cut w F) J) :
    maxRank J (P0FamilyWordCut.cut w F).word ≤ maxRank J w :=
  maximum _ J hc hends (family_loops J w F hl) he

end NSSE.P0DZCutRank
