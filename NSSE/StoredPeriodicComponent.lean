import NSSE.StoredCheckedPeriods

/-! Actual left-language concatenation with the checked bounded-period DFA.
The returned counter includes period construction, guard and concatenation. -/
namespace NSSE.StoredPeriodicComponent
variable {d : Nat}

def build (c : StoredNormalizationRows.Row) (b : Nat) : StoredOrdinaryDFABuild.Data × Nat :=
  let p := StoredCheckedPeriods.build (d := d) c.right b
  let g := StoredPaddingDecode.less p.1.start p.1.count
  if h : g.1=true then
    let r := StoredConcatBuild.build (d := d) c.left p.1 ((StoredPaddingDecode.less_value _ _).mp h)
    (r.1,2+p.2+g.2+r.2)
  else
    let r := StoredDFAUnions.constant d false
    (r.1,2+p.2+g.2+r.2)

theorem value (c : FiniteSOARankDecision.Component (Fin d)) (b : Nat) :
    (build (d := d) (StoredNormalizationRows.snapshot c) b).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteCapLive.periodicComponent (finEnumeration d) c b) := by
  have hg := (StoredPaddingDecode.less_value
    (FiniteBoundedPeriods.bounded (finEnumeration d) c.right b).automaton.start.val
    (FiniteBoundedPeriods.bounded (finEnumeration d) c.right b).count).mpr
    (FiniteBoundedPeriods.bounded (finEnumeration d) c.right b).automaton.start.isLt
  simp only [build,StoredNormalizationRows.snapshot,StoredCheckedPeriods.value]
  simp only [StoredOrdinaryDFABuild.snapshot] at hg ⊢
  simp only [hg,↓reduceDIte]
  exact StoredConcatBuild.value c.left (FiniteBoundedPeriods.bounded (finEnumeration d) c.right b)

theorem bound (c : FiniteSOARankDecision.Component (Fin d)) (b : Nat) :
    (build (d := d) (StoredNormalizationRows.snapshot c) b).2 ≤
      2+(StoredCheckedPeriods.build (d := d) (StoredOrdinaryDFABuild.snapshot c.right) b).2+
        ((FiniteBoundedPeriods.bounded (finEnumeration d) c.right b).count+1)+
        StoredConcatBuild.budget c.left.count
          (FiniteBoundedPeriods.bounded (finEnumeration d) c.right b).count d := by
  let B := FiniteBoundedPeriods.bounded (finEnumeration d) c.right b
  have hg := (StoredPaddingDecode.less_value B.automaton.start.val B.count).mpr B.automaton.start.isLt
  have hgc := StoredPaddingDecode.less_bound B.automaton.start.val B.count
  have ht := StoredConcatBuild.bound_snapshot c.left B
  simp only [build,StoredNormalizationRows.snapshot,StoredCheckedPeriods.value]
  dsimp only [B] at hg hgc ht
  simp only [StoredOrdinaryDFABuild.snapshot] at hg ⊢
  simp only [hg,↓reduceDIte]
  exact Nat.add_le_add (Nat.add_le_add_left hgc _) ht
end NSSE.StoredPeriodicComponent
