import NSSE.StoredConcatBuild
import NSSE.StoredDFAUnions
import NSSE.StoredPrefixClosureBuild

namespace NSSE.StoredComponentRegular
variable {d : Nat}

def core (c : StoredNormalizationRows.Row) (h : c.right.start<c.right.count) :
    StoredOrdinaryDFABuild.Data × Nat :=
  let l := StoredPrefixClosureBuild.build (d := d) c.left
  let r := StoredPrefixClosureBuild.build (d := d) c.right
  let t := StoredConcatBuild.build (d := d) c.left r.1 h
  let u := StoredDFAProductBuild.build (d := d) l.1 t.1 (· || ·)
  (u.1,3+l.2+r.2+t.2+u.2)

def build (c : StoredNormalizationRows.Row) : StoredOrdinaryDFABuild.Data × Nat :=
  let t := StoredPaddingDecode.less c.right.start c.right.count
  if h : t.1 = true then
    let r := core (d := d) c ((StoredPaddingDecode.less_value _ _).mp h)
    (r.1,1+t.2+r.2)
  else
    let r := StoredDFAUnions.constant d false
    (r.1,1+t.2+r.2)

def coreBudget (n m d : Nat) := 3+StoredPrefixClosureBuild.budget n d+
  StoredPrefixClosureBuild.budget m d+StoredConcatBuild.budget n m d+
  StoredDFAProductBuild.budget n (2^(n+m)) d

def budget (n m d : Nat) := m+2+coreBudget n m d

theorem core_value (c : FiniteSOARankDecision.Component (Fin d))
    (h : (StoredNormalizationRows.snapshot c).right.start < (StoredNormalizationRows.snapshot c).right.count) :
    (core (d := d) (StoredNormalizationRows.snapshot c) h).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteCapFrontEnd.componentRegular c) := by
  simp only [core,StoredNormalizationRows.snapshot,StoredPrefixClosureBuild.value,
    StoredConcatBuild.value,StoredDFAProductBuild.union_value]
  rfl

theorem value (c : FiniteSOARankDecision.Component (Fin d)) :
    (build (d := d) (StoredNormalizationRows.snapshot c)).1 =
      StoredOrdinaryDFABuild.snapshot (FiniteCapFrontEnd.componentRegular c) := by
  unfold build
  dsimp only
  split
  · exact core_value c _
  · rename_i h
    exact False.elim (h ((StoredPaddingDecode.less_value _ _).mpr c.right.automaton.start.isLt))

theorem core_bound (c : FiniteSOARankDecision.Component (Fin d))
    (h : (StoredNormalizationRows.snapshot c).right.start < (StoredNormalizationRows.snapshot c).right.count) :
    (core (d := d) (StoredNormalizationRows.snapshot c) h).2 ≤ coreBudget c.left.count c.right.count d := by
  let l := StoredPrefixClosureBuild.build (d := d) (StoredOrdinaryDFABuild.snapshot c.left)
  let r := StoredPrefixClosureBuild.build (d := d) (StoredOrdinaryDFABuild.snapshot c.right)
  let t := StoredConcatBuild.build (d := d) (StoredOrdinaryDFABuild.snapshot c.left) r.1 h
  have hl := StoredPrefixClosureBuild.bound (d := d) (StoredOrdinaryDFABuild.snapshot c.left)
  have hr := StoredPrefixClosureBuild.bound (d := d) (StoredOrdinaryDFABuild.snapshot c.right)
  have ht := StoredConcatBuild.bound (d := d) (StoredOrdinaryDFABuild.snapshot c.left) r.1 h
  have hu : (StoredDFAProductBuild.build (d := d) l.1 t.1 (· || ·)).2 ≤
      StoredDFAProductBuild.budget c.left.count (2^(c.left.count+c.right.count)) d := by
    have vl : l.1 = StoredOrdinaryDFABuild.snapshot (FiniteDFAOperations.prefixClosure c.left) := StoredPrefixClosureBuild.value _
    have vt : t.1 = StoredOrdinaryDFABuild.snapshot
        (FiniteDFAConcat.concat c.left (FiniteDFAOperations.prefixClosure c.right)) := by
      dsimp only [t,r]
      simp only [StoredPrefixClosureBuild.value,StoredConcatBuild.value]
    have hh := StoredDFAProductBuild.bound (d := d) l.1 t.1 (· || ·)
      (by rw [vl]; exact StoredDFAProductCells.valid_snapshot _)
      (by rw [vt]; exact StoredDFAProductCells.valid_snapshot _)
    have hc : t.1.count = 2^(c.left.count+c.right.count) := StoredConcatBuild.count _ _ _
    rw [hc] at hh
    exact hh
  change _ ≤ StoredConcatBuild.budget c.left.count c.right.count d at ht
  dsimp only [l,r,t] at hu ht
  change _ ≤ StoredPrefixClosureBuild.budget c.left.count d at hl
  change _ ≤ StoredPrefixClosureBuild.budget c.right.count d at hr
  simp only [core,coreBudget,StoredNormalizationRows.snapshot]
  omega

theorem bound (c : FiniteSOARankDecision.Component (Fin d)) :
    (build (d := d) (StoredNormalizationRows.snapshot c)).2 ≤ budget c.left.count c.right.count d := by
  have ht := StoredPaddingDecode.less_bound c.right.automaton.start.val c.right.count
  unfold build
  dsimp only
  split
  · have h := core_bound c c.right.automaton.start.isLt
    dsimp only
    unfold budget
    change (StoredPaddingDecode.less (StoredNormalizationRows.snapshot c).right.start
      (StoredNormalizationRows.snapshot c).right.count).2 ≤ c.right.count+1 at ht
    omega
  · rename_i h
    exact False.elim (h ((StoredPaddingDecode.less_value _ _).mpr c.right.automaton.start.isLt))
theorem count (c : FiniteSOARankDecision.Component (Fin d)) :
    (build (d := d) (StoredNormalizationRows.snapshot c)).1.count =
      c.left.count*2^(c.left.count+c.right.count) := by
  unfold build
  dsimp only
  split
  · simp only [core,StoredDFAProductBuild.count,StoredConcatBuild.count]
    rfl
  · rename_i h
    exact False.elim (h ((StoredPaddingDecode.less_value _ _).mpr c.right.automaton.start.isLt))

theorem original_count (c : FiniteSOARankDecision.Component (Fin d)) :
    (FiniteCapFrontEnd.componentRegular c).count = c.left.count*2^(c.left.count+c.right.count) := by
  have h := count c
  rw [value] at h
  exact h
end NSSE.StoredComponentRegular
