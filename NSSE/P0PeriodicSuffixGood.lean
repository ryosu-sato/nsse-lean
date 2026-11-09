import NSSE.P0PeriodicBlocks

/-! The regular suffix condition supplies the entire additional safety
inspection window. Good remains a separate predicate on the full history. -/
namespace NSSE.P0PeriodicSuffixGood
open P0ProperMachine P0ProperWords P0PeriodicDriver P0PeriodicInspection
open P0PeriodicInspectionDecision P0PeriodicBlocks
variable {Q A H : Type*} [Fintype Q] {r : Nat}

def copies (N : Nat) : Nat := N^2+N+1

def pattern (Q : Type*) [Fintype Q] (hr : 0 < r) (cycle : Fin r → A) : List A :=
  block hr cycle (copies (Fintype.card Q))

theorem pattern_length (hr : 0 < r) (cycle : Fin r → A) :
    (pattern Q hr cycle).length = horizon (Fintype.card Q) r := by
  rw [pattern,block_length,horizon_eq]
  rfl

theorem good_iff_block (M : Machine Q A H) (stem : List A) (hr : 0 < r) (cycle : Fin r → A) :
    Good M (lasso stem hr cycle) ↔ GoodWord M (stem++pattern Q hr cycle) := by
  have hs : Spells (lasso stem hr cycle) (stem++pattern Q hr cycle) :=
    append_spells stem hr cycle (copies (Fintype.card Q))
  rw [goodWord_iff_stream M _ (lasso stem hr cycle) hs,List.length_append,pattern_length]
  exact good_iff_inspected M (lasso stem hr cycle) stem.length r hr cycle (lasso_periodic stem hr cycle)

theorem suffix_good_iff (M : Machine Q A H) (w : List A) (hr : 0 < r) (cycle : Fin r → A)
    (hs : (pattern Q hr cycle).IsSuffix w) :
    GoodWord M w ↔ Good M (lasso w hr cycle) := by
  obtain ⟨stem,rfl⟩ := hs
  rw [show lasso (stem++pattern Q hr cycle) hr cycle = lasso stem hr cycle from
    lasso_append stem hr cycle (copies (Fintype.card Q))]
  exact (good_iff_block M stem hr cycle).symm

theorem suffix_extend (M : Machine Q A H) (w : List A) (hr : 0 < r) (cycle : Fin r → A)
    (hs : (pattern Q hr cycle).IsSuffix w) (hw : GoodWord M w) :
    Good M (lasso w hr cycle) := (suffix_good_iff M w hr cycle hs).mp hw

end NSSE.P0PeriodicSuffixGood
