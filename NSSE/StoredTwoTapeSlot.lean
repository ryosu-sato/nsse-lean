import NSSE.StoredArrayColumns

/-! Counted inverse sparse-slot lookup for the actual two-tape shapes. -/
namespace NSSE.StoredTwoTapeSlot
open ConvolutionShapes

def slot (s : Shape 2) (i : Fin 2) (hi : mask s i = true) : Fin (tapes (mask s)).length × Nat :=
  let a := FiniteValuationLookup.equalNat s.val 3
  (⟨if a.1 then i.val else 0,by
    fin_cases s <;> fin_cases i
    all_goals first | exact False.elim (Bool.noConfusion hi) | decide⟩,2+a.2)
theorem value (s : Shape 2) (i : Fin 2) (hi : mask s i = true) :
    (slot s i hi).1 = ConvolutionShapes.slot (mask s) i hi := by
  fin_cases s <;> fin_cases i
  all_goals first | exact False.elim (Bool.noConfusion hi) | rfl
theorem bound (s : Shape 2) (i : Fin 2) (hi : mask s i = true) : (slot s i hi).2 ≤ 6 := by
  have h := FiniteValuationLookup.equalNat_bound s.val 3
  have hs : s.val < 4 := s.isLt
  simp only [slot]; omega

def valueIndex {P : Type} (s : Shape 2) (i : Fin 2) (fallback : P) : (P ⊕ Fin (tapes (mask s)).length) × Nat :=
  let a := StoredTwoTapeShape.read s i
  if h : a.1 = true then
    let b := slot s i ((StoredTwoTapeShape.read_value s i).symm.trans h)
    (.inr b.1,3+a.2+b.2)
  else (.inl fallback,3+a.2)
theorem valueIndex_value {P : Type} (s : Shape 2) (i : Fin 2) (fallback : P) :
    (valueIndex s i fallback).1 = SymbolicGuardedBlocks.Row.valueIndex s i fallback := by
  by_cases h : mask s i = true <;>
    simp only [valueIndex,StoredTwoTapeShape.read_value,h,Bool.false_eq_true,↓reduceDIte,value,SymbolicGuardedBlocks.Row.valueIndex]
theorem valueIndex_bound {P : Type} (s : Shape 2) (i : Fin 2) (fallback : P) :
    (valueIndex s i fallback).2 ≤ 19 := by
  have ha := StoredTwoTapeShape.read_bound s i
  dsimp only [valueIndex]
  split
  · rename_i h
    have hb := bound s i ((StoredTwoTapeShape.read_value s i).symm.trans h)
    omega
  · omega
end NSSE.StoredTwoTapeSlot
