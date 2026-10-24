import NSSE.NormalizedEnumeration
import NSSE.FiniteControl

/-!
# Canonical finite colors for control values

The factor-forest-to-split conversion colors an idempotent level by its
control value.  A normalized enumeration gives a canonical finite index for
each value and a total idempotent decoding function for all indices.
-/

namespace NSSE

universe v

theorem getElem_idxOf_eq
    [DecidableEq α] {value : α}
    (values : List α) (hmem : value ∈ values) :
    values[values.idxOf value]'(
      List.idxOf_lt_length hmem) = value := by
  induction values with
  | nil =>
      simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      by_cases heq : head = value
      · subst head
        simp
      · have htail : value ∈ tail := by
          exact hmem.resolve_left (Ne.symm heq)
        have hbeq : (head == value) = false := by
          simp [heq]
        simpa [List.idxOf_cons, hbeq] using ih htail

namespace Enumeration

def canonicalIndex
    [DecidableEq M] (elements : Enumeration M)
    (value : M) :
    Fin elements.normalized.values.length :=
  ⟨elements.normalized.values.idxOf value,
    List.idxOf_lt_length
      (elements.normalized.complete value)⟩

def valueAt
    [DecidableEq M] (elements : Enumeration M)
    (index : Fin elements.normalized.values.length) : M :=
  elements.normalized.values[index]

@[simp] theorem valueAt_canonicalIndex
    [DecidableEq M] (elements : Enumeration M)
    (value : M) :
    elements.valueAt (elements.canonicalIndex value) =
      value := by
  exact getElem_idxOf_eq
    elements.normalized.values
    (elements.normalized.complete value)

theorem normalized_length_pos
    [DecidableEq M] (elements : Enumeration M)
    (value : M) :
    0 < elements.normalized.values.length := by
  have hmem := elements.normalized.complete value
  exact List.length_pos_iff.mpr
    (List.ne_nil_of_mem hmem)

end Enumeration

namespace ControlMonoid

def idempotentColor
    [DecidableEq M] (C : ControlMonoid M)
    (elements : Enumeration M)
    (index : Fin elements.normalized.values.length) : M :=
  let value := elements.valueAt index
  if C.mul value value = value then value else C.one

theorem idempotentColor_idempotent
    [DecidableEq M] (C : ControlMonoid M)
    (elements : Enumeration M)
    (index : Fin elements.normalized.values.length) :
    C.Idempotent (C.idempotentColor elements index) := by
  change C.mul
      (C.idempotentColor elements index)
      (C.idempotentColor elements index) =
    C.idempotentColor elements index
  unfold idempotentColor
  dsimp only
  split
  · assumption
  · exact C.mul_one C.one

@[simp] theorem idempotentColor_canonicalIndex
    [DecidableEq M] (C : ControlMonoid M)
    (elements : Enumeration M) (value : M)
    (hvalue : C.Idempotent value) :
    C.idempotentColor elements
        (elements.canonicalIndex value) =
      value := by
  unfold Idempotent at hvalue
  simp [idempotentColor, hvalue]

end ControlMonoid

end NSSE
