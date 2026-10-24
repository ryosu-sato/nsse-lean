import NSSE.TaggedCompiler
import Lean.Elab.Tactic.Omega

/-!
# Duplicate-free normalization of finite enumerations

Enumeration lists may contain duplicates, so their raw length is not a
valid induction measure.  The executable normalization below preserves
membership and completeness while producing a `Nodup` value list.
-/

namespace NSSE

universe u

def deduplicate [DecidableEq α] : List α → List α
  | [] => []
  | head :: tail =>
      let normalizedTail := deduplicate tail
      if head ∈ normalizedTail then
        normalizedTail
      else
        head :: normalizedTail

@[simp] theorem mem_deduplicate
    [DecidableEq α] (value : α) :
    ∀ values : List α,
      value ∈ deduplicate values ↔ value ∈ values := by
  intro values
  induction values with
  | nil => simp [deduplicate]
  | cons head tail ih =>
      simp only [deduplicate]
      split
      next hmem =>
        constructor
        · intro hvalue
          exact List.mem_cons_of_mem head ((ih).1 hvalue)
        · intro hvalue
          simp only [List.mem_cons] at hvalue
          rcases hvalue with rfl | htail
          · exact hmem
          · exact (ih).2 htail
      next hnot =>
        simp only [List.mem_cons, ih]

theorem deduplicate_nodup
    [DecidableEq α] :
    ∀ values : List α, (deduplicate values).Nodup := by
  intro values
  induction values with
  | nil => simp [deduplicate]
  | cons head tail ih =>
      simp only [deduplicate]
      split
      next => exact ih
      next hnot =>
        exact List.nodup_cons.mpr ⟨hnot, ih⟩

theorem deduplicate_length_le
    [DecidableEq α] :
    ∀ values : List α,
      (deduplicate values).length ≤ values.length := by
  intro values
  induction values with
  | nil => simp [deduplicate]
  | cons head tail ih =>
      simp only [deduplicate]
      split
      next =>
        simp only [List.length_cons]
        omega
      next =>
        simp only [List.length_cons]
        omega

def Enumeration.normalized
    [DecidableEq α] (enumeration : Enumeration α) :
    Enumeration α where
  values := deduplicate enumeration.values
  complete := by
    intro value
    exact (mem_deduplicate value enumeration.values).2
      (enumeration.complete value)

theorem Enumeration.normalized_nodup
    [DecidableEq α] (enumeration : Enumeration α) :
    enumeration.normalized.values.Nodup :=
  deduplicate_nodup enumeration.values

@[simp] theorem Enumeration.mem_normalized_values
    [DecidableEq α] (enumeration : Enumeration α) (value : α) :
    value ∈ enumeration.normalized.values := by
  exact enumeration.normalized.complete value

theorem Enumeration.normalized_length_le
    [DecidableEq α] (enumeration : Enumeration α) :
    enumeration.normalized.values.length ≤ enumeration.values.length :=
  deduplicate_length_le enumeration.values

def Enumeration.without
    [DecidableEq α] (enumeration : Enumeration α) (removed : α) :
    List α :=
  enumeration.normalized.values.erase removed

theorem Enumeration.without_nodup
    [DecidableEq α] (enumeration : Enumeration α) (removed : α) :
    (enumeration.without removed).Nodup :=
  (enumeration.normalized_nodup).erase removed

@[simp] theorem Enumeration.mem_without
    [DecidableEq α] (enumeration : Enumeration α)
    (removed value : α) :
    value ∈ enumeration.without removed ↔ value ≠ removed := by
  constructor
  · intro hmem heq
    subst value
    exact List.Nodup.not_mem_erase
      enumeration.normalized_nodup hmem
  · intro hne
    exact (List.mem_erase_of_ne hne).2
      (enumeration.normalized.complete value)

theorem Enumeration.without_length_lt
    [DecidableEq α] (enumeration : Enumeration α) (removed : α) :
    (enumeration.without removed).length <
      enumeration.normalized.values.length := by
  rw [Enumeration.without, List.length_erase_of_mem]
  · have hpositive :
        0 < enumeration.normalized.values.length :=
      List.length_pos_iff.mpr (by
        intro hempty
        have := enumeration.normalized.complete removed
        rw [hempty] at this
        simp at this)
    omega
  · exact enumeration.normalized.complete removed

end NSSE
