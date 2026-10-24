import NSSE.FiniteTransformationMonoid
import Lean.Elab.Tactic.Omega

/-!
# Constructive list pigeonhole lemmas

If a duplicate-free list is contained in a finite universe, its length is
at most the universe length.  Consequently every longer list has an
explicit two-occurrence decomposition.
-/

namespace NSSE

universe u

theorem nodup_length_le_of_subset_list
    [DecidableEq α]
    {values ambient : List α}
    (hnodup : values.Nodup)
    (hsubset : ∀ x ∈ values, x ∈ ambient) :
    values.length ≤ ambient.length := by
  induction values generalizing ambient with
  | nil => simp
  | cons head tail ih =>
      have hheadNotMem : head ∉ tail :=
        (List.nodup_cons.mp hnodup).1
      have htailNodup : tail.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hheadUniverse : head ∈ ambient :=
        hsubset head (by simp)
      have htailSubset :
          ∀ x ∈ tail, x ∈ ambient.erase head := by
        intro x hx
        have hxne : x ≠ head := by
          intro heq
          subst x
          exact hheadNotMem hx
        exact (List.mem_erase_of_ne hxne).2
          (hsubset x (by simp [hx]))
      have htailLength :=
        ih htailNodup htailSubset
      rw [List.length_erase_of_mem hheadUniverse] at htailLength
      simp only [List.length_cons]
      have hambientPositive : 0 < ambient.length :=
        List.length_pos_iff.mpr (by
          intro hempty
          subst ambient
          simp at hheadUniverse)
      omega

theorem List.not_nodup_exists_repeated_decomposition
    [DecidableEq α]
    {values : List α}
    (hnodup : ¬ values.Nodup) :
    ∃ before middle after x,
      values = before ++ x :: middle ++ x :: after := by
  induction values with
  | nil =>
      exact False.elim (hnodup (by simp))
  | cons head tail ih =>
      by_cases hhead : head ∈ tail
      · obtain ⟨middle, after, htail⟩ :=
          List.append_of_mem hhead
        exact ⟨[], middle, after, head, by
          simp [htail, List.append_assoc]⟩
      · have htailNotNodup : ¬ tail.Nodup := by
          intro htail
          exact hnodup (List.nodup_cons.mpr ⟨hhead, htail⟩)
        obtain ⟨before, middle, after, x, htail⟩ :=
          ih htailNotNodup
        exact ⟨head :: before, middle, after, x, by
          simp [htail, List.append_assoc]⟩

theorem List.exists_repeated_decomposition_of_subset_of_length_lt
    [DecidableEq α]
    {values ambient : List α}
    (hsubset : ∀ x ∈ values, x ∈ ambient)
    (hlength : ambient.length < values.length) :
    ∃ before middle after x,
      values = before ++ x :: middle ++ x :: after := by
  apply List.not_nodup_exists_repeated_decomposition
  intro hnodup
  have := nodup_length_le_of_subset_list hnodup hsubset
  omega

end NSSE
