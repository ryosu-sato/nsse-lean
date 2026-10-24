import NSSE.LocalDivisorControl

/-!
# Decomposition at every occurrence of a pivot

`PivotGapDecomposition pivot word gaps` records all maximal pivot-free gaps,
including empty endpoint or consecutive-pivot gaps.  The custom join operation
reconstructs the word by inserting exactly one pivot between adjacent gaps.
This relational presentation keeps the induction equations simple and avoids
depending on a library string-splitting API.
-/

namespace NSSE

universe u

def joinPivotGaps (pivot : α) : List (Word α) → Word α
  | [] => []
  | [gap] => gap
  | gap :: next :: rest =>
      gap ++ pivot :: joinPivotGaps pivot (next :: rest)

theorem joinPivotGaps_append
    (pivot : α)
    (left right : List (Word α))
    (hleft : left ≠ [])
    (hright : right ≠ []) :
    joinPivotGaps pivot (left ++ right) =
      joinPivotGaps pivot left ++
        pivot :: joinPivotGaps pivot right := by
  cases left with
  | nil =>
      exact False.elim (hleft rfl)
  | cons head tail =>
      induction tail generalizing head with
      | nil =>
          cases right with
          | nil =>
              exact False.elim (hright rfl)
          | cons next rest =>
              simp [joinPivotGaps]
      | cons next tail ih =>
          simp only [List.cons_append,
            joinPivotGaps]
          have htail := ih next (by simp)
          simp only [List.cons_append] at htail
          rw [htail]
          simp only [List.append_assoc,
            List.cons_append]

theorem joinPivotGaps_append_three
    (pivot : α)
    (before middle after : List (Word α))
    (hbefore : before ≠ [])
    (hmiddle : middle ≠ [])
    (hafter : after ≠ []) :
    joinPivotGaps pivot
        (before ++ middle ++ after) =
      joinPivotGaps pivot before ++
        pivot :: joinPivotGaps pivot middle ++
          pivot :: joinPivotGaps pivot after := by
  rw [joinPivotGaps_append pivot
    (before ++ middle) after
    (List.append_ne_nil_of_left_ne_nil hbefore middle)
    hafter]
  rw [joinPivotGaps_append pivot
    before middle hbefore hmiddle]

theorem flatMap_append_pivot_eq_join_append
    (pivot : α) :
    ∀ gaps : List (Word α), gaps ≠ [] →
      gaps.flatMap (fun gap => gap ++ [pivot]) =
        joinPivotGaps pivot gaps ++ [pivot] := by
  intro gaps hgaps
  cases gaps with
  | nil =>
      exact False.elim (hgaps rfl)
  | cons gap rest =>
      induction rest generalizing gap with
      | nil =>
          simp [joinPivotGaps]
      | cons next rest ih =>
          have htail :=
            ih next (by simp)
          change
            (gap ++ [pivot]) ++
                (next :: rest).flatMap
                  (fun current => current ++ [pivot]) =
              (gap ++
                  pivot ::
                    joinPivotGaps pivot
                      (next :: rest)) ++ [pivot]
          rw [htail]
          simp only [List.cons_append,
            List.nil_append,
            List.append_assoc]

theorem mem_joinPivotGaps_of_mem_gap
    (pivot : α) {gaps : List (Word α)}
    {gap : Word α} (hgap : gap ∈ gaps)
    {value : α} (hvalue : value ∈ gap) :
    value ∈ joinPivotGaps pivot gaps := by
  induction gaps with
  | nil => simp at hgap
  | cons head tail ih =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at hgap
          subst gap
          exact hvalue
      | cons next rest =>
          simp only [joinPivotGaps, List.mem_append,
            List.mem_cons]
          simp only [List.mem_cons] at hgap
          rcases hgap with rfl | hgap
          · exact Or.inl hvalue
          · exact Or.inr (Or.inr
              (ih (by simp [hgap])))

inductive PivotGapDecomposition
    (pivot : α) : Word α → List (Word α) → Prop
  | nil : PivotGapDecomposition pivot [] [[]]
  | pivot
      {word gaps}
      (tail : PivotGapDecomposition pivot word gaps) :
      PivotGapDecomposition pivot
        (pivot :: word) ([] :: gaps)
  | other
      {symbol : α} {word gap gaps}
      (hne : symbol ≠ pivot)
      (tail :
        PivotGapDecomposition pivot word (gap :: gaps)) :
      PivotGapDecomposition pivot
        (symbol :: word) ((symbol :: gap) :: gaps)

namespace PivotGapDecomposition

theorem gaps_ne_nil
    {pivot : α} {word : Word α} {gaps : List (Word α)}
    (decomposition :
      PivotGapDecomposition pivot word gaps) :
    gaps ≠ [] := by
  cases decomposition <;> simp

theorem exists_decomposition
    [DecidableEq α] (pivot : α) :
    ∀ word : Word α,
      ∃ gaps, PivotGapDecomposition pivot word gaps := by
  intro word
  induction word with
  | nil =>
      exact ⟨[[]], .nil⟩
  | cons symbol word ih =>
      obtain ⟨gaps, decomposition⟩ := ih
      by_cases heq : symbol = pivot
      · subst symbol
        exact ⟨[] :: gaps, .pivot decomposition⟩
      · cases gaps with
        | nil =>
            exact False.elim (decomposition.gaps_ne_nil rfl)
        | cons gap gaps =>
            exact ⟨(symbol :: gap) :: gaps,
              .other heq decomposition⟩

theorem join_eq
    {pivot : α} {word : Word α} {gaps : List (Word α)}
    (decomposition :
      PivotGapDecomposition pivot word gaps) :
    joinPivotGaps pivot gaps = word := by
  induction decomposition with
  | nil =>
      rfl
  | @pivot word gaps tail ih =>
      cases gaps with
      | nil =>
          exact False.elim (tail.gaps_ne_nil rfl)
      | cons gap rest =>
          simp only [joinPivotGaps, List.nil_append]
          rw [ih]
  | @other symbol word gap gaps hne tail ih =>
      cases gaps with
      | nil =>
          simp only [joinPivotGaps] at ih ⊢
          rw [ih]
      | cons next rest =>
          simp only [joinPivotGaps, List.cons_append]
          exact congrArg (fun suffix => symbol :: suffix) ih

theorem gaps_avoid
    {pivot : α} {word : Word α} {gaps : List (Word α)}
    (decomposition :
      PivotGapDecomposition pivot word gaps) :
    ∀ gap ∈ gaps, pivot ∉ gap := by
  induction decomposition with
  | nil =>
      intro target htarget
      simp at htarget
      subst target
      simp
  | @pivot word gaps tail ih =>
      intro target htarget
      simp only [List.mem_cons] at htarget
      rcases htarget with rfl | htarget
      · simp
      · exact ih target htarget
  | @other symbol word gap gaps hne tail ih =>
      intro target htarget
      simp only [List.mem_cons] at htarget
      rcases htarget with rfl | htarget
      · simp only [List.mem_cons, not_or]
        exact ⟨Ne.symm hne, ih gap (by simp)⟩
      · exact ih target (by simp [htarget])

theorem join_length_succ
    (pivot : α) :
    ∀ gaps : List (Word α), gaps ≠ [] →
      (joinPivotGaps pivot gaps).length + 1 =
        (gaps.map List.length).sum + gaps.length := by
  intro gaps hne
  cases gaps with
  | nil => exact False.elim (hne rfl)
  | cons gap rest =>
      induction rest generalizing gap with
      | nil =>
          simp [joinPivotGaps]
      | cons next rest ih =>
          simp only [joinPivotGaps, List.length_append,
            List.length_cons, List.map_cons, List.sum_cons]
          have htail := ih next (by simp)
          simp only [List.length_cons, List.map_cons,
            List.sum_cons] at htail
          omega

theorem word_length_succ
    {pivot : α} {word : Word α} {gaps : List (Word α)}
    (decomposition :
      PivotGapDecomposition pivot word gaps) :
    word.length + 1 =
      (gaps.map List.length).sum + gaps.length := by
  rw [← decomposition.join_eq]
  exact join_length_succ pivot gaps decomposition.gaps_ne_nil

end PivotGapDecomposition

end NSSE
