import NSSE.FinitePigeonholeList
import Lean.Elab.Tactic.Omega

/-!
# Finite pigeonhole with bounded multiplicity

The ordinary duplicate lemma supplies two equal entries.  Simon block
grouping needs four ordered occurrences of one prefix control.  This
file proves a multiplicity bound for lists contained in a duplicate-free
finite universe and extracts an explicit four-occurrence decomposition.
-/

namespace NSSE

universe u

theorem getElem?_append_head
    (before after : List α) (value : α) :
    (before ++ value :: after)[before.length]? = some value := by
  simp

def occurrences [DecidableEq α]
    (value : α) (values : List α) : List α :=
  values.filter fun candidate => candidate == value

@[simp] theorem mem_occurrences
    [DecidableEq α] (value candidate : α) (values : List α) :
    candidate ∈ occurrences value values ↔
      candidate ∈ values ∧ candidate = value := by
  simp [occurrences]

def withoutValue [DecidableEq α]
    (value : α) (values : List α) : List α :=
  values.filter fun candidate => candidate != value

@[simp] theorem mem_withoutValue
    [DecidableEq α] (value candidate : α) (values : List α) :
    candidate ∈ withoutValue value values ↔
      candidate ∈ values ∧ candidate ≠ value := by
  simp [withoutValue]

theorem length_occurrences_add_withoutValue
    [DecidableEq α] (value : α) (values : List α) :
    (occurrences value values).length +
      (withoutValue value values).length =
      values.length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp only [occurrences, withoutValue] at ih ⊢
      by_cases heq : head = value
      · subst head
        simp
        omega
      · simp [heq]
        omega

theorem occurrences_length_eq_count
    [DecidableEq α] (value : α) :
    ∀ values : List α,
      (occurrences value values).length =
        List.count value values := by
  intro values
  induction values with
  | nil => simp [occurrences]
  | cons head tail ih =>
      simp only [occurrences] at ih ⊢
      by_cases heq : head = value
      · subst head
        simp [ih]
      · simp [heq, ih, List.count_cons]

theorem length_le_mul_of_occurrences_le
    [DecidableEq α]
    {values ambient : List α}
    (hambient : ambient.Nodup)
    (hsubset : ∀ value ∈ values, value ∈ ambient)
    (multiplicity : Nat)
    (hcount :
      ∀ value ∈ ambient,
        (occurrences value values).length ≤ multiplicity) :
    values.length ≤ multiplicity * ambient.length := by
  induction ambient generalizing values with
  | nil =>
      have hnil : values = [] := by
        cases values with
        | nil => rfl
        | cons head tail =>
            have := hsubset head (by simp)
            simp at this
      subst values
      simp
  | cons head tail ih =>
      have htailNodup := (List.nodup_cons.mp hambient).2
      let rest := withoutValue head values
      have hrestSubset :
          ∀ value ∈ rest, value ∈ tail := by
        intro value hvalue
        have hparts :=
          (mem_withoutValue head value values).1 hvalue
        have hambientMem := hsubset value hparts.1
        simp only [List.mem_cons] at hambientMem
        rcases hambientMem with heq | htail
        · exact False.elim (hparts.2 heq)
        · exact htail
      have hrestCount :
          ∀ value ∈ tail,
            (occurrences value rest).length ≤ multiplicity := by
        intro value hvalue
        have hne : value ≠ head := by
          intro heq
          subst value
          exact (List.nodup_cons.mp hambient).1 hvalue
        have hfilter :
            (occurrences value rest).length =
              (occurrences value values).length := by
          rw [occurrences_length_eq_count,
            occurrences_length_eq_count]
          dsimp [rest, withoutValue]
          rw [List.count_filter]
          simp [hne]
        rw [hfilter]
        exact hcount value (by simp [hvalue])
      have hrestLe :=
        ih htailNodup hrestSubset hrestCount
      have hheadLe :
          (occurrences head values).length ≤ multiplicity :=
        hcount head (by simp)
      have hpartition :=
        length_occurrences_add_withoutValue head values
      change
        (occurrences head values).length + rest.length =
          values.length at hpartition
      simp only [List.length_cons]
      rw [Nat.mul_add]
      simp only [Nat.mul_one]
      omega

theorem exists_occurrences_length_gt_of_mul_lt_length
    [DecidableEq α]
    {values ambient : List α}
    (hambient : ambient.Nodup)
    (hsubset : ∀ value ∈ values, value ∈ ambient)
    (multiplicity : Nat)
    (hlong : multiplicity * ambient.length < values.length) :
    ∃ value ∈ ambient,
      multiplicity < (occurrences value values).length := by
  exact Classical.byContradiction fun hnot => by
    have hcount :
        ∀ value ∈ ambient,
          (occurrences value values).length ≤ multiplicity := by
      intro value hvalue
      have hnotValue :
          ¬ multiplicity <
            (occurrences value values).length := by
        intro hlt
        exact hnot ⟨value, hvalue, hlt⟩
      omega
    have hle :=
      length_le_mul_of_occurrences_le
        hambient hsubset multiplicity hcount
    omega

def OccursFour (value : α) (values : List α) : Prop :=
  ∃ before firstGap secondGap thirdGap after,
    values =
      before ++ value :: firstGap ++ value ::
        secondGap ++ value :: thirdGap ++ value :: after

def OccursAtLeast (value : α) : Nat → List α → Prop
  | 0, _ => True
  | count + 1, values =>
      ∃ before after,
        values = before ++ value :: after ∧
        OccursAtLeast value count after

theorem occursAtLeast_of_le_occurrences
    [DecidableEq α] (value : α) :
    ∀ count values,
      count ≤ (occurrences value values).length →
      OccursAtLeast value count values := by
  intro count
  induction count with
  | zero =>
      intro values hlength
      trivial
  | succ count ihCount =>
      intro values hlength
      induction values with
      | nil =>
          simp [occurrences] at hlength
      | cons head tail ihTail =>
          by_cases heq : head = value
          · subst head
            refine ⟨[], tail, by simp, ?_⟩
            apply ihCount tail
            have heqlength :
                (occurrences value (value :: tail)).length =
                  (occurrences value tail).length + 1 := by
              simp [occurrences]
            rw [heqlength] at hlength
            omega
          · have htailLength :
                count + 1 ≤
                  (occurrences value tail).length := by
              simpa [occurrences, heq] using hlength
            obtain ⟨before, after, htail, hrest⟩ :=
              ihTail htailLength
            exact ⟨head :: before, after, by
              simp [htail], hrest⟩

theorem exists_occursAtLeast_of_mul_lt_length
    [DecidableEq α]
    {values ambient : List α}
    (hambient : ambient.Nodup)
    (hsubset : ∀ value ∈ values, value ∈ ambient)
    (multiplicity : Nat)
    (hlong : multiplicity * ambient.length < values.length) :
    ∃ value ∈ ambient,
      OccursAtLeast value (multiplicity + 1) values := by
  obtain ⟨value, hvalue, hcount⟩ :=
    exists_occurrences_length_gt_of_mul_lt_length
      hambient hsubset multiplicity hlong
  refine ⟨value, hvalue, ?_⟩
  apply occursAtLeast_of_le_occurrences
  omega

theorem exists_occursAtLeast_of_count_mul_lt_length
    [DecidableEq α]
    {values ambient : List α}
    (hambient : ambient.Nodup)
    (hsubset : ∀ value ∈ values, value ∈ ambient)
    (count : Nat)
    (hcount : 0 < count)
    (hlong : (count - 1) * ambient.length < values.length) :
    ∃ value ∈ ambient,
      OccursAtLeast value count values := by
  obtain ⟨value, hvalue, hoccurs⟩ :=
    exists_occursAtLeast_of_mul_lt_length
      hambient hsubset (count - 1) hlong
  have hcountEq : count - 1 + 1 = count := by omega
  exact ⟨value, hvalue, hcountEq ▸ hoccurs⟩

theorem OccursAtLeast.exists_ordered_indices
    (value : α) :
    ∀ {count values},
      OccursAtLeast value count values →
      ∃ indices : List Nat,
        indices.length = count ∧
        indices.Pairwise (· < ·) ∧
        ∀ index ∈ indices, values[index]? = some value := by
  intro count
  induction count with
  | zero =>
      intro values hoccurs
      exact ⟨[], rfl, by simp, by simp⟩
  | succ count ih =>
      intro values hoccurs
      unfold OccursAtLeast at hoccurs
      obtain ⟨before, after, hvalues, hafter⟩ := hoccurs
      obtain ⟨tailIndices, hlength, hordered, hget⟩ :=
        ih hafter
      let offset := before.length + 1
      let shifted := tailIndices.map fun index => offset + index
      refine ⟨before.length :: shifted, ?_, ?_, ?_⟩
      · simp [shifted, hlength]
      · rw [List.pairwise_cons]
        constructor
        · intro index hindex
          simp only [shifted, List.mem_map] at hindex
          obtain ⟨source, hsource, rfl⟩ := hindex
          dsimp [offset]
          omega
        · dsimp [shifted]
          rw [List.pairwise_map]
          exact hordered.imp fun hlt =>
            Nat.add_lt_add_left hlt offset
      · intro index hindex
        simp only [List.mem_cons] at hindex
        rcases hindex with rfl | hshifted
        · rw [hvalues]
          exact getElem?_append_head before after value
        · simp only [shifted, List.mem_map] at hshifted
          obtain ⟨source, hsource, rfl⟩ := hshifted
          rw [hvalues]
          have hreassociate :
              before ++ value :: after =
                (before ++ [value]) ++ after := by
            simp
          rw [hreassociate]
          rw [List.getElem?_append_right]
          · have hsub :
                offset + source - (before ++ [value]).length =
                  source := by
              dsimp [offset]
              rw [List.length_append]
              simp only [List.length_singleton]
              exact Nat.add_sub_cancel_left
                (before.length + 1) source
            rw [hsub]
            exact hget source hsource
          · simp [offset]

theorem occursFour_of_occurrences_length_gt_three
    [DecidableEq α] {value : α} (values : List α)
    (hlength : 3 < (occurrences value values).length) :
    OccursFour value values := by
  have hfour : 4 ≤ (occurrences value values).length := by
    omega
  have hoccurs :=
    occursAtLeast_of_le_occurrences value 4 values hfour
  unfold OccursAtLeast at hoccurs
  obtain ⟨before, tail₁, h₁,
    gap₁, tail₂, h₂,
    gap₂, tail₃, h₃,
    gap₃, after, h₄, hzero⟩ := hoccurs
  exact ⟨before, gap₁, gap₂, gap₃, after, by
    rw [h₁, h₂, h₃, h₄]
    simp [List.append_assoc]⟩

theorem exists_four_occurrences_of_mul_lt_length
    [DecidableEq α]
    {values ambient : List α}
    (hambient : ambient.Nodup)
    (hsubset : ∀ value ∈ values, value ∈ ambient)
    (hlong : 3 * ambient.length < values.length) :
    ∃ value ∈ ambient, OccursFour value values := by
  obtain ⟨value, hvalue, hcount⟩ :=
    exists_occurrences_length_gt_of_mul_lt_length
      hambient hsubset 3 hlong
  exact ⟨value, hvalue,
    occursFour_of_occurrences_length_gt_three values hcount⟩

theorem OccursFour.exists_ordered_indices
    {value : α} {values : List α}
    (hoccurs : OccursFour value values) :
    ∃ i₀ i₁ i₂ i₃,
      i₀ < i₁ ∧ i₁ < i₂ ∧ i₂ < i₃ ∧
      i₃ < values.length ∧
      values[i₀]? = some value ∧
      values[i₁]? = some value ∧
      values[i₂]? = some value ∧
      values[i₃]? = some value := by
  obtain ⟨before, gap₁, gap₂, gap₃, after, hvalues⟩ :=
    hoccurs
  let i₀ := before.length
  let i₁ := i₀ + gap₁.length + 1
  let i₂ := i₁ + gap₂.length + 1
  let i₃ := i₂ + gap₃.length + 1
  refine ⟨i₀, i₁, i₂, i₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [i₀, i₁]
    omega
  · dsimp [i₁, i₂]
    omega
  · dsimp [i₂, i₃]
    omega
  · rw [hvalues]
    dsimp [i₀, i₁, i₂, i₃]
    simp only [List.length_append, List.length_cons]
    omega
  · rw [hvalues]
    dsimp [i₀]
    simp
  · rw [hvalues]
    have hreassociate :
        before ++ value :: gap₁ ++ value ::
            gap₂ ++ value :: gap₃ ++ value :: after =
          (before ++ value :: gap₁) ++ value ::
            gap₂ ++ value :: gap₃ ++ value :: after := by
      simp [List.append_assoc]
    rw [hreassociate]
    have hlength :
        (before ++ value :: gap₁).length = i₁ := by
      simp [i₀, i₁]
      omega
    rw [← hlength]
    simpa [List.append_assoc] using
      getElem?_append_head
        (before ++ value :: gap₁)
        (gap₂ ++ value :: gap₃ ++ value :: after) value
  · rw [hvalues]
    have hreassociate :
        before ++ value :: gap₁ ++ value ::
            gap₂ ++ value :: gap₃ ++ value :: after =
          (before ++ value :: gap₁ ++ value :: gap₂) ++
            value :: gap₃ ++ value :: after := by
      simp [List.append_assoc]
    rw [hreassociate]
    have hlength :
        (before ++ value :: gap₁ ++ value :: gap₂).length = i₂ := by
      simp [i₀, i₁, i₂]
      omega
    rw [← hlength]
    simpa [List.append_assoc] using
      getElem?_append_head
        (before ++ value :: gap₁ ++ value :: gap₂)
        (gap₃ ++ value :: after) value
  · rw [hvalues]
    have hreassociate :
        before ++ value :: gap₁ ++ value ::
            gap₂ ++ value :: gap₃ ++ value :: after =
          (before ++ value :: gap₁ ++ value ::
            gap₂ ++ value :: gap₃) ++ value :: after := by
      simp [List.append_assoc]
    rw [hreassociate]
    have hlength :
        (before ++ value :: gap₁ ++ value ::
          gap₂ ++ value :: gap₃).length = i₃ := by
      simp [i₀, i₁, i₂, i₃]
      omega
    rw [← hlength]
    exact getElem?_append_head
      (before ++ value :: gap₁ ++ value ::
        gap₂ ++ value :: gap₃) after value

end NSSE
