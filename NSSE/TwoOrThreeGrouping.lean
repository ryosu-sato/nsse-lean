import NSSE.FactorForest

/-!
# Grouping a list into consecutive pairs and a final pair or triple

For an input of length at least two, every output group has length two or
three.  Flattening the groups recovers the input exactly.  This is the
combinatorial shape used to place one complete shared-pivot zero interval
inside every block.
-/

namespace NSSE

def groupTwoOrThree : List α → List (List α)
  | [] => []
  | [first] => [[first]]
  | [first, second] => [[first, second]]
  | [first, second, third] =>
      [[first, second, third]]
  | first :: second :: third :: fourth :: rest =>
      [first, second] ::
        groupTwoOrThree (third :: fourth :: rest)
termination_by values => values.length

@[simp] theorem groupTwoOrThree_nil :
    groupTwoOrThree ([] : List α) = [] :=
  by simp [groupTwoOrThree]

@[simp] theorem groupTwoOrThree_singleton
    (first : α) :
    groupTwoOrThree [first] = [[first]] :=
  by simp [groupTwoOrThree]

@[simp] theorem groupTwoOrThree_pair
    (first second : α) :
    groupTwoOrThree [first, second] =
      [[first, second]] :=
  by simp [groupTwoOrThree]

@[simp] theorem groupTwoOrThree_triple
    (first second third : α) :
    groupTwoOrThree [first, second, third] =
      [[first, second, third]] :=
  by simp [groupTwoOrThree]

theorem flatten_groupTwoOrThree :
    ∀ values : List α,
      (groupTwoOrThree values).flatten = values := by
  intro values
  fun_induction groupTwoOrThree values with
  | case1 =>
      simp
  | case2 first =>
      simp
  | case3 first second =>
      simp
  | case4 first second third =>
      simp
  | case5 first second third fourth rest ih =>
      simp only [groupTwoOrThree,
        List.flatten_cons, ih]
      rfl

theorem flatten_map_flatten
    (groups : List (List (List α))) :
    (groups.map List.flatten).flatten =
      groups.flatten.flatten := by
  induction groups with
  | nil =>
      rfl
  | cons group rest ih =>
      simp only [List.map_cons,
        List.flatten_cons, ih]
      exact List.flatten_append.symm

theorem flatten_groupedWords
    (blocks : List (List α)) :
    ((groupTwoOrThree blocks).map
      List.flatten).flatten =
        blocks.flatten := by
  rw [flatten_map_flatten,
    flatten_groupTwoOrThree]

theorem groupTwoOrThree_ne_nil
    (values : List α) (hvalues : values ≠ []) :
    groupTwoOrThree values ≠ [] := by
  cases values with
  | nil =>
      exact False.elim (hvalues rfl)
  | cons first rest =>
      cases rest with
      | nil =>
          simp
      | cons second rest =>
          cases rest with
          | nil =>
              simp
          | cons third rest =>
              cases rest with
              | nil =>
                  simp
              | cons fourth rest =>
                  simp [groupTwoOrThree]

theorem mem_groupTwoOrThree_length
    (values : List α)
    (hvalues : 2 ≤ values.length) :
    ∀ group ∈ groupTwoOrThree values,
      group.length = 2 ∨ group.length = 3 := by
  intro group hgroup
  fun_induction groupTwoOrThree values with
  | case1 =>
      simp at hvalues
  | case2 first =>
      simp at hvalues
  | case3 first second =>
      simp at hgroup
      subst group
      simp
  | case4 first second third =>
      simp at hgroup
      subst group
      simp
  | case5 first second third fourth rest ih =>
      simp only [groupTwoOrThree,
        List.mem_cons] at hgroup
      rcases hgroup with rfl | htail
      · simp
      · apply ih
        · simp
        · exact htail

theorem mem_groupTwoOrThree_nonempty
    (values : List α)
    (hvalues : 2 ≤ values.length)
    {group : List α}
    (hgroup : group ∈ groupTwoOrThree values) :
    group ≠ [] := by
  have hlength :=
    mem_groupTwoOrThree_length
      values hvalues group hgroup
  rcases hlength with htwo | hthree
  · intro hempty
    subst group
    simp at htwo
  · intro hempty
    subst group
    simp at hthree

theorem mem_groupTwoOrThree_pair_or_triple
    (values : List α)
    (hvalues : 2 ≤ values.length)
    {group : List α}
    (hgroup : group ∈ groupTwoOrThree values) :
    (∃ first second,
        group = [first, second]) ∨
      ∃ first second third,
        group = [first, second, third] := by
  have hlength :=
    mem_groupTwoOrThree_length
      values hvalues group hgroup
  cases group with
  | nil =>
      simp at hlength
  | cons first rest =>
      cases rest with
      | nil =>
          simp at hlength
      | cons second rest =>
          cases rest with
          | nil =>
              exact Or.inl
                ⟨first, second, rfl⟩
          | cons third rest =>
              cases rest with
              | nil =>
                  exact Or.inr
                    ⟨first, second, third, rfl⟩
              | cons fourth rest =>
                  simp at hlength

theorem mem_of_mem_groupTwoOrThree
    {values : List α} {group : List α}
    (hgroup : group ∈ groupTwoOrThree values)
    {value : α} (hvalue : value ∈ group) :
    value ∈ values := by
  have hflatten :
      value ∈ (groupTwoOrThree values).flatten := by
    exact List.mem_flatten.mpr
      ⟨group, hgroup, hvalue⟩
  rw [flatten_groupTwoOrThree] at hflatten
  exact hflatten

end NSSE
