import NSSE.ParameterizedIntervalAgreement

/-!
# Adjacent phase regions

An ordered list of event boundaries partitions the interval between its
first and last elements into adjacent regions. This is the combinatorial
coverage fact used after fixing an order type in Lemma A.1.
-/

namespace NSSE

def adjacentPairs : List β → List (β × β)
  | first :: second :: rest =>
      (first, second) :: adjacentPairs (second :: rest)
  | _ => []

theorem adjacentPairs_map
    (transform : β → γ) (values : List β) :
    adjacentPairs (values.map transform) =
      (adjacentPairs values).map fun pair =>
        (transform pair.1, transform pair.2) := by
  cases values with
  | nil => rfl
  | cons first rest =>
      induction rest generalizing first with
      | nil => rfl
      | cons second rest ih =>
          simp only [List.map_cons, adjacentPairs,
            List.cons.injEq, true_and]
          exact ih second

theorem adjacentPairs_mem_of_pairwise
    (first second : Nat) (rest : List Nat)
    (hsorted : (first :: second :: rest).Pairwise (· ≤ ·))
    (position : Nat)
    (hlower : first ≤ position)
    (hupper :
      position ≤ (second :: rest).getLast (by simp)) :
    ∃ left right,
      (left, right) ∈
        adjacentPairs (first :: second :: rest) ∧
      left ≤ position ∧ position ≤ right := by
  induction rest generalizing first second with
  | nil =>
      refine ⟨first, second, by simp [adjacentPairs],
        hlower, ?_⟩
      simpa using hupper
  | cons third rest ih =>
      by_cases hfirstRegion : position ≤ second
      · exact ⟨first, second,
          by simp [adjacentPairs], hlower, hfirstRegion⟩
      · have htailSorted :
            (second :: third :: rest).Pairwise (· ≤ ·) :=
          hsorted.tail
        have hsecondLower : second ≤ position := by omega
        have htailUpper :
            position ≤ (third :: rest).getLast (by simp) := by
          simpa using hupper
        obtain ⟨left, right, hpair, hleft, hright⟩ :=
          ih second third htailSorted
            hsecondLower htailUpper
        exact ⟨left, right,
          by
            simp only [adjacentPairs, List.mem_cons]
            right
            simpa only [adjacentPairs, List.mem_cons] using hpair,
          hleft, hright⟩

def AdjacentCover
    (boundaries : List Nat)
    (lower upper : Nat) : Prop :=
  ∀ position,
    lower ≤ position → position ≤ upper →
    ∃ left right,
      (left, right) ∈ adjacentPairs boundaries ∧
      left ≤ position ∧ position ≤ right

theorem pairwise_adjacentCover
    (first second : Nat) (rest : List Nat)
    (hsorted : (first :: second :: rest).Pairwise (· ≤ ·)) :
    AdjacentCover (first :: second :: rest)
      first ((second :: rest).getLast (by simp)) := by
  intro position hlower hupper
  exact adjacentPairs_mem_of_pairwise
    first second rest hsorted position hlower hupper

def AdjacentContained
    (boundaries : List Nat)
    (lower upper : Nat) : Prop :=
  ∀ left right,
    (left, right) ∈ adjacentPairs boundaries →
    lower ≤ left ∧ right ≤ upper

theorem interval_predicate_iff_adjacent
    (predicate : Nat → Prop)
    (boundaries : List Nat)
    (lower upper : Nat)
    (hcover :
      AdjacentCover boundaries lower upper)
    (hcontained :
      AdjacentContained boundaries lower upper) :
    (∀ position, lower ≤ position →
        position ≤ upper → predicate position) ↔
      ∀ left right,
        (left, right) ∈ adjacentPairs boundaries →
        ∀ position, left ≤ position →
          position ≤ right → predicate position := by
  constructor
  · intro hglobal left right hpair position hleft hright
    obtain ⟨hlower, hupper⟩ :=
      hcontained left right hpair
    exact hglobal position
      (Nat.le_trans hlower hleft)
      (Nat.le_trans hright hupper)
  · intro hadjacent position hlower hupper
    obtain ⟨left, right, hpair, hleft, hright⟩ :=
      hcover position hlower hupper
    exact hadjacent left right hpair
      position hleft hright

end NSSE
