import NSSE.BoundedWordEnumeration
import NSSE.AutomataMembership

/-!
# Counterexample enumeration and the Pi-one presentation

For a finite alphabet and a decidable coverage predicate, all words up to a
given length form an executable finite list.  Searching these lists gives
the semidecision procedure for non-universality and the universal
quantification over bounds gives the `Pi_1` presentation in Corollary 1.4.
-/

namespace NSSE

universe u

/-- A proposition-valued `List.any`, convenient without importing Finset. -/
def ListAnyProp (P : α → Prop) : List α → Prop
  | [] => False
  | x :: xs => P x ∨ ListAnyProp P xs

theorem listAnyProp_iff
    (P : α → Prop) (xs : List α) :
    ListAnyProp P xs ↔ ∃ x, x ∈ xs ∧ P x := by
  induction xs with
  | nil => simp [ListAnyProp]
  | cons x xs ih =>
      simp [ListAnyProp, ih, or_assoc, or_left_comm]

def decideListAnyProp
    (P : α → Prop) (hP : ∀ x, Decidable (P x)) :
    (xs : List α) → Decidable (ListAnyProp P xs)
  | [] => isFalse id
  | x :: xs => by
      unfold ListAnyProp
      letI : Decidable (P x) := hP x
      letI : Decidable (ListAnyProp P xs) :=
        decideListAnyProp P hP xs
      infer_instance

/-- A counterexample occurring among words of length at most `bound`. -/
def BoundedCounterexample
    (alphabet : Enumeration α) (Covered : Word α → Prop)
    (bound : Nat) : Prop :=
  ListAnyProp (fun w => ¬ Covered w) (wordsUpTo alphabet bound)

def decideBoundedCounterexample
    (alphabet : Enumeration α) (Covered : Word α → Prop)
    (hCovered : ∀ w, Decidable (Covered w))
    (bound : Nat) :
    Decidable (BoundedCounterexample alphabet Covered bound) :=
  decideListAnyProp (fun w => ¬ Covered w)
    (fun w => by
      letI : Decidable (Covered w) := hCovered w
      infer_instance)
    (wordsUpTo alphabet bound)

theorem boundedCounterexample_iff
    (alphabet : Enumeration α) (Covered : Word α → Prop)
    (bound : Nat) :
    BoundedCounterexample alphabet Covered bound ↔
      ∃ w, w.length ≤ bound ∧ ¬ Covered w := by
  rw [BoundedCounterexample, listAnyProp_iff]
  constructor
  · rintro ⟨w, hmem, huncovered⟩
    exact ⟨w, (mem_wordsUpTo_iff alphabet bound w).1 hmem,
      huncovered⟩
  · rintro ⟨w, hlength, huncovered⟩
    exact ⟨w, (mem_wordsUpTo_iff alphabet bound w).2 hlength,
      huncovered⟩

/--
Non-universality is witnessed at some finite search bound. Together with
`decideBoundedCounterexample`, this is its explicit semidecision form.
-/
theorem exists_uncovered_iff_exists_boundedCounterexample
    (alphabet : Enumeration α) (Covered : Word α → Prop) :
    (∃ w, ¬ Covered w) ↔
      ∃ bound, BoundedCounterexample alphabet Covered bound := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w.length,
      (boundedCounterexample_iff alphabet Covered w.length).2
        ⟨w, Nat.le_refl _, hw⟩⟩
  · rintro ⟨bound, hbound⟩
    obtain ⟨w, -, hw⟩ :=
      (boundedCounterexample_iff alphabet Covered bound).1 hbound
    exact ⟨w, hw⟩

/--
Universality is a `Pi_1` statement: every finite counterexample search
returns empty.
-/
theorem universal_iff_no_boundedCounterexample
    (alphabet : Enumeration α) (Covered : Word α → Prop)
    (hCovered : ∀ w, Decidable (Covered w)) :
    (∀ w, Covered w) ↔
      ∀ bound, ¬ BoundedCounterexample alphabet Covered bound := by
  constructor
  · intro hall bound hcounter
    obtain ⟨w, -, hw⟩ :=
      (boundedCounterexample_iff alphabet Covered bound).1 hcounter
    exact hw (hall w)
  · intro hnone w
    letI : Decidable (Covered w) := hCovered w
    by_cases hw : Covered w
    · exact hw
    · exact False.elim <| hnone w.length
        ((boundedCounterexample_iff alphabet Covered w.length).2
          ⟨w, Nat.le_refl _, hw⟩)

/--
Corollary 1.4 specialized to the finite automata cap family constructed in
`AutomataMembership`: non-universality is found at some finite word-length
bound.
-/
theorem productiveCapFamily_nonuniversal_iff_exists_bound
    [DecidableEq α]
    (alphabet : Enumeration α)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    [∀ c : ProductiveCapPair α Q₁ Q₂,
      ∀ q, Decidable (c.left.automaton.accept q)]
    [∀ c : ProductiveCapPair α Q₁ Q₂,
      ∀ q, Decidable (c.right.automaton.accept q)] :
    (∃ w, ¬ ProductiveCapFamilyCovers components w) ↔
      ∃ bound,
        BoundedCounterexample alphabet
          (ProductiveCapFamilyCovers components) bound :=
  exists_uncovered_iff_exists_boundedCounterexample
    alphabet (ProductiveCapFamilyCovers components)

/--
The corresponding explicit `Pi_1` presentation of universality for the
finite automata cap family.
-/
theorem productiveCapFamily_universal_iff_no_bound
    [DecidableEq α]
    (alphabet : Enumeration α)
    (components : List (ProductiveCapPair α Q₁ Q₂))
    [∀ c : ProductiveCapPair α Q₁ Q₂,
      ∀ q, Decidable (c.left.automaton.accept q)]
    [∀ c : ProductiveCapPair α Q₁ Q₂,
      ∀ q, Decidable (c.right.automaton.accept q)] :
    (∀ w, ProductiveCapFamilyCovers components w) ↔
      ∀ bound,
        ¬ BoundedCounterexample alphabet
          (ProductiveCapFamilyCovers components) bound := by
  apply universal_iff_no_boundedCounterexample
  intro w
  exact decideProductiveCapFamilyCovers w components

end NSSE
