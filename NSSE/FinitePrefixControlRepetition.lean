import NSSE.FinitePigeonholeList

/-!
# Repetition among finite prefix controls

The transition value of every prefix belongs to the finite transformation
enumeration.  Once a word is at least as long as that enumeration, its
`length + 1` prefix controls contain two equal entries.
-/

namespace NSSE

universe u v

def DFA.prefixTransitionValues
    (A : DFA α Q) (word : Word α) : List (Q → Q) :=
  (List.range (word.length + 1)).map fun length =>
    A.transitionEval (word.take length)

@[simp] theorem DFA.prefixTransitionValues_length
    (A : DFA α Q) (word : Word α) :
    (A.prefixTransitionValues word).length = word.length + 1 := by
  simp [DFA.prefixTransitionValues]

theorem DFA.prefixTransitionValues_mem_enumeration
    [DecidableEq Q]
    (A : DFA α Q) (states : Enumeration Q)
    (word : Word α) :
    ∀ value ∈ A.prefixTransitionValues word,
      value ∈ (A.transformationEnumeration states).values := by
  intro value hvalue
  exact (A.transformationEnumeration states).complete value

def RepeatedPrefixTransition
    (A : DFA α Q) (word : Word α) : Prop :=
  ∃ before middle after value,
    A.prefixTransitionValues word =
      before ++ value :: middle ++ value :: after

theorem DFA.exists_repeatedPrefixTransition
    [DecidableEq Q]
    (A : DFA α Q) (states : Enumeration Q)
    (word : Word α)
    (hlong :
      (A.transformationEnumeration states).values.length ≤ word.length) :
    RepeatedPrefixTransition A word := by
  letI : DecidableEq (Q → Q) :=
    decidableEqFunctionOfEnumeration states
  obtain ⟨before, middle, after, value, hdecomposition⟩ :=
    List.exists_repeated_decomposition_of_subset_of_length_lt
      (A.prefixTransitionValues_mem_enumeration states word)
      (by
        rw [A.prefixTransitionValues_length]
        omega)
  exact ⟨before, middle, after, value, hdecomposition⟩

end NSSE
