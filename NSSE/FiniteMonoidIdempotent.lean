import NSSE.FiniteMonoidPowers

/-!
# A positive idempotent power in every enumerated finite monoid

The first `N + 1` powers lie in an enumeration of length `N`, hence two
powers repeat.  Their positive period yields a positive exponent whose
power is idempotent.
-/

namespace NSSE

universe u

namespace ControlMonoid

def powerValues
    (C : ControlMonoid M) (x : M) (count : Nat) : List M :=
  (List.range count).map (C.power x)

@[simp] theorem powerValues_length
    (C : ControlMonoid M) (x : M) (count : Nat) :
    (C.powerValues x count).length = count := by
  simp [powerValues]

theorem powerValues_getElem?_of_lt
    (C : ControlMonoid M) (x : M)
    {count index : Nat} (hlt : index < count) :
    (C.powerValues x count)[index]? =
      some (C.power x index) := by
  simp [powerValues, hlt]

theorem getElem?_at_append_head
    (before after : List α) (value : α) :
    (before ++ value :: after)[before.length]? = some value := by
  simp

theorem exists_repeated_power
    [DecidableEq M]
    (C : ControlMonoid M)
    (elements : Enumeration M)
    (x : M) :
    ∃ i j,
      i < j ∧
      j ≤ elements.values.length ∧
      C.power x i = C.power x j := by
  let count := elements.values.length + 1
  have hsubset :
      ∀ value ∈ C.powerValues x count,
        value ∈ elements.values := by
    intro value hvalue
    exact elements.complete value
  obtain ⟨before, middle, after, value, hdecomposition⟩ :=
    List.exists_repeated_decomposition_of_subset_of_length_lt
      hsubset (by simp [count])
  let i := before.length
  let j := before.length + middle.length + 1
  have hlength := congrArg List.length hdecomposition
  simp only [C.powerValues_length, List.length_append,
    List.length_cons] at hlength
  have hiCount : i < count := by
    dsimp [i, count]
    omega
  have hjCount : j < count := by
    dsimp [j, count]
    omega
  have hiValue :
      C.power x i = value := by
    have hget := congrArg (fun values => values[i]?) hdecomposition
    change
      (C.powerValues x count)[i]? =
        (before ++ value :: middle ++ value :: after)[i]?
      at hget
    rw [C.powerValues_getElem?_of_lt x hiCount] at hget
    have hright :
        (before ++ value :: middle ++ value :: after)[i]? =
          some value := by
      dsimp [i]
      simp [List.append_assoc]
    rw [hright] at hget
    exact Option.some.inj hget
  have hjValue :
      C.power x j = value := by
    have hget := congrArg (fun values => values[j]?) hdecomposition
    change
      (C.powerValues x count)[j]? =
        (before ++ value :: middle ++ value :: after)[j]?
      at hget
    rw [C.powerValues_getElem?_of_lt x hjCount] at hget
    have hright :
        (before ++ value :: middle ++ value :: after)[j]? =
          some value := by
      have hreassociate :
          before ++ value :: middle ++ value :: after =
            (before ++ value :: middle) ++ value :: after := by
        simp [List.append_assoc]
      rw [hreassociate]
      have hprefix :
          (before ++ value :: middle).length = j := by
        simp [j]
        omega
      rw [← hprefix]
      exact getElem?_at_append_head
        (before ++ value :: middle) after value
    rw [hright] at hget
    exact Option.some.inj hget
  exact ⟨i, j, by
    dsimp [i, j]
    omega, by
    dsimp [j, count] at hjCount ⊢
    omega, hiValue.trans hjValue.symm⟩

theorem exists_positive_idempotent_power
    [DecidableEq M]
    (C : ControlMonoid M)
    (elements : Enumeration M)
    (x : M) :
    ∃ exponent,
      0 < exponent ∧
      C.Idempotent (C.power x exponent) := by
  obtain ⟨i, j, hij, hjBound, hpower⟩ :=
    C.exists_repeated_power elements x
  by_cases hi : i = 0
  · subst i
    refine ⟨j, hij, ?_⟩
    have hjOne : C.power x j = C.one := by
      rw [← hpower]
      rfl
    rw [hjOne]
    exact C.one_is_idempotent
  · let period := j - i
    have hperiodPositive : 0 < period := by
      dsimp [period]
      omega
    have hj : j = i + period := by
      dsimp [period]
      omega
    have hperiod :
        C.power x i = C.power x (i + period) := by
      rwa [← hj]
    let exponent := i * period
    have hiPositive : 0 < i := Nat.pos_of_ne_zero hi
    have hle : i ≤ exponent := by
      dsimp [exponent]
      have hone : 1 ≤ period := hperiodPositive
      have hmul := Nat.mul_le_mul_left i hone
      simpa using hmul
    refine ⟨exponent, ?_, ?_⟩
    · dsimp [exponent]
      exact Nat.mul_pos hiPositive hperiodPositive
    · exact C.idempotent_power_of_period_multiple x
        hperiod hle rfl

end ControlMonoid

theorem DFA.exists_positive_idempotent_word_power
    [DecidableEq Q]
    (A : DFA α Q) (states : Enumeration Q)
    (word : Word α) :
    ∃ exponent,
      0 < exponent ∧
      (transformationMonoid Q).Idempotent
        (A.transitionEval (Word.power word exponent)) := by
  letI : DecidableEq (Q → Q) :=
    decidableEqFunctionOfEnumeration states
  obtain ⟨exponent, hpositive, hidempotent⟩ :=
    (transformationMonoid Q).exists_positive_idempotent_power
      (A.transformationEnumeration states)
      (A.transitionEval word)
  refine ⟨exponent, hpositive, ?_⟩
  change
    (transformationMonoid Q).Idempotent
      ((transformationMonoid Q).eval A.letterTransform
        (Word.power word exponent))
  rw [(transformationMonoid Q).eval_word_power]
  exact hidempotent

end NSSE
