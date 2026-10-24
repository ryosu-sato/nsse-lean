import NSSE.ControlStabilizer
import NSSE.FiniteMultiplicityPigeonhole
import Lean.Elab.Tactic.Omega

/-!
# Repeated prefix controls as stabilizer loops

For a word at least as long as a complete finite control enumeration,
two of its prefix controls coincide.  This file extracts the two cut
indices, the nonempty middle factor between them, and the proof that the
middle factor evaluates in the corresponding right stabilizer.
-/

namespace NSSE

universe u v

namespace ControlMonoid

variable {M : Type v} {α : Type u}

def prefixControlValues
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) : List M :=
  (List.range (word.length + 1)).map fun length =>
    C.eval letter (word.take length)

@[simp] theorem prefixControlValues_length
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) :
    (C.prefixControlValues letter word).length =
      word.length + 1 := by
  simp [prefixControlValues]

theorem prefixControlValues_getElem?_of_le
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) {index : Nat}
    (hle : index ≤ word.length) :
    (C.prefixControlValues letter word)[index]? =
      some (C.eval letter (word.take index)) := by
  have hlt : index < word.length + 1 := by omega
  simp [prefixControlValues, hlt]

theorem getElem?_append_head
    (before after : List α) (value : α) :
    (before ++ value :: after)[before.length]? = some value := by
  simp

theorem exists_repeated_prefix_control
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hlong : elements.values.length ≤ word.length) :
    ∃ i j,
      i < j ∧
      j ≤ word.length ∧
      C.eval letter (word.take i) =
        C.eval letter (word.take j) := by
  have hsubset :
      ∀ value ∈ C.prefixControlValues letter word,
        value ∈ elements.values := by
    intro value hvalue
    exact elements.complete value
  obtain ⟨before, middle, after, value, hdecomposition⟩ :=
    List.exists_repeated_decomposition_of_subset_of_length_lt
      hsubset (by
        rw [C.prefixControlValues_length]
        omega)
  let i := before.length
  let j := before.length + middle.length + 1
  have hlength := congrArg List.length hdecomposition
  simp only [C.prefixControlValues_length, List.length_append,
    List.length_cons] at hlength
  have hi : i ≤ word.length := by
    dsimp [i]
    omega
  have hj : j ≤ word.length := by
    dsimp [j]
    omega
  have hiValue :
      C.eval letter (word.take i) = value := by
    have hget := congrArg (fun values => values[i]?) hdecomposition
    change
      (C.prefixControlValues letter word)[i]? =
        (before ++ value :: middle ++ value :: after)[i]?
      at hget
    rw [C.prefixControlValues_getElem?_of_le letter word hi] at hget
    have hright :
        (before ++ value :: middle ++ value :: after)[i]? =
          some value := by
      dsimp [i]
      simp [List.append_assoc]
    rw [hright] at hget
    exact Option.some.inj hget
  have hjValue :
      C.eval letter (word.take j) = value := by
    have hget := congrArg (fun values => values[j]?) hdecomposition
    change
      (C.prefixControlValues letter word)[j]? =
        (before ++ value :: middle ++ value :: after)[j]?
      at hget
    rw [C.prefixControlValues_getElem?_of_le letter word hj] at hget
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
      exact getElem?_append_head
        (before ++ value :: middle) after value
    rw [hright] at hget
    exact Option.some.inj hget
  exact ⟨i, j, by
    dsimp [i, j]
    omega, hj, hiValue.trans hjValue.symm⟩

def middleFactor
    (word : Word α) (i j : Nat) : Word α :=
  (word.drop i).take (j - i)

theorem take_append_middleFactor
    (word : Word α) {i j : Nat} (hij : i ≤ j) :
    word.take i ++ middleFactor word i j = word.take j := by
  unfold middleFactor
  rw [← List.take_add]
  congr 1
  omega

theorem middleFactor_length
    (word : Word α) {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ word.length) :
    (middleFactor word i j).length = j - i := by
  unfold middleFactor
  simp only [List.length_take, List.length_drop]
  apply Nat.min_eq_left
  omega

theorem middleFactor_ne_nil
    (word : Word α) {i j : Nat}
    (hij : i < j) (hj : j ≤ word.length) :
    middleFactor word i j ≠ [] := by
  intro hempty
  have hlength :=
    middleFactor_length word (Nat.le_of_lt hij) hj
  rw [hempty] at hlength
  simp at hlength
  omega

theorem take_middleFactor_drop
    (word : Word α) {i j : Nat}
    (hij : i ≤ j) :
    word.take i ++ middleFactor word i j ++ word.drop j = word := by
  rw [take_append_middleFactor word hij]
  exact List.take_append_drop j word

structure PrefixControlLoop
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) where
  i : Nat
  j : Nat
  lt : i < j
  j_le : j ≤ word.length
  equal_control :
    C.eval letter (word.take i) =
      C.eval letter (word.take j)

variable {C : ControlMonoid M}
variable {letter : α → M} {word : Word α}

def PrefixControlLoop.anchor
    (loop : PrefixControlLoop C letter word) : M :=
  C.eval letter (word.take loop.i)

def PrefixControlLoop.middle
    (loop : PrefixControlLoop C letter word) : Word α :=
  middleFactor word loop.i loop.j

theorem PrefixControlLoop.middle_ne_nil
  (loop : PrefixControlLoop C letter word) :
    loop.middle ≠ [] :=
  by
    simpa [PrefixControlLoop.middle] using
      middleFactor_ne_nil word loop.lt loop.j_le

theorem PrefixControlLoop.word_eq
    (loop : PrefixControlLoop C letter word) :
    word.take loop.i ++ loop.middle ++ word.drop loop.j = word :=
  by
    simpa [PrefixControlLoop.middle] using
      take_middleFactor_drop word (Nat.le_of_lt loop.lt)

theorem PrefixControlLoop.middle_mem_rightStabilizer
    (loop : PrefixControlLoop C letter word) :
    (C.rightStabilizer loop.anchor).carrier
      (C.eval letter loop.middle) := by
  apply C.eval_mem_rightStabilizer_of_prefix_eq
    letter loop.anchor (word.take loop.i) loop.middle
  · unfold PrefixControlLoop.anchor
    rfl
  · change
      C.eval letter
          (word.take loop.i ++
            middleFactor word loop.i loop.j) =
        loop.anchor
    rw [take_append_middleFactor word
      (Nat.le_of_lt loop.lt)]
    exact loop.equal_control.symm

def PrefixControlLoop.middleControl
    (loop : PrefixControlLoop C letter word) :
    {value : M //
      (C.rightStabilizer loop.anchor).carrier value} :=
  ⟨C.eval letter loop.middle,
    loop.middle_mem_rightStabilizer⟩

@[simp] theorem PrefixControlLoop.middleControl_val
    (loop : PrefixControlLoop C letter word) :
    loop.middleControl.1 = C.eval letter loop.middle :=
  rfl

theorem exists_prefixControlLoop
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hlong : elements.values.length ≤ word.length) :
    Nonempty (PrefixControlLoop C letter word) := by
  obtain ⟨i, j, hij, hj, heq⟩ :=
    C.exists_repeated_prefix_control
      elements letter word hlong
  exact ⟨⟨i, j, hij, hj, heq⟩⟩

theorem exists_prefixControlLoop_of_normalized_length
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hlong :
      elements.normalized.values.length ≤ word.length) :
    Nonempty (PrefixControlLoop C letter word) :=
  C.exists_prefixControlLoop elements.normalized
    letter word hlong

theorem exists_prefixControlLoop_stabilizer_dichotomy
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hlong :
      elements.normalized.values.length ≤ word.length) :
    ∃ loop : PrefixControlLoop C letter word,
      (C.rightStabilizer loop.anchor).Proper ∨
        (C.Idempotent loop.anchor ∧
          ∀ value : M, C.mul loop.anchor value = loop.anchor) := by
  classical
  obtain ⟨loop⟩ :=
    C.exists_prefixControlLoop_of_normalized_length
      elements letter word hlong
  refine ⟨loop, ?_⟩
  by_cases hproper :
      (C.rightStabilizer loop.anchor).Proper
  · exact Or.inl hproper
  · exact Or.inr
      ⟨C.idempotent_of_not_rightStabilizer_proper
          loop.anchor hproper,
        C.right_absorbing_of_not_stabilizer_proper
          loop.anchor hproper⟩

theorem exists_many_equal_prefix_controls
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (count : Nat) (hcount : 0 < count)
    (hlong :
      (count - 1) * elements.normalized.values.length <
        word.length + 1) :
    ∃ anchor : M, ∃ indices : List Nat,
      indices.length = count ∧
      indices.Pairwise (· < ·) ∧
      (∀ index ∈ indices, index ≤ word.length) ∧
      ∀ index ∈ indices,
        C.eval letter (word.take index) = anchor := by
  let values := C.prefixControlValues letter word
  let ambient := elements.normalized.values
  have hsubset :
      ∀ value ∈ values, value ∈ ambient := by
    intro value hvalue
    exact elements.normalized.complete value
  have hvaluesLong :
      (count - 1) * ambient.length < values.length := by
    simpa [values, ambient] using hlong
  obtain ⟨anchor, hanchor, hoccurs⟩ :=
    exists_occursAtLeast_of_count_mul_lt_length
      elements.normalized_nodup hsubset count hcount
      hvaluesLong
  obtain ⟨indices, hlength, hordered, hget⟩ :=
    hoccurs.exists_ordered_indices anchor
  refine ⟨anchor, indices, hlength, hordered, ?_, ?_⟩
  · intro index hindex
    have hsome := hget index hindex
    have hlt := (List.getElem?_eq_some_iff.mp hsome).1
    dsimp [values] at hlt
    rw [C.prefixControlValues_length] at hlt
    omega
  · intro index hindex
    have hle : index ≤ word.length := by
      have hsome := hget index hindex
      have hlt := (List.getElem?_eq_some_iff.mp hsome).1
      dsimp [values] at hlt
      rw [C.prefixControlValues_length] at hlt
      omega
    have hprefix :=
      C.prefixControlValues_getElem?_of_le
        letter word hle
    have hanchorAt := hget index hindex
    dsimp [values] at hanchorAt
    rw [hprefix] at hanchorAt
    exact Option.some.inj hanchorAt

structure FourPrefixControlCuts
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) where
  i₀ : Nat
  i₁ : Nat
  i₂ : Nat
  i₃ : Nat
  lt₀₁ : i₀ < i₁
  lt₁₂ : i₁ < i₂
  lt₂₃ : i₂ < i₃
  i₃_le : i₃ ≤ word.length
  equal₀₁ :
    C.eval letter (word.take i₀) =
      C.eval letter (word.take i₁)
  equal₀₂ :
    C.eval letter (word.take i₀) =
      C.eval letter (word.take i₂)
  equal₀₃ :
    C.eval letter (word.take i₀) =
      C.eval letter (word.take i₃)

namespace FourPrefixControlCuts

def anchor
    (cuts : FourPrefixControlCuts C letter word) : M :=
  C.eval letter (word.take cuts.i₀)

def block₀₁
    (cuts : FourPrefixControlCuts C letter word) : Word α :=
  middleFactor word cuts.i₀ cuts.i₁

def block₁₂
    (cuts : FourPrefixControlCuts C letter word) : Word α :=
  middleFactor word cuts.i₁ cuts.i₂

def block₂₃
    (cuts : FourPrefixControlCuts C letter word) : Word α :=
  middleFactor word cuts.i₂ cuts.i₃

theorem block₀₁_ne_nil
    (cuts : FourPrefixControlCuts C letter word) :
    cuts.block₀₁ ≠ [] :=
  middleFactor_ne_nil word cuts.lt₀₁
    (Nat.le_trans (Nat.le_of_lt cuts.lt₁₂)
      (Nat.le_trans (Nat.le_of_lt cuts.lt₂₃) cuts.i₃_le))

theorem block₁₂_ne_nil
    (cuts : FourPrefixControlCuts C letter word) :
    cuts.block₁₂ ≠ [] :=
  middleFactor_ne_nil word cuts.lt₁₂
    (Nat.le_trans (Nat.le_of_lt cuts.lt₂₃) cuts.i₃_le)

theorem block₂₃_ne_nil
    (cuts : FourPrefixControlCuts C letter word) :
    cuts.block₂₃ ≠ [] :=
  middleFactor_ne_nil word cuts.lt₂₃ cuts.i₃_le

theorem block₀₁_mem_rightStabilizer
    (cuts : FourPrefixControlCuts C letter word) :
    (C.rightStabilizer cuts.anchor).carrier
      (C.eval letter cuts.block₀₁) := by
  apply C.eval_mem_rightStabilizer_of_prefix_eq
    letter cuts.anchor (word.take cuts.i₀) cuts.block₀₁
  · rfl
  · unfold block₀₁ anchor
    rw [take_append_middleFactor word
      (Nat.le_of_lt cuts.lt₀₁)]
    exact cuts.equal₀₁.symm

theorem block₁₂_mem_rightStabilizer
    (cuts : FourPrefixControlCuts C letter word) :
    (C.rightStabilizer cuts.anchor).carrier
      (C.eval letter cuts.block₁₂) := by
  apply C.eval_mem_rightStabilizer_of_prefix_eq
    letter cuts.anchor (word.take cuts.i₁) cuts.block₁₂
  · exact cuts.equal₀₁.symm
  · unfold block₁₂ anchor
    rw [take_append_middleFactor word
      (Nat.le_of_lt cuts.lt₁₂)]
    exact cuts.equal₀₂.symm

theorem block₂₃_mem_rightStabilizer
    (cuts : FourPrefixControlCuts C letter word) :
    (C.rightStabilizer cuts.anchor).carrier
      (C.eval letter cuts.block₂₃) := by
  apply C.eval_mem_rightStabilizer_of_prefix_eq
    letter cuts.anchor (word.take cuts.i₂) cuts.block₂₃
  · exact cuts.equal₀₂.symm
  · unfold block₂₃ anchor
    rw [take_append_middleFactor word
      (Nat.le_of_lt cuts.lt₂₃)]
    exact cuts.equal₀₃.symm

theorem later_prefix_control_eq_anchor
    (cuts : FourPrefixControlCuts C letter word)
    (habsorbing :
      ∀ value : M, C.mul cuts.anchor value = cuts.anchor)
    {later : Nat} (hlater : cuts.i₀ ≤ later) :
    C.eval letter (word.take later) = cuts.anchor := by
  apply C.eval_take_eq_of_right_absorbing
    letter cuts.anchor habsorbing word hlater
  rfl

theorem three_block_word_eq
    (cuts : FourPrefixControlCuts C letter word) :
    word.take cuts.i₀ ++ cuts.block₀₁ ++ cuts.block₁₂ ++
        cuts.block₂₃ ++ word.drop cuts.i₃ =
      word := by
  unfold block₀₁ block₁₂ block₂₃
  calc
    word.take cuts.i₀ ++ middleFactor word cuts.i₀ cuts.i₁ ++
          middleFactor word cuts.i₁ cuts.i₂ ++
          middleFactor word cuts.i₂ cuts.i₃ ++ word.drop cuts.i₃ =
        (word.take cuts.i₀ ++
            middleFactor word cuts.i₀ cuts.i₁) ++
          middleFactor word cuts.i₁ cuts.i₂ ++
          middleFactor word cuts.i₂ cuts.i₃ ++ word.drop cuts.i₃ := by
            simp [List.append_assoc]
    _ =
        (word.take cuts.i₁ ++
            middleFactor word cuts.i₁ cuts.i₂) ++
          middleFactor word cuts.i₂ cuts.i₃ ++ word.drop cuts.i₃ := by
            rw [take_append_middleFactor word
              (Nat.le_of_lt cuts.lt₀₁)]
    _ =
        (word.take cuts.i₂ ++
            middleFactor word cuts.i₂ cuts.i₃) ++
          word.drop cuts.i₃ := by
            rw [take_append_middleFactor word
              (Nat.le_of_lt cuts.lt₁₂)]
    _ = word.take cuts.i₃ ++ word.drop cuts.i₃ := by
          rw [take_append_middleFactor word
            (Nat.le_of_lt cuts.lt₂₃)]
    _ = word := List.take_append_drop cuts.i₃ word

theorem block₀₁_length_lt
    (cuts : FourPrefixControlCuts C letter word) :
    cuts.block₀₁.length < word.length := by
  have hlength := congrArg List.length cuts.three_block_word_eq
  simp only [List.length_append] at hlength
  have h₁ : 0 < cuts.block₁₂.length :=
    List.length_pos_iff.mpr cuts.block₁₂_ne_nil
  have h₂ : 0 < cuts.block₂₃.length :=
    List.length_pos_iff.mpr cuts.block₂₃_ne_nil
  omega

theorem block₁₂_length_lt
    (cuts : FourPrefixControlCuts C letter word) :
    cuts.block₁₂.length < word.length := by
  have hlength := congrArg List.length cuts.three_block_word_eq
  simp only [List.length_append] at hlength
  have h₀ : 0 < cuts.block₀₁.length :=
    List.length_pos_iff.mpr cuts.block₀₁_ne_nil
  have h₂ : 0 < cuts.block₂₃.length :=
    List.length_pos_iff.mpr cuts.block₂₃_ne_nil
  omega

theorem block₂₃_length_lt
    (cuts : FourPrefixControlCuts C letter word) :
    cuts.block₂₃.length < word.length := by
  have hlength := congrArg List.length cuts.three_block_word_eq
  simp only [List.length_append] at hlength
  have h₀ : 0 < cuts.block₀₁.length :=
    List.length_pos_iff.mpr cuts.block₀₁_ne_nil
  have h₁ : 0 < cuts.block₁₂.length :=
    List.length_pos_iff.mpr cuts.block₁₂_ne_nil
  omega

theorem before_length_lt
    (cuts : FourPrefixControlCuts C letter word) :
    (word.take cuts.i₀).length < word.length := by
  have hi₀lt : cuts.i₀ < word.length := by
    exact Nat.lt_of_lt_of_le
      (Nat.lt_trans cuts.lt₀₁
        (Nat.lt_trans cuts.lt₁₂ cuts.lt₂₃))
      cuts.i₃_le
  simp [List.length_take, Nat.min_eq_left
    (Nat.le_of_lt hi₀lt), hi₀lt]

theorem after_length_lt
    (cuts : FourPrefixControlCuts C letter word) :
    (word.drop cuts.i₃).length < word.length := by
  have hi₃positive : 0 < cuts.i₃ := by
    exact Nat.lt_of_le_of_lt (Nat.zero_le cuts.i₀)
      (Nat.lt_trans cuts.lt₀₁
        (Nat.lt_trans cuts.lt₁₂ cuts.lt₂₃))
  have hwordPositive : 0 < word.length :=
    Nat.lt_of_lt_of_le hi₃positive cuts.i₃_le
  simp only [List.length_drop]
  exact Nat.sub_lt hwordPositive hi₃positive

end FourPrefixControlCuts

theorem exists_fourPrefixControlCuts
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (letter : α → M) (word : Word α)
    (hlong :
      3 * elements.normalized.values.length <
        word.length + 1) :
    Nonempty (FourPrefixControlCuts C letter word) := by
  let ambient := elements.normalized.values
  let values := C.prefixControlValues letter word
  have hsubset :
      ∀ value ∈ values, value ∈ ambient := by
    intro value hvalue
    exact elements.normalized.complete value
  have hvaluesLong :
      3 * ambient.length < values.length := by
    simpa [ambient, values] using hlong
  obtain ⟨value, hvalue, hfour⟩ :=
    exists_four_occurrences_of_mul_lt_length
      elements.normalized_nodup hsubset hvaluesLong
  obtain ⟨i₀, i₁, i₂, i₃,
    h₀₁, h₁₂, h₂₃, hi₃, hget₀, hget₁, hget₂, hget₃⟩ :=
    hfour.exists_ordered_indices
  have hi₃le : i₃ ≤ word.length := by
    dsimp [values] at hi₃
    rw [C.prefixControlValues_length] at hi₃
    omega
  have hi₂le : i₂ ≤ word.length := by omega
  have hi₁le : i₁ ≤ word.length := by omega
  have hi₀le : i₀ ≤ word.length := by omega
  have heval₀ :
      C.eval letter (word.take i₀) = value := by
    dsimp [values] at hget₀
    rw [C.prefixControlValues_getElem?_of_le
      letter word hi₀le] at hget₀
    exact Option.some.inj hget₀
  have heval₁ :
      C.eval letter (word.take i₁) = value := by
    dsimp [values] at hget₁
    rw [C.prefixControlValues_getElem?_of_le
      letter word hi₁le] at hget₁
    exact Option.some.inj hget₁
  have heval₂ :
      C.eval letter (word.take i₂) = value := by
    dsimp [values] at hget₂
    rw [C.prefixControlValues_getElem?_of_le
      letter word hi₂le] at hget₂
    exact Option.some.inj hget₂
  have heval₃ :
      C.eval letter (word.take i₃) = value := by
    dsimp [values] at hget₃
    rw [C.prefixControlValues_getElem?_of_le
      letter word hi₃le] at hget₃
    exact Option.some.inj hget₃
  exact ⟨{
    i₀ := i₀
    i₁ := i₁
    i₂ := i₂
    i₃ := i₃
    lt₀₁ := h₀₁
    lt₁₂ := h₁₂
    lt₂₃ := h₂₃
    i₃_le := hi₃le
    equal₀₁ := heval₀.trans heval₁.symm
    equal₀₂ := heval₀.trans heval₂.symm
    equal₀₃ := heval₀.trans heval₃.symm
  }⟩

end ControlMonoid

end NSSE
