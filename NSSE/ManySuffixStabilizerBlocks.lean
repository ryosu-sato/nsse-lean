import NSSE.ManyPrefixStabilizerBlocks

/-!
# Many consecutive left-stabilizer blocks

This is the suffix-control dual of `ManyPrefixStabilizerBlocks`.  Equal
suffix controls place every intervening block product in one common left
stabilizer.
-/

namespace NSSE

universe u v

namespace ControlMonoid

def suffixControlValues
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) : List M :=
  (List.range (word.length + 1)).map fun index =>
    C.eval letter (word.drop index)

@[simp] theorem suffixControlValues_length
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) :
    (C.suffixControlValues letter word).length =
      word.length + 1 := by
  simp [suffixControlValues]

theorem suffixControlValues_getElem?_of_le
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) {index : Nat}
    (hle : index ≤ word.length) :
    (C.suffixControlValues letter word)[index]? =
      some (C.eval letter (word.drop index)) := by
  have hlt : index < word.length + 1 := by omega
  simp [suffixControlValues, hlt]

theorem middleFactor_append_drop
    (word : Word α) {first second : Nat}
    (hfirstSecond : first ≤ second) :
    middleFactor word first second ++ word.drop second =
      word.drop first := by
  unfold middleFactor
  have hsplit :=
    List.take_append_drop (second - first) (word.drop first)
  have hdrop :
      (word.drop first).drop (second - first) =
        word.drop second := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hdrop] at hsplit
  exact hsplit

theorem exists_many_equal_suffix_controls
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
        C.eval letter (word.drop index) = anchor := by
  let values := C.suffixControlValues letter word
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
    rw [C.suffixControlValues_length] at hlt
    omega
  · intro index hindex
    have hle : index ≤ word.length := by
      have hsome := hget index hindex
      have hlt := (List.getElem?_eq_some_iff.mp hsome).1
      dsimp [values] at hlt
      rw [C.suffixControlValues_length] at hlt
      omega
    have hsuffix :=
      C.suffixControlValues_getElem?_of_le
        letter word hle
    have hanchorAt := hget index hindex
    dsimp [values] at hanchorAt
    rw [hsuffix] at hanchorAt
    exact Option.some.inj hanchorAt

theorem blocksBetweenCuts_mem_leftStabilizer
    {M : Type v} {α : Type u}
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (anchor : M) :
    ∀ {indices : List Nat},
      indices.Pairwise (· < ·) →
      (∀ index ∈ indices, index ≤ word.length) →
      (∀ index ∈ indices,
        C.eval letter (word.drop index) = anchor) →
      ∀ block ∈ blocksBetweenCuts word indices,
        (C.leftStabilizer anchor).carrier
          (C.eval letter block) := by
  intro indices hordered hbound hcontrol
  induction indices with
  | nil =>
      simp
  | cons first tail ih =>
      cases tail with
      | nil =>
          simp
      | cons second rest =>
          intro block hblock
          simp only [blocksBetweenCuts_cons_cons,
            List.mem_cons] at hblock
          have hfirstSecond : first < second :=
            (List.pairwise_cons.mp hordered).1 second (by simp)
          rcases hblock with rfl | hrest
          · change
              C.mul
                (C.eval letter
                  (middleFactor word first second))
                anchor = anchor
            calc
              C.mul
                  (C.eval letter
                    (middleFactor word first second))
                  anchor =
                  C.mul
                    (C.eval letter
                      (middleFactor word first second))
                    (C.eval letter (word.drop second)) := by
                      rw [hcontrol second (by simp)]
              _ =
                  C.eval letter
                    (middleFactor word first second ++
                      word.drop second) := by
                    rw [C.eval_append]
              _ = C.eval letter (word.drop first) := by
                    rw [middleFactor_append_drop word
                      (Nat.le_of_lt hfirstSecond)]
              _ = anchor :=
                    hcontrol first (by simp)
          · apply ih
              (List.pairwise_cons.mp hordered).2
              (fun index hindex =>
                hbound index (by simp [hindex]))
              (fun index hindex =>
                hcontrol index (by simp [hindex]))
              block hrest

theorem exists_many_leftStabilizer_blocks
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
      (∀ index ∈ indices,
        C.eval letter (word.drop index) = anchor) ∧
      (blocksBetweenCuts word indices).length = count - 1 ∧
      (∀ block ∈ blocksBetweenCuts word indices, block ≠ []) ∧
      ∀ block ∈ blocksBetweenCuts word indices,
        (C.leftStabilizer anchor).carrier
          (C.eval letter block) := by
  obtain ⟨anchor, indices, hlength, hordered,
    hbound, hcontrol⟩ :=
    C.exists_many_equal_suffix_controls
      elements letter word count hcount hlong
  refine ⟨anchor, indices, hlength, hordered,
    hbound, hcontrol, ?_, ?_, ?_⟩
  · rw [blocksBetweenCuts_length, hlength]
  · exact blocksBetweenCuts_ne_nil
      word hordered hbound
  · exact C.blocksBetweenCuts_mem_leftStabilizer
      letter word anchor hordered hbound hcontrol

end ControlMonoid

end NSSE
