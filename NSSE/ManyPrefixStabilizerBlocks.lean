import NSSE.FinitePrefixControlLoop

/-!
# Many consecutive stabilizer blocks

An ordered list of equal-prefix-control cuts determines a list of
consecutive nonempty word blocks.  Every block product fixes the common
prefix control on the right, hence belongs to one common right
stabilizer.  Unlike the four-cut interface, the number of blocks is
arbitrary.
-/

namespace NSSE

universe u v

namespace ControlMonoid

def blocksBetweenCuts (word : Word α) : List Nat → List (Word α)
  | first :: second :: rest =>
      middleFactor word first second ::
        blocksBetweenCuts word (second :: rest)
  | _ => []

@[simp] theorem blocksBetweenCuts_nil
    (word : Word α) :
    blocksBetweenCuts word [] = [] :=
  rfl

@[simp] theorem blocksBetweenCuts_singleton
    (word : Word α) (index : Nat) :
    blocksBetweenCuts word [index] = [] :=
  rfl

@[simp] theorem blocksBetweenCuts_cons_cons
    (word : Word α) (first second : Nat) (rest : List Nat) :
    blocksBetweenCuts word (first :: second :: rest) =
      middleFactor word first second ::
        blocksBetweenCuts word (second :: rest) :=
  rfl

theorem blocksBetweenCuts_length
    (word : Word α) :
    ∀ indices,
      (blocksBetweenCuts word indices).length =
        indices.length - 1 := by
  intro indices
  induction indices with
  | nil => rfl
  | cons first tail ih =>
      cases tail with
      | nil => rfl
      | cons second rest =>
          simp only [blocksBetweenCuts_cons_cons,
            List.length_cons]
          have htail := ih
          simp only [List.length_cons] at htail
          rw [htail]
          omega

theorem take_append_flatten_blocksBetweenCuts
    (word : Word α) :
    ∀ first rest,
      (first :: rest).Pairwise (· < ·) →
      ∃ last ∈ first :: rest,
        word.take first ++
            (blocksBetweenCuts word (first :: rest)).flatten =
          word.take last := by
  intro first rest hordered
  induction rest generalizing first with
  | nil =>
      exact ⟨first, by simp, by simp⟩
  | cons second rest ih =>
      have hfirstSecond : first < second :=
        (List.pairwise_cons.mp hordered).1 second (by simp)
      have htailOrdered :
          (second :: rest).Pairwise (· < ·) :=
        (List.pairwise_cons.mp hordered).2
      obtain ⟨last, hlast, htail⟩ :=
        ih second htailOrdered
      refine ⟨last, by simp [hlast], ?_⟩
      simp only [blocksBetweenCuts_cons_cons,
        List.flatten_cons]
      rw [← List.append_assoc,
        take_append_middleFactor word
          (Nat.le_of_lt hfirstSecond)]
      exact htail

theorem exists_blocksBetweenCuts_word_eq
    (word : Word α) (first : Nat) (rest : List Nat)
    (hordered : (first :: rest).Pairwise (· < ·)) :
    ∃ last ∈ first :: rest,
      word.take first ++
          (blocksBetweenCuts word (first :: rest)).flatten ++
          word.drop last =
        word := by
  obtain ⟨last, hlast, hmiddle⟩ :=
    take_append_flatten_blocksBetweenCuts
      word first rest hordered
  refine ⟨last, hlast, ?_⟩
  rw [hmiddle]
  exact List.take_append_drop last word

noncomputable def assembleBlocksBetweenCuts
    {M : Type v} {α : Type u}
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (first : Nat) (rest : List Nat)
    (hordered : (first :: rest).Pairwise (· < ·))
    (middle :
      FactorTree.HeightBoundedForest C letter
        (blocksBetweenCuts word (first :: rest)).flatten bound)
    (before :
      word.take first ≠ [] →
        FactorTree.HeightBoundedForest C letter
          (word.take first) bound)
    (after :
      ∀ last ∈ first :: rest,
        word.drop last ≠ [] →
          FactorTree.HeightBoundedForest C letter
            (word.drop last) bound) :
    FactorTree.HeightBoundedForest C letter word (bound + 2) := by
  have hexists :=
    exists_blocksBetweenCuts_word_eq
      word first rest hordered
  let last := Classical.choose hexists
  have hlast : last ∈ first :: rest :=
    (Classical.choose_spec hexists).1
  have hword :
      word.take first ++
          (blocksBetweenCuts word (first :: rest)).flatten ++
          word.drop last =
        word :=
    (Classical.choose_spec hexists).2
  exact FactorTree.HeightBoundedForest.surround
    middle before (after last hlast) hword

theorem blocksBetweenCuts_ne_nil
    (word : Word α) :
    ∀ {indices : List Nat},
      indices.Pairwise (· < ·) →
      (∀ index ∈ indices, index ≤ word.length) →
      ∀ block ∈ blocksBetweenCuts word indices,
        block ≠ [] := by
  intro indices hordered hbound
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
          have hsecondBound : second ≤ word.length :=
            hbound second (by simp)
          rcases hblock with rfl | hrest
          · exact middleFactor_ne_nil
              word hfirstSecond hsecondBound
          · apply ih
              (List.pairwise_cons.mp hordered).2
              (fun index hindex =>
                hbound index (by simp [hindex]))
              block hrest

theorem blocksBetweenCuts_mem_rightStabilizer
    {M : Type v} {α : Type u}
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (anchor : M) :
    ∀ {indices : List Nat},
      indices.Pairwise (· < ·) →
      (∀ index ∈ indices, index ≤ word.length) →
      (∀ index ∈ indices,
        C.eval letter (word.take index) = anchor) →
      ∀ block ∈ blocksBetweenCuts word indices,
        (C.rightStabilizer anchor).carrier
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
          · exact C.eval_mem_rightStabilizer_of_prefix_eq
              letter anchor (word.take first)
                (middleFactor word first second)
              (hcontrol first (by simp))
              (by
                rw [take_append_middleFactor word
                  (Nat.le_of_lt hfirstSecond)]
                exact hcontrol second (by simp))
          · apply ih
              (List.pairwise_cons.mp hordered).2
              (fun index hindex =>
                hbound index (by simp [hindex]))
              (fun index hindex =>
                hcontrol index (by simp [hindex]))
              block hrest

theorem exists_many_rightStabilizer_blocks
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
        C.eval letter (word.take index) = anchor) ∧
      (blocksBetweenCuts word indices).length = count - 1 ∧
      (∀ block ∈ blocksBetweenCuts word indices, block ≠ []) ∧
      ∀ block ∈ blocksBetweenCuts word indices,
        (C.rightStabilizer anchor).carrier
          (C.eval letter block) := by
  obtain ⟨anchor, indices, hlength, hordered,
    hbound, hcontrol⟩ :=
    C.exists_many_equal_prefix_controls
      elements letter word count hcount hlong
  refine ⟨anchor, indices, hlength, hordered,
    hbound, hcontrol, ?_, ?_, ?_⟩
  · rw [blocksBetweenCuts_length, hlength]
  · exact blocksBetweenCuts_ne_nil
      word hordered hbound
  · exact C.blocksBetweenCuts_mem_rightStabilizer
      letter word anchor hordered hbound hcontrol

end ControlMonoid

end NSSE
