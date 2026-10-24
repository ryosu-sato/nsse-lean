import NSSE.LocalDivisorGapForest
import NSSE.RamseyanSplit
import NSSE.BoundaryRankLists
import NSSE.LocalIdempotentStabilizer

/-!
# Concrete cuts around shared pivot boundaries

A cut of the gap sequence denotes one concrete pivot occurrence in the word
obtained by sharing adjacent delimiters.  That occurrence has two ordinary
word cuts: immediately before it and immediately after it.
-/

namespace NSSE

universe u

def sharedPivotWord
    (pivot : α) (gaps : List (Word α)) : Word α :=
  pivot :: joinPivotGaps pivot gaps ++ [pivot]

theorem sharedPivotWord_cons
    (pivot : α) (gap : Word α)
    (gaps : List (Word α))
    (hgaps : gaps ≠ []) :
    sharedPivotWord pivot (gap :: gaps) =
      pivot :: gap ++ sharedPivotWord pivot gaps := by
  cases gaps with
  | nil =>
      exact False.elim (hgaps rfl)
  | cons next rest =>
      simp [sharedPivotWord, joinPivotGaps,
        List.append_assoc]

def gapPrefixWidth
    (gaps : List (Word α)) (count : Nat) : Nat :=
  ((gaps.take count).map List.length).sum +
    (gaps.take count).length

@[simp] theorem gapPrefixWidth_zero
    (gaps : List (Word α)) :
    gapPrefixWidth gaps 0 = 0 := by
  simp [gapPrefixWidth]

theorem gapPrefixWidth_succ
    (gap : Word α) (gaps : List (Word α))
    (count : Nat) :
    gapPrefixWidth (gap :: gaps) (count + 1) =
      gap.length + 1 +
        gapPrefixWidth gaps count := by
  simp [gapPrefixWidth]
  omega

theorem natListSum_append
    (left right : List Nat) :
    (left ++ right).sum =
      left.sum + right.sum := by
  induction left with
  | nil => simp
  | cons value left ih =>
      simp only [List.cons_append,
        List.sum_cons, ih]
      omega

theorem gapPrefixWidth_le_total
    (gaps : List (Word α)) (count : Nat) :
    gapPrefixWidth gaps count ≤
      (gaps.map List.length).sum + gaps.length := by
  induction gaps generalizing count with
  | nil =>
      simp [gapPrefixWidth]
  | cons gap gaps ih =>
      cases count with
      | zero =>
          simp [gapPrefixWidth]
      | succ count =>
          rw [gapPrefixWidth_succ]
          simp only [List.map_cons, List.sum_cons,
            List.length_cons]
          have htail := ih count
          omega

theorem gapPrefixWidth_all
    (gaps : List (Word α)) :
    gapPrefixWidth gaps gaps.length =
      (gaps.map List.length).sum + gaps.length := by
  simp [gapPrefixWidth]

theorem gapPrefixWidth_index_succ
    (gaps : List (Word α))
    (index : Fin gaps.length) :
    gapPrefixWidth gaps (index.1 + 1) =
      gapPrefixWidth gaps index.1 +
        gaps[index.1].length + 1 := by
  unfold gapPrefixWidth
  rw [← List.take_concat_get index.2]
  simp only [List.concat_eq_append,
    List.map_append, List.map_singleton,
    List.length_append, List.length_singleton]
  rw [natListSum_append]
  simp only [List.sum_cons, List.sum_nil,
    Nat.add_zero]
  omega

theorem gapPrefixWidth_le_shared_length
    (pivot : α) (gaps : List (Word α))
    (count : Nat) :
    gapPrefixWidth gaps count ≤
      (sharedPivotWord pivot gaps).length := by
  have htotal :=
    gapPrefixWidth_le_total gaps count
  cases gaps with
  | nil =>
      simp [sharedPivotWord, gapPrefixWidth]
  | cons gap rest =>
      have hjoin :=
        PivotGapDecomposition.join_length_succ
          pivot (gap :: rest)
          (by simp)
      simp only [sharedPivotWord,
        List.length_cons, List.length_append,
        List.length_singleton]
      omega

theorem gapPrefixWidth_succ_le_shared_length
    (pivot : α) (gaps : List (Word α))
    (cut : WordCut gaps) :
    gapPrefixWidth gaps cut.1 + 1 ≤
      (sharedPivotWord pivot gaps).length := by
  cases gaps with
  | nil =>
      have hcut : cut.1 = 0 := by
        have hbound := cut.2
        change cut.1 < 0 + 1 at hbound
        omega
      simp [sharedPivotWord, gapPrefixWidth, hcut]
  | cons gap rest =>
      have hcutLe :
          cut.1 ≤ (gap :: rest).length := by
        exact cut.val_le_length
      have htakeLength :
          ((gap :: rest).take cut.1).length =
            cut.1 := by
        exact List.length_take_of_le hcutLe
      have hsumLe :=
        gapPrefixWidth_le_total
          (gap :: rest) cut.1
      have hjoin :=
        PivotGapDecomposition.join_length_succ
          pivot (gap :: rest)
          (by simp)
      simp only [sharedPivotWord,
        List.length_cons, List.length_append,
        List.length_singleton]
      omega

def gapCutBefore
    (pivot : α) (gaps : List (Word α))
    (cut : WordCut gaps) :
    WordCut (sharedPivotWord pivot gaps) :=
  ⟨gapPrefixWidth gaps cut.1, by
    have hle :=
      gapPrefixWidth_le_shared_length
        pivot gaps cut.1
    omega⟩

def gapCutAfter
    (pivot : α) (gaps : List (Word α))
    (cut : WordCut gaps) :
    WordCut (sharedPivotWord pivot gaps) :=
  ⟨gapPrefixWidth gaps cut.1 + 1, by
    have hle :=
      gapPrefixWidth_succ_le_shared_length
        pivot gaps cut
    omega⟩

def gapIndexCut
    (gaps : List (Word α))
    (index : Fin gaps.length) :
    WordCut gaps :=
  ⟨index.1, by omega⟩

def gapIndexSuccCut
    (gaps : List (Word α))
    (index : Fin gaps.length) :
    WordCut gaps :=
  ⟨index.1 + 1, by omega⟩

def gapLocalCutIntoShared
    (pivot : α) (gaps : List (Word α))
    (index : Fin gaps.length)
    (cut : WordCut gaps[index.1]) :
    WordCut (sharedPivotWord pivot gaps) :=
  ⟨gapPrefixWidth gaps index.1 + 1 + cut.1, by
    have hnext :=
      gapPrefixWidth_index_succ gaps index
    have hnextBound :=
      gapPrefixWidth_le_shared_length
        pivot gaps (index.1 + 1)
    have hcutBound := cut.val_le_length
    omega⟩

@[simp] theorem gapLocalCutIntoShared_val
    (pivot : α) (gaps : List (Word α))
    (index : Fin gaps.length)
    (cut : WordCut gaps[index.1]) :
    (gapLocalCutIntoShared
      pivot gaps index cut).1 =
        gapPrefixWidth gaps index.1 + 1 + cut.1 :=
  rfl

@[simp] theorem gapLocalCutIntoShared_start
    (pivot : α) (gaps : List (Word α))
    (index : Fin gaps.length) :
    gapLocalCutIntoShared pivot gaps index
        ⟨0, by omega⟩ =
      gapCutAfter pivot gaps
        (gapIndexCut gaps index) := by
  apply Fin.ext
  rfl

@[simp] theorem gapLocalCutIntoShared_end
    (pivot : α) (gaps : List (Word α))
    (index : Fin gaps.length) :
    gapLocalCutIntoShared pivot gaps index
        ⟨gaps[index.1].length, by omega⟩ =
      gapCutBefore pivot gaps
        (gapIndexSuccCut gaps index) := by
  apply Fin.ext
  simp only [gapLocalCutIntoShared_val,
    gapCutBefore, gapIndexSuccCut,
    gapPrefixWidth_index_succ]
  omega

@[simp] theorem gapCutBefore_val
    (pivot : α) (gaps : List (Word α))
    (cut : WordCut gaps) :
    (gapCutBefore pivot gaps cut).1 =
      gapPrefixWidth gaps cut.1 :=
  rfl

@[simp] theorem gapCutAfter_val
    (pivot : α) (gaps : List (Word α))
    (cut : WordCut gaps) :
    (gapCutAfter pivot gaps cut).1 =
      gapPrefixWidth gaps cut.1 + 1 :=
  rfl

/-!
Every ordinary cut of the shared word is either immediately before a
distinguished pivot, inside one of the gaps (including its two endpoint
cuts), or immediately after a distinguished pivot.  The alternatives are
intentionally allowed to overlap at endpoints.
-/

theorem exists_sharedPivot_cut_location
    (pivot : α) (gaps : List (Word α))
    (hgaps : gaps ≠ [])
    (cut : WordCut (sharedPivotWord pivot gaps)) :
    (∃ boundary : WordCut gaps,
        cut = gapCutBefore pivot gaps boundary) ∨
      (∃ (index : Fin gaps.length)
          (gapCut : WordCut gaps[index.1]),
        cut =
          gapLocalCutIntoShared
            pivot gaps index gapCut) ∨
      (∃ boundary : WordCut gaps,
        cut = gapCutAfter pivot gaps boundary) := by
  induction gaps with
  | nil =>
      exact False.elim (hgaps rfl)
  | cons gap gaps ih =>
      cases gaps with
      | nil =>
          by_cases hstart : cut.1 = 0
          · left
            let boundary : WordCut [gap] :=
              ⟨0, by omega⟩
            refine ⟨boundary, Fin.ext ?_⟩
            simpa [gapCutBefore, gapPrefixWidth] using hstart
          · by_cases hinGap : cut.1 ≤ gap.length + 1
            · right
              left
              let index : Fin ([gap] : List (Word α)).length :=
                ⟨0, by simp⟩
              let gapCut : WordCut gap :=
                ⟨cut.1 - 1, by omega⟩
              refine ⟨index, gapCut, Fin.ext ?_⟩
              simp only [gapLocalCutIntoShared_val]
              change cut.1 =
                gapPrefixWidth [gap] 0 +
                  1 + (cut.1 - 1)
              simp [gapPrefixWidth]
              omega
            · right
              right
              have hcutEnd :
                  cut.1 = gap.length + 2 := by
                have hbound := cut.2
                simp [sharedPivotWord,
                  joinPivotGaps] at hbound
                omega
              let boundary : WordCut [gap] :=
                ⟨1, by simp⟩
              refine ⟨boundary, Fin.ext ?_⟩
              simp only [gapCutAfter_val]
              change cut.1 =
                gapPrefixWidth [gap] 1 + 1
              simp [gapPrefixWidth]
              omega
      | cons next rest =>
          have htailNonempty :
              (next :: rest : List (Word α)) ≠ [] := by
            simp
          by_cases hstart : cut.1 = 0
          · left
            let boundary :
                WordCut (gap :: next :: rest) :=
              ⟨0, by omega⟩
            refine ⟨boundary, Fin.ext ?_⟩
            simpa [gapCutBefore,
              gapPrefixWidth] using hstart
          · by_cases hinGap :
                cut.1 ≤ gap.length + 1
            · right
              left
              let index :
                  Fin (gap :: next :: rest).length :=
                ⟨0, by simp⟩
              let gapCut : WordCut gap :=
                ⟨cut.1 - 1, by omega⟩
              refine ⟨index, gapCut, Fin.ext ?_⟩
              simp only [gapLocalCutIntoShared_val]
              change cut.1 =
                gapPrefixWidth
                    (gap :: next :: rest) 0 +
                  1 + (cut.1 - 1)
              simp [gapPrefixWidth]
              omega
            · have hwordLength :
                  (sharedPivotWord pivot
                      (gap :: next :: rest)).length =
                    gap.length + 1 +
                      (sharedPivotWord pivot
                        (next :: rest)).length := by
                rw [sharedPivotWord_cons
                  pivot gap (next :: rest)
                  htailNonempty]
                simp
                omega
              let tailCut :
                  WordCut
                    (sharedPivotWord pivot
                      (next :: rest)) :=
                ⟨cut.1 - (gap.length + 1), by
                  have hbound := cut.2
                  have hbound' :
                      cut.1 <
                        gap.length + 1 +
                          (sharedPivotWord pivot
                            (next :: rest)).length + 1 := by
                    omega
                  omega⟩
              rcases ih htailNonempty tailCut with
                  ⟨tailBoundary, htail⟩ |
                  ⟨tailIndex, tailGapCut, htail⟩ |
                  ⟨tailBoundary, htail⟩
              · left
                let boundary :
                    WordCut (gap :: next :: rest) :=
                  ⟨tailBoundary.1 + 1, by
                    have hbound := tailBoundary.2
                    simp only [List.length_cons]
                      at hbound ⊢
                    omega⟩
                refine ⟨boundary, Fin.ext ?_⟩
                have htailVal :=
                  congrArg Fin.val htail
                change cut.1 =
                  gapPrefixWidth (gap :: next :: rest)
                    (tailBoundary.1 + 1)
                rw [gapPrefixWidth_succ]
                simp only [gapCutBefore_val]
                  at htailVal
                dsimp [tailCut] at htailVal
                omega
              · right
                left
                let index :
                    Fin (gap :: next :: rest).length :=
                  ⟨tailIndex.1 + 1, by
                    have hbound := tailIndex.2
                    simp only [List.length_cons]
                      at hbound ⊢
                    omega⟩
                have hgap :
                    (gap :: next :: rest)[index.1] =
                      (next :: rest)[tailIndex.1] := by
                  simp [index]
                let liftedGapCut :
                    WordCut
                      (gap :: next :: rest)[index.1] :=
                  ⟨tailGapCut.1, by
                    rw [hgap]
                    exact tailGapCut.2⟩
                refine
                  ⟨index, liftedGapCut, Fin.ext ?_⟩
                have htailVal :=
                  congrArg Fin.val htail
                change cut.1 =
                  gapPrefixWidth (gap :: next :: rest)
                      (tailIndex.1 + 1) +
                    1 + tailGapCut.1
                rw [gapPrefixWidth_succ]
                simp only [gapLocalCutIntoShared_val]
                  at htailVal
                dsimp [tailCut] at htailVal
                omega
              · right
                right
                let boundary :
                    WordCut (gap :: next :: rest) :=
                  ⟨tailBoundary.1 + 1, by
                    have hbound := tailBoundary.2
                    simp only [List.length_cons]
                      at hbound ⊢
                    omega⟩
                refine ⟨boundary, Fin.ext ?_⟩
                have htailVal :=
                  congrArg Fin.val htail
                change cut.1 =
                  gapPrefixWidth (gap :: next :: rest)
                      (tailBoundary.1 + 1) + 1
                rw [gapPrefixWidth_succ]
                simp only [gapCutAfter_val]
                  at htailVal
                dsimp [tailCut] at htailVal
                omega

theorem gapCutBefore_lt_gapCutAfter
    (pivot : α) (gaps : List (Word α))
    (cut : WordCut gaps) :
    (gapCutBefore pivot gaps cut).1 <
      (gapCutAfter pivot gaps cut).1 := by
  simp

def sharedGapPrefix
    (pivot : α) : List (Word α) → Word α
  | [] => []
  | gap :: rest =>
      pivot :: joinPivotGaps pivot (gap :: rest)

def sharedGapSuffix
    (pivot : α) : List (Word α) → Word α
  | [] => []
  | gap :: rest =>
      joinPivotGaps pivot (gap :: rest) ++ [pivot]

theorem sharedGapPrefix_length
    (pivot : α) (gaps : List (Word α)) :
    (sharedGapPrefix pivot gaps).length =
      (gaps.map List.length).sum + gaps.length := by
  cases gaps with
  | nil =>
      simp [sharedGapPrefix]
  | cons gap rest =>
      have hjoin :=
        PivotGapDecomposition.join_length_succ
          pivot (gap :: rest) (by simp)
      simp only [sharedGapPrefix,
        List.length_cons]
      simp only [List.map_cons, List.sum_cons,
        List.length_cons] at hjoin ⊢
      omega

theorem sharedSandwich_length
    (pivot : α) (gaps : List (Word α))
    (hgaps : gaps ≠ []) :
    ([pivot] ++ joinPivotGaps pivot gaps ++
        [pivot]).length =
      (gaps.map List.length).sum +
        gaps.length + 1 := by
  have hjoin :=
    PivotGapDecomposition.join_length_succ
      pivot gaps hgaps
  simp only [List.length_append,
    List.length_singleton]
  omega

theorem totalGapWidth_append
    (left right : List (Word α)) :
    ((left ++ right).map List.length).sum +
        (left ++ right).length =
      ((left.map List.length).sum + left.length) +
        ((right.map List.length).sum + right.length) := by
  simp only [List.map_append,
    List.length_append]
  rw [natListSum_append]
  omega

theorem sharedPivotWord_decompose
    (pivot : α)
    (before middle after : List (Word α))
    (hmiddle : middle ≠ []) :
    sharedPivotWord pivot
        (before ++ middle ++ after) =
      sharedGapPrefix pivot before ++
        ([pivot] ++
          joinPivotGaps pivot middle ++ [pivot]) ++
        sharedGapSuffix pivot after := by
  cases before with
  | nil =>
      cases after with
      | nil =>
          simp [sharedPivotWord,
            sharedGapPrefix, sharedGapSuffix]
      | cons afterHead afterTail =>
          rw [show
            ([] : List (Word α)) ++ middle ++
                (afterHead :: afterTail) =
              middle ++ (afterHead :: afterTail) by simp]
          unfold sharedPivotWord
          rw [joinPivotGaps_append pivot
            middle (afterHead :: afterTail)
            hmiddle (by simp)]
          simp [sharedPivotWord,
            sharedGapPrefix, sharedGapSuffix,
            List.append_assoc]
  | cons beforeHead beforeTail =>
      cases after with
      | nil =>
          rw [show
            (beforeHead :: beforeTail) ++ middle ++
                ([] : List (Word α)) =
              (beforeHead :: beforeTail) ++ middle by
                simp]
          unfold sharedPivotWord
          simp only [List.cons_append]
          have hjoin := joinPivotGaps_append pivot
            (beforeHead :: beforeTail) middle
            (by simp) hmiddle
          simp only [List.cons_append] at hjoin
          rw [hjoin]
          simp [sharedPivotWord,
            sharedGapPrefix, sharedGapSuffix,
            List.append_assoc]
      | cons afterHead afterTail =>
          unfold sharedPivotWord
          simp only [List.cons_append]
          have hjoin :=
            joinPivotGaps_append_three pivot
            (beforeHead :: beforeTail) middle
            (afterHead :: afterTail)
            (by simp) hmiddle (by simp)
          simp only [List.cons_append] at hjoin
          rw [hjoin]
          simp [sharedPivotWord,
            sharedGapPrefix, sharedGapSuffix,
            List.append_assoc]

theorem sharedPivotWord_at_gap_decompose
    (pivot : α)
    (gaps : List (Word α))
    (index : Fin gaps.length) :
    sharedPivotWord pivot gaps =
      (sharedGapPrefix pivot
          (gaps.take index.1) ++ [pivot]) ++
        gaps[index.1] ++
      ([pivot] ++
        sharedGapSuffix pivot
          (gaps.drop (index.1 + 1))) := by
  have htail :=
    List.drop_eq_getElem_cons index.2
  have htake :=
    List.take_append_drop index.1 gaps
  have hdecomp :
      gaps =
        gaps.take index.1 ++
          [gaps[index.1]] ++
            gaps.drop (index.1 + 1) := by
    rw [htail] at htake
    simpa only [List.append_assoc,
      List.cons_append, List.singleton_append]
      using htake.symm
  have hshared :=
    sharedPivotWord_decompose pivot
      (gaps.take index.1)
      [gaps[index.1]]
      (gaps.drop (index.1 + 1))
      (by simp)
  calc
    sharedPivotWord pivot gaps =
        sharedPivotWord pivot
          (gaps.take index.1 ++
            [gaps[index.1]] ++
              gaps.drop (index.1 + 1)) :=
      congrArg (sharedPivotWord pivot)
        hdecomp
    _ = (sharedGapPrefix pivot
            (gaps.take index.1) ++ [pivot]) ++
          gaps[index.1] ++
        ([pivot] ++
          sharedGapSuffix pivot
            (gaps.drop (index.1 + 1))) := by
      simpa [joinPivotGaps,
        List.append_assoc] using hshared

theorem gapLocalCut_interval
    (pivot : α)
    (gaps : List (Word α))
    (index : Fin gaps.length)
    (left right : WordCut gaps[index.1])
    (hle : left.1 ≤ right.1) :
    WordCut.interval
        (sharedPivotWord pivot gaps)
        (gapLocalCutIntoShared
          pivot gaps index left)
        (gapLocalCutIntoShared
          pivot gaps index right) =
      WordCut.interval gaps[index.1]
        left right := by
  let prefixWord :=
    sharedGapPrefix pivot
      (gaps.take index.1) ++ [pivot]
  let suffixWord :=
    [pivot] ++
      sharedGapSuffix pivot
        (gaps.drop (index.1 + 1))
  have hword :
      sharedPivotWord pivot gaps =
        prefixWord ++ gaps[index.1] ++ suffixWord :=
    sharedPivotWord_at_gap_decompose
      pivot gaps index
  have htakeLength :
      (gaps.take index.1).length =
        index.1 :=
    List.length_take_of_le
      (Nat.le_of_lt index.2)
  have hprefixLength :
      prefixWord.length =
        gapPrefixWidth gaps index.1 + 1 := by
    simp only [prefixWord,
      List.length_append,
      List.length_singleton]
    rw [sharedGapPrefix_length]
    unfold gapPrefixWidth
    omega
  unfold WordCut.interval
  simp only [gapLocalCutIntoShared_val]
  change
    ControlMonoid.middleFactor
        (sharedPivotWord pivot gaps)
        (gapPrefixWidth gaps index.1 + 1 +
          left.1)
        (gapPrefixWidth gaps index.1 + 1 +
          right.1) =
      ControlMonoid.middleFactor
        gaps[index.1] left.1 right.1
  calc
    ControlMonoid.middleFactor
        (sharedPivotWord pivot gaps)
        (gapPrefixWidth gaps index.1 + 1 +
          left.1)
        (gapPrefixWidth gaps index.1 + 1 +
          right.1) =
      ControlMonoid.middleFactor
        (prefixWord ++ gaps[index.1] ++
          suffixWord)
        (prefixWord.length + left.1)
        (prefixWord.length + right.1) := by
          rw [hword, hprefixLength]
    _ = ControlMonoid.middleFactor
        gaps[index.1] left.1 right.1 :=
      middleFactor_append_shift
        prefixWord gaps[index.1] suffixWord
        left.1 right.1 hle
        right.val_le_length

structure GapIntervalDecomposition
    (gaps : List (Word α))
    (left right : WordCut gaps) where
  before : List (Word α)
  middle : List (Word α)
  after : List (Word α)
  decompose :
    gaps = before ++ middle ++ after
  middle_ne : middle ≠ []
  left_width :
    gapPrefixWidth gaps left.1 =
      (before.map List.length).sum +
        before.length
  right_width :
    gapPrefixWidth gaps right.1 =
      ((before ++ middle).map List.length).sum +
        (before ++ middle).length

namespace GapIntervalDecomposition

noncomputable def of_lt
    (gaps : List (Word α))
    (left right : WordCut gaps)
    (hlt : left.1 < right.1) :
    GapIntervalDecomposition gaps left right where
  before := gaps.take left.1
  middle :=
    ControlMonoid.middleFactor
      gaps left.1 right.1
  after := gaps.drop right.1
  decompose := by
    exact (ControlMonoid.take_middleFactor_drop
      gaps (Nat.le_of_lt hlt)).symm
  middle_ne := by
    apply ControlMonoid.middleFactor_ne_nil
      gaps hlt right.val_le_length
  left_width := by
    unfold gapPrefixWidth
    rfl
  right_width := by
    have htake :=
      ControlMonoid.take_append_middleFactor
        gaps (Nat.le_of_lt hlt)
    unfold gapPrefixWidth
    rw [← htake]

theorem shared_interval_eq_sandwich
    (pivot : α)
    {gaps : List (Word α)}
    {left right : WordCut gaps}
    (decomposition :
      GapIntervalDecomposition gaps left right) :
    WordCut.interval
        (sharedPivotWord pivot gaps)
        (gapCutBefore pivot gaps left)
        (gapCutAfter pivot gaps right) =
      [pivot] ++
        joinPivotGaps pivot decomposition.middle ++
          [pivot] := by
  let prefixWord :=
    sharedGapPrefix pivot decomposition.before
  let sandwich :=
    [pivot] ++
      joinPivotGaps pivot decomposition.middle ++
        [pivot]
  let suffixWord :=
    sharedGapSuffix pivot decomposition.after
  have hword :
      sharedPivotWord pivot gaps =
        prefixWord ++ sandwich ++ suffixWord := by
    rw [decomposition.decompose]
    exact sharedPivotWord_decompose
      pivot decomposition.before
      decomposition.middle decomposition.after
      decomposition.middle_ne
  have hprefixLength :
      prefixWord.length =
        gapPrefixWidth gaps left.1 := by
    rw [decomposition.left_width]
    exact sharedGapPrefix_length
      pivot decomposition.before
  have hsandwichLength :
      sandwich.length =
        (decomposition.middle.map
          List.length).sum +
          decomposition.middle.length + 1 := by
    exact sharedSandwich_length
      pivot decomposition.middle
      decomposition.middle_ne
  have hcombinedWidth :
      ((decomposition.before ++
          decomposition.middle).map
            List.length).sum +
          (decomposition.before ++
            decomposition.middle).length =
        ((decomposition.before.map
          List.length).sum +
            decomposition.before.length) +
        ((decomposition.middle.map
          List.length).sum +
            decomposition.middle.length) :=
    totalGapWidth_append
      decomposition.before
      decomposition.middle
  have hrightLength :
      gapPrefixWidth gaps right.1 + 1 =
        prefixWord.length + sandwich.length := by
    rw [decomposition.right_width]
    rw [hprefixLength]
    rw [decomposition.left_width]
    omega
  unfold WordCut.interval
  simp only [gapCutBefore_val,
    gapCutAfter_val]
  change
    ControlMonoid.middleFactor
        (sharedPivotWord pivot gaps)
        (gapPrefixWidth gaps left.1)
        (gapPrefixWidth gaps right.1 + 1) =
      sandwich
  calc
    ControlMonoid.middleFactor
        (sharedPivotWord pivot gaps)
        (gapPrefixWidth gaps left.1)
        (gapPrefixWidth gaps right.1 + 1) =
      ControlMonoid.middleFactor
        (prefixWord ++ sandwich ++ suffixWord)
        prefixWord.length
        (prefixWord.length + sandwich.length) := by
          rw [hword, ← hprefixLength,
            hrightLength]
    _ = sandwich :=
      middleFactor_append_three
        prefixWord sandwich suffixWord

end GapIntervalDecomposition

namespace RamseyanSplit

theorem gapLocal_neighbor_control
    (C : ControlMonoid M) (pivot : M)
    (gaps : List (Word M))
    (index : Fin gaps.length)
    {height : Nat}
    (split :
      RamseyanSplit C id gaps[index.1] height)
    {left right : WordCut gaps[index.1]}
    (hneighbors :
      levelNeighbors split.rank left right) :
    C.eval (id : M → M)
        (WordCut.interval
          (sharedPivotWord pivot gaps)
          (gapLocalCutIntoShared
            pivot gaps index left)
          (gapLocalCutIntoShared
            pivot gaps index right)) =
      split.idempotentAt
        (split.rank left) := by
  rw [gapLocalCut_interval
    pivot gaps index left right
    (Nat.le_of_lt hneighbors.1)]
  exact split.neighbor_control
    left right hneighbors

theorem gapLocal_neighbor_idempotent
    (C : ControlMonoid M) (pivot : M)
    (gaps : List (Word M))
    (index : Fin gaps.length)
    {height : Nat}
    (split :
      RamseyanSplit C id gaps[index.1] height)
    {left right : WordCut gaps[index.1]}
    (hneighbors :
      levelNeighbors split.rank left right) :
    C.Idempotent
      (C.eval id
        (WordCut.interval
          (sharedPivotWord pivot gaps)
          (gapLocalCutIntoShared
            pivot gaps index left)
          (gapLocalCutIntoShared
            pivot gaps index right))) := by
  rw [split.gapLocal_neighbor_control
    C pivot gaps index hneighbors]
  exact split.idempotent
    (split.rank left)

theorem sharedPivot_neighbor_control
    (C : ControlMonoid M) (pivot : M)
    {gaps : List (Word M)} {height : Nat}
    (split :
      RamseyanSplit
        (C.localDivisor pivot)
        (C.localGapLetter pivot)
        gaps height)
    {left right : WordCut gaps}
    (hneighbors :
      levelNeighbors split.rank left right) :
    C.eval id
        (WordCut.interval
          (sharedPivotWord pivot gaps)
          (gapCutBefore pivot gaps left)
          (gapCutAfter pivot gaps right)) =
      (split.idempotentAt
        (split.rank left)).1 := by
  let decomposition :=
    GapIntervalDecomposition.of_lt
      gaps left right hneighbors.1
  have hinterval :=
    decomposition.shared_interval_eq_sandwich
      pivot
  have hshared :=
    C.localEval_gaps_val_eq_eval_shared
      pivot decomposition.middle
      decomposition.middle_ne
  have hlocal :=
    split.neighbor_control left right hneighbors
  calc
    C.eval id
        (WordCut.interval
          (sharedPivotWord pivot gaps)
          (gapCutBefore pivot gaps left)
          (gapCutAfter pivot gaps right)) =
      C.eval id
        ([pivot] ++
          joinPivotGaps pivot
            decomposition.middle ++ [pivot]) := by
              rw [hinterval]
    _ = ((C.localDivisor pivot).eval
          (C.localGapLetter pivot)
          decomposition.middle).1 :=
      hshared.symm
    _ = (split.idempotentAt
          (split.rank left)).1 := by
      apply congrArg Subtype.val
      change
        (C.localDivisor pivot).eval
            (C.localGapLetter pivot)
            (WordCut.interval gaps left right) =
          split.idempotentAt
            (split.rank left)
      exact hlocal

theorem sharedPivot_neighbor_local_idempotent
    (C : ControlMonoid M) (pivot : M)
    {gaps : List (Word M)} {height : Nat}
    (split :
      RamseyanSplit
        (C.localDivisor pivot)
        (C.localGapLetter pivot)
        gaps height)
    {left right : WordCut gaps}
    (hneighbors :
      levelNeighbors split.rank left right) :
    (C.localDivisor pivot).Idempotent
      ⟨C.eval id
          (WordCut.interval
            (sharedPivotWord pivot gaps)
            (gapCutBefore pivot gaps left)
            (gapCutAfter pivot gaps right)),
        by
          rw [split.sharedPivot_neighbor_control
            C pivot hneighbors]
          exact (split.idempotentAt
            (split.rank left)).2⟩ := by
  have hidempotent :=
    split.idempotent (split.rank left)
  have hcontrol :=
    split.sharedPivot_neighbor_control
      C pivot hneighbors
  simpa only [hcontrol] using hidempotent

end RamseyanSplit

structure SharedPivotBoundarySplit
    (C : ControlMonoid M) (pivot : M)
    (gaps : List (Word M)) (height : Nat) where
  rank : WordCut gaps → Fin height
  idempotentAt :
    Fin height →
      {value : M //
        C.localDivisorCarrier pivot value}
  local_idempotent :
    ∀ level,
      (C.localDivisor pivot).Idempotent
        (idempotentAt level)
  neighbor_control :
    ∀ left right,
      levelNeighbors rank left right →
      C.eval id
          (WordCut.interval
            (sharedPivotWord pivot gaps)
            (gapCutBefore pivot gaps left)
            (gapCutAfter pivot gaps right)) =
        (idempotentAt (rank left)).1

namespace SharedPivotBoundarySplit

def ofLocalRamseyanSplit
    (C : ControlMonoid M) (pivot : M)
    {gaps : List (Word M)} {height : Nat}
    (split :
      RamseyanSplit
        (C.localDivisor pivot)
        (C.localGapLetter pivot)
        gaps height) :
    SharedPivotBoundarySplit
      C pivot gaps height where
  rank := split.rank
  idempotentAt := split.idempotentAt
  local_idempotent := split.idempotent
  neighbor_control := by
    intro left right hneighbors
    exact split.sharedPivot_neighbor_control
      C pivot hneighbors

theorem before_after_distance_one
    (pivot : M) (gaps : List (Word M))
    (cut : WordCut gaps) :
    (gapCutAfter pivot gaps cut).1 =
      (gapCutBefore pivot gaps cut).1 + 1 := by
  rfl

/-!
The two cuts around one pivot cannot in general receive the same rank in an
ambient Ramseyan split.  Already at the first boundary that equality would
force the pivot itself to be idempotent.  This records the obstruction that
prevents treating a local-divisor boundary split as an ambient split by
simply copying its rank to both sides of every shared pivot.
-/

theorem ambient_idempotent_of_start_boundary_rank_eq
    (C : ControlMonoid M) (pivot : M)
    (gaps : List (Word M)) {height : Nat}
    (split :
      RamseyanSplit C id
        (sharedPivotWord pivot gaps) height)
    (hrank :
      split.rank
          (gapCutBefore pivot gaps
            ⟨0, by omega⟩) =
        split.rank
          (gapCutAfter pivot gaps
            ⟨0, by omega⟩)) :
    C.Idempotent pivot := by
  let before :=
    gapCutBefore pivot gaps
      (⟨0, by omega⟩ : WordCut gaps)
  let after :=
    gapCutAfter pivot gaps
      (⟨0, by omega⟩ : WordCut gaps)
  have hneighbors :
      levelNeighbors split.rank before after := by
    refine ⟨?_, hrank, ?_⟩
    · simp [before, after]
    · intro middle hleft hright
      simp [before, after] at hleft hright
      omega
  have hcontrol :=
    split.neighbor_control
      before after hneighbors
  have hinterval :
      WordCut.interval
          (sharedPivotWord pivot gaps)
          before after =
        [pivot] := by
    simp [before, after, WordCut.interval,
      ControlMonoid.middleFactor,
      sharedPivotWord, gapPrefixWidth]
  rw [hinterval] at hcontrol
  have heval :
      C.eval id [pivot] = pivot := by
    simpa [ControlMonoid.eval] using
      C.mul_one pivot
  rw [heval] at hcontrol
  rw [hcontrol]
  exact split.idempotent (split.rank before)

theorem boundary_rank_idempotent
    (shared :
      SharedPivotBoundarySplit
        C pivot gaps height)
    (cut : WordCut gaps) :
    (C.localDivisor pivot).Idempotent
      (shared.idempotentAt
        (shared.rank cut)) :=
  shared.local_idempotent (shared.rank cut)

theorem boundary_control_mul_after
    (shared :
      SharedPivotBoundarySplit
        C pivot gaps height)
    (cut : WordCut gaps) :
    C.mul
        (shared.idempotentAt
          (shared.rank cut)).1
        (C.localAfter pivot
          (shared.idempotentAt
            (shared.rank cut))) =
      (shared.idempotentAt
        (shared.rank cut)).1 :=
  C.localIdempotent_mul_after
    pivot
    (shared.idempotentAt (shared.rank cut))
    (shared.boundary_rank_idempotent cut)

theorem before_mul_boundary_control
    (shared :
      SharedPivotBoundarySplit
        C pivot gaps height)
    (cut : WordCut gaps) :
    C.mul
        (C.localBefore pivot
          (shared.idempotentAt
            (shared.rank cut)))
        (shared.idempotentAt
          (shared.rank cut)).1 =
      (shared.idempotentAt
        (shared.rank cut)).1 :=
  C.localBefore_mul_localIdempotent
    pivot
    (shared.idempotentAt (shared.rank cut))
    (shared.boundary_rank_idempotent cut)

theorem after_mem_rightStabilizer
    (shared :
      SharedPivotBoundarySplit
        C pivot gaps height)
    (cut : WordCut gaps) :
    (C.rightStabilizer
      (shared.idempotentAt
        (shared.rank cut)).1).carrier
      (C.localAfter pivot
        (shared.idempotentAt
          (shared.rank cut))) :=
  shared.boundary_control_mul_after cut

theorem before_mem_leftStabilizer
    (shared :
      SharedPivotBoundarySplit
        C pivot gaps height)
    (cut : WordCut gaps) :
    (C.leftStabilizer
      (shared.idempotentAt
        (shared.rank cut)).1).carrier
      (C.localBefore pivot
        (shared.idempotentAt
          (shared.rank cut))) :=
  shared.before_mul_boundary_control cut

noncomputable def boundaryLiftStep
    (shared :
      SharedPivotBoundarySplit
        C pivot gaps height)
    (cut : WordCut gaps) :
    C.LocalIdempotentLiftStep pivot
      (shared.idempotentAt
        (shared.rank cut)) :=
  C.localIdempotentLiftStep
    pivot
    (shared.idempotentAt (shared.rank cut))
    (shared.boundary_rank_idempotent cut)

theorem neighbor_interval_mul_after
    (shared :
      SharedPivotBoundarySplit
        C pivot gaps height)
    {left right : WordCut gaps}
    (hneighbors :
      levelNeighbors shared.rank left right) :
    C.mul
        (C.eval id
          (WordCut.interval
            (sharedPivotWord pivot gaps)
            (gapCutBefore pivot gaps left)
            (gapCutAfter pivot gaps right)))
        (C.localAfter pivot
          (shared.idempotentAt
            (shared.rank left))) =
      C.eval id
        (WordCut.interval
          (sharedPivotWord pivot gaps)
          (gapCutBefore pivot gaps left)
          (gapCutAfter pivot gaps right)) := by
  rw [shared.neighbor_control
    left right hneighbors]
  exact shared.boundary_control_mul_after left

theorem before_mul_neighbor_interval
    (shared :
      SharedPivotBoundarySplit
        C pivot gaps height)
    {left right : WordCut gaps}
    (hneighbors :
      levelNeighbors shared.rank left right) :
    C.mul
        (C.localBefore pivot
          (shared.idempotentAt
            (shared.rank left)))
        (C.eval id
          (WordCut.interval
            (sharedPivotWord pivot gaps)
            (gapCutBefore pivot gaps left)
            (gapCutAfter pivot gaps right))) =
      C.eval id
        (WordCut.interval
          (sharedPivotWord pivot gaps)
          (gapCutBefore pivot gaps left)
          (gapCutAfter pivot gaps right)) := by
  rw [shared.neighbor_control
    left right hneighbors]
  exact shared.before_mul_boundary_control left

end SharedPivotBoundarySplit

end NSSE
