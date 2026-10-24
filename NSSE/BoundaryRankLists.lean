import NSSE.FiniteColoredLevels
import NSSE.FactorForest
import NSSE.RamseyanSplit

/-!
# Stitching interior boundary-rank lists

Every child tree supplies ranks for its strict interior cuts.  A parent node
joins these lists by inserting one parent rank between consecutive children.
The resulting list has exactly one entry for every strict interior cut of the
parent yield.
-/

namespace NSSE

universe u w

def listLevelNeighbors
    {height : Nat}
    (ranks : List (Fin height))
    (left right : Fin ranks.length) : Prop :=
  left.1 < right.1 ∧
  ranks[left.1] = ranks[right.1] ∧
  ∀ middle : Fin ranks.length,
    left.1 < middle.1 →
    middle.1 < right.1 →
    ranks[middle.1].1 ≤ ranks[left.1].1

theorem getElem_append_separator
    (left right : List ρ) (separator : ρ) :
    (left ++ separator :: right)[left.length] =
      separator := by
  rw [List.getElem_append_right (Nat.le_refl _)]
  simp

theorem getElem_lt_separator_of_index_ne
    {height : Nat}
    (left right : List (Fin height))
    (separator : Fin height)
    (hleft :
      ∀ rank ∈ left, rank.1 < separator.1)
    (hright :
      ∀ rank ∈ right, rank.1 < separator.1)
    (index :
      Fin (left ++ separator :: right).length)
    (hne : index.1 ≠ left.length) :
    (left ++ separator :: right)[index.1].1 <
      separator.1 := by
  rcases Nat.lt_or_gt_of_ne hne with hbefore | hafter
  · rw [List.getElem_append_left hbefore]
    exact hleft _ (List.getElem_mem hbefore)
  · rw [List.getElem_append_right (by omega)]
    let shifted := index.1 - left.length - 1
    have hshifted :
        shifted < right.length := by
      have hbound := index.2
      simp only [List.length_append,
        List.length_cons] at hbound
      dsimp only [shifted]
      omega
    have hindex :
        index.1 - left.length =
          shifted + 1 := by
      dsimp only [shifted]
      omega
    have htailBound :
        index.1 - left.length <
          (separator :: right).length := by
      have hbound := index.2
      simp only [List.length_append,
        List.length_cons] at hbound ⊢
      omega
    have hshiftedSucc :
        shifted + 1 <
          (separator :: right).length := by
      simp only [List.length_cons]
      omega
    calc
      ((separator :: right)[
        index.1 - left.length]'htailBound).1 =
          ((separator :: right)[
            shifted + 1]'hshiftedSucc).1 := by
            congr 2
      _ = right[shifted].1 := by
        rw [List.getElem_cons_succ]
      _ < separator.1 :=
        hright _ (List.getElem_mem hshifted)

theorem listLevelNeighbors_binary_side
    {height : Nat}
    (left right : List (Fin height))
    (separator : Fin height)
    (hleft :
      ∀ rank ∈ left, rank.1 < separator.1)
    (hright :
      ∀ rank ∈ right, rank.1 < separator.1)
    {first last :
      Fin (left ++ separator :: right).length}
    (hneighbors :
      listLevelNeighbors
        (left ++ separator :: right) first last) :
    last.1 < left.length ∨
      left.length < first.1 := by
  have horder := hneighbors.1
  have hrankEq := hneighbors.2.1
  by_cases hfirstSeparator :
      first.1 = left.length
  · have hlastNe :
        last.1 ≠ left.length := by
      omega
    have hlastBelow :=
      getElem_lt_separator_of_index_ne
        left right separator hleft hright
        last hlastNe
    have hfirstRank :
        (left ++ separator :: right)[first.1] =
          separator := by
      calc
        (left ++ separator :: right)[first.1] =
            (left ++ separator :: right)[left.length] := by
              congr 2
        _ = separator :=
          getElem_append_separator
            left right separator
    rw [hfirstRank] at hrankEq
    have hval := congrArg Fin.val hrankEq
    omega
  · by_cases hlastSeparator :
      last.1 = left.length
    · have hfirstBelow :=
        getElem_lt_separator_of_index_ne
          left right separator hleft hright
          first hfirstSeparator
      have hlastRank :
          (left ++ separator :: right)[last.1] =
            separator := by
        calc
          (left ++ separator :: right)[last.1] =
              (left ++ separator :: right)[left.length] := by
                congr 2
          _ = separator :=
            getElem_append_separator
              left right separator
      rw [hlastRank] at hrankEq
      have hval := congrArg Fin.val hrankEq
      omega
    · by_cases hlastBefore :
        last.1 < left.length
      · exact Or.inl hlastBefore
      · by_cases hfirstAfter :
          left.length < first.1
        · exact Or.inr hfirstAfter
        · have hfirstBefore :
            first.1 < left.length := by
            omega
          have hlastAfter :
              left.length < last.1 := by
            omega
          let middle :
              Fin (left ++ separator :: right).length :=
            ⟨left.length, by simp⟩
          have hseparatorLe :=
            hneighbors.2.2 middle
              (by
                simp only [middle]
                omega)
              (by
                simp only [middle]
                omega)
          have hmiddleRank :
              (left ++ separator :: right)[middle.1] =
                separator := by
            simp only [middle]
            exact getElem_append_separator
              left right separator
          rw [hmiddleRank] at hseparatorLe
          have hfirstBelow :=
            getElem_lt_separator_of_index_ne
              left right separator hleft hright
              first hfirstSeparator
          omega

theorem listLevelNeighbors_head_separator_cases
    {height : Nat}
    (head tail : List (Fin height))
    (separator : Fin height)
    (hhead :
      ∀ rank ∈ head, rank.1 < separator.1)
    {first last :
      Fin (head ++ separator :: tail).length}
    (hneighbors :
      listLevelNeighbors
        (head ++ separator :: tail) first last) :
    last.1 < head.length ∨
      (head ++ separator :: tail)[first.1] =
        separator ∨
      head.length < first.1 := by
  have horder := hneighbors.1
  by_cases hlastBefore :
      last.1 < head.length
  · exact Or.inl hlastBefore
  · by_cases hfirstAfter :
      head.length < first.1
    · exact Or.inr (Or.inr hfirstAfter)
    · have hfirstLe :
        first.1 ≤ head.length := by
        omega
      by_cases hfirstAt :
          first.1 = head.length
      · apply Or.inr
        apply Or.inl
        calc
          (head ++ separator :: tail)[first.1] =
              (head ++ separator :: tail)[head.length] := by
                congr 2
          _ = separator :=
            getElem_append_separator
              head tail separator
      · have hfirstBefore :
          first.1 < head.length := by
          omega
        have hfirstBelow :
            (head ++ separator :: tail)[first.1].1 <
              separator.1 := by
          rw [List.getElem_append_left hfirstBefore]
          exact hhead _
            (List.getElem_mem hfirstBefore)
        by_cases hlastAt :
            last.1 = head.length
        · have hlastRank :
              (head ++ separator :: tail)[last.1] =
                separator := by
            calc
              (head ++ separator :: tail)[last.1] =
                  (head ++ separator :: tail)[
                    head.length] := by
                      congr 2
              _ = separator :=
                getElem_append_separator
                  head tail separator
          have hrankEq := hneighbors.2.1
          rw [hlastRank] at hrankEq
          have hval := congrArg Fin.val hrankEq
          omega
        · have hlastAfter :
            head.length < last.1 := by
            omega
          let middle :
              Fin (head ++ separator :: tail).length :=
            ⟨head.length, by simp⟩
          have hseparatorLe :=
            hneighbors.2.2 middle
              (by
                simp only [middle]
                omega)
              (by
                simp only [middle]
                omega)
          have hmiddleRank :
              (head ++ separator :: tail)[middle.1] =
                separator := by
            simp only [middle]
            exact getElem_append_separator
              head tail separator
          rw [hmiddleRank] at hseparatorLe
          omega

theorem listLevelNeighbors_prefix
    {height : Nat}
    (head tail : List (Fin height))
    {first last :
      Fin (head ++ tail).length}
    (hneighbors :
      listLevelNeighbors
        (head ++ tail) first last)
    (hlast : last.1 < head.length) :
    listLevelNeighbors head
      ⟨first.1, by
        have horder := hneighbors.1
        omega⟩
      ⟨last.1, hlast⟩ := by
  have hfirst : first.1 < head.length := by
    have horder := hneighbors.1
    omega
  let prefixFirst : Fin head.length :=
    ⟨first.1, hfirst⟩
  let prefixLast : Fin head.length :=
    ⟨last.1, hlast⟩
  refine ⟨hneighbors.1, ?_, ?_⟩
  · change
      head[first.1]'hfirst =
        head[last.1]'hlast
    rw [← List.getElem_append_left
      hfirst]
    rw [← List.getElem_append_left hlast]
    exact hneighbors.2.1
  · intro middle hfirstMiddle hmiddleLast
    let wholeMiddle :
        Fin (head ++ tail).length :=
      ⟨middle.1, by
        have hmiddleBound := middle.2
        simp only [List.length_append]
        omega⟩
    have hwhole :=
      hneighbors.2.2 wholeMiddle
        (by
          simpa only [wholeMiddle, prefixFirst]
            using hfirstMiddle)
        (by
          simpa only [wholeMiddle, prefixLast]
            using hmiddleLast)
    change (head[middle.1]'middle.2).1 ≤
      (head[first.1]'hfirst).1
    rw [← List.getElem_append_left middle.2]
    rw [← List.getElem_append_left hfirst]
    exact hwhole

theorem listLevelNeighbors_suffix
    {height : Nat}
    (head tail : List (Fin height))
    {first last :
      Fin (head ++ tail).length}
    (hneighbors :
      listLevelNeighbors
        (head ++ tail) first last)
    (hfirst : head.length ≤ first.1) :
    listLevelNeighbors tail
      ⟨first.1 - head.length, by
        have hbound := first.2
        simp only [List.length_append] at hbound
        omega⟩
      ⟨last.1 - head.length, by
        have hbound := last.2
        have horder := hneighbors.1
        have hlast : head.length ≤ last.1 := by
          omega
        simp only [List.length_append] at hbound
        omega⟩ := by
  have hlast : head.length ≤ last.1 := by
    have horder := hneighbors.1
    omega
  have hfirstShift :
      first.1 - head.length < tail.length := by
    have hbound := first.2
    simp only [List.length_append] at hbound
    omega
  have hlastShift :
      last.1 - head.length < tail.length := by
    have hbound := last.2
    simp only [List.length_append] at hbound
    omega
  let tailFirst : Fin tail.length :=
    ⟨first.1 - head.length, hfirstShift⟩
  let tailLast : Fin tail.length :=
    ⟨last.1 - head.length, hlastShift⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [tailFirst, tailLast]
    have horder := hneighbors.1
    omega
  · change
      tail[first.1 - head.length]'hfirstShift =
        tail[last.1 - head.length]'hlastShift
    rw [← List.getElem_append_right hfirst]
    rw [← List.getElem_append_right hlast]
    exact hneighbors.2.1
  · intro middle hfirstMiddle hmiddleLast
    let wholeMiddle :
        Fin (head ++ tail).length :=
      ⟨head.length + middle.1, by
        have hmiddleBound := middle.2
        simp only [List.length_append]
        omega⟩
    have hwholeFirst :
        first.1 < wholeMiddle.1 := by
      simp only [wholeMiddle, tailFirst] at *
      omega
    have hwholeLast :
        wholeMiddle.1 < last.1 := by
      simp only [wholeMiddle, tailLast] at *
      omega
    have hwhole :=
      hneighbors.2.2 wholeMiddle
        hwholeFirst hwholeLast
    change tail[middle.1].1 ≤
      (tail[first.1 - head.length]'hfirstShift).1
    have hmiddleWhole :
        head.length ≤ wholeMiddle.1 := by
      simp only [wholeMiddle]
      omega
    have hmiddleEq :
        (head ++ tail)[wholeMiddle.1] =
          tail[middle.1] := by
      rw [List.getElem_append_right hmiddleWhole]
      congr 2
      simp only [wholeMiddle]
      omega
    have hfirstEq :
        (head ++ tail)[first.1] =
          tail[first.1 - head.length] := by
      exact List.getElem_append_right hfirst
    rw [← hmiddleEq, ← hfirstEq]
    exact hwhole

theorem listLevelNeighbors_after_head_separator
    {height : Nat}
    (head tail : List (Fin height))
    (separator : Fin height)
    {first last :
      Fin (head ++ separator :: tail).length}
    (hneighbors :
      listLevelNeighbors
        (head ++ separator :: tail) first last)
    (hfirstAfter : head.length < first.1) :
    ∃ localFirst localLast : Fin tail.length,
      first.1 =
        head.length + 1 + localFirst.1 ∧
      last.1 =
        head.length + 1 + localLast.1 ∧
      listLevelNeighbors tail
        localFirst localLast := by
  have hafterHead :
      head.length ≤ first.1 := by
    omega
  have htailNeighbors :=
    listLevelNeighbors_suffix
      head (separator :: tail)
      hneighbors hafterHead
  let tailFirst :
      Fin (separator :: tail).length :=
    ⟨first.1 - head.length, by
      have hbound := first.2
      simp only [List.length_append,
        List.length_cons] at hbound ⊢
      omega⟩
  let tailLast :
      Fin (separator :: tail).length :=
    ⟨last.1 - head.length, by
      have hbound := last.2
      simp only [List.length_append,
        List.length_cons] at hbound ⊢
      omega⟩
  have htailFirstPositive :
      1 ≤ tailFirst.1 := by
    simp only [tailFirst]
    omega
  have hrestNeighbors :=
    listLevelNeighbors_suffix
      [separator] tail
      htailNeighbors htailFirstPositive
  let localFirst : Fin tail.length :=
    ⟨tailFirst.1 - 1, by
      have hbound := tailFirst.2
      simp only [List.length_cons] at hbound
      omega⟩
  let localLast : Fin tail.length :=
    ⟨tailLast.1 - 1, by
      have hbound := tailLast.2
      have horder := htailNeighbors.1
      simp only [List.length_cons] at hbound
      omega⟩
  refine ⟨localFirst, localLast, ?_, ?_, ?_⟩
  · simp only [localFirst, tailFirst]
    omega
  · simp only [localLast, tailLast]
    have horder := hneighbors.1
    omega
  · exact hrestNeighbors

theorem getElem_after_head_separator
    (head tail : List ρ)
    (separator : ρ)
    (index :
      Fin (head ++ separator :: tail).length)
    (localIndex : Fin tail.length)
    (hindex :
      index.1 =
        head.length + 1 + localIndex.1) :
    (head ++ separator :: tail)[index.1] =
      tail[localIndex.1] := by
  have hafter : head.length ≤ index.1 := by
    omega
  rw [List.getElem_append_right hafter]
  have hshift :
      index.1 - head.length =
        localIndex.1 + 1 := by
    omega
  have hleftBound :
      index.1 - head.length <
        (separator :: tail).length := by
    have hbound := index.2
    simp only [List.length_append,
      List.length_cons] at hbound ⊢
    omega
  have hrightBound :
      localIndex.1 + 1 <
        (separator :: tail).length := by
    simp only [List.length_cons]
    omega
  calc
    ((separator :: tail)[
      index.1 - head.length]'hleftBound) =
        ((separator :: tail)[
          localIndex.1 + 1]'hrightBound) := by
            congr 2
    _ = tail[localIndex.1] := by
      rw [List.getElem_cons_succ]

theorem listLevelNeighbors_binary_cases
    {height : Nat}
    (left right : List (Fin height))
    (separator : Fin height)
    (hleft :
      ∀ rank ∈ left, rank.1 < separator.1)
    (hright :
      ∀ rank ∈ right, rank.1 < separator.1)
    {first last :
      Fin (left ++ separator :: right).length}
    (hneighbors :
      listLevelNeighbors
        (left ++ separator :: right) first last) :
    (∃ localFirst localLast : Fin left.length,
      localFirst.1 = first.1 ∧
      localLast.1 = last.1 ∧
      listLevelNeighbors left
        localFirst localLast) ∨
    (∃ localFirst localLast : Fin right.length,
      first.1 = left.length + 1 + localFirst.1 ∧
      last.1 = left.length + 1 + localLast.1 ∧
      listLevelNeighbors right
        localFirst localLast) := by
  rcases listLevelNeighbors_binary_side
      left right separator hleft hright
      hneighbors with hleftSide | hrightSide
  · let localFirst : Fin left.length :=
      ⟨first.1, by
        have horder := hneighbors.1
        omega⟩
    let localLast : Fin left.length :=
      ⟨last.1, hleftSide⟩
    refine Or.inl
      ⟨localFirst, localLast, rfl, rfl, ?_⟩
    exact listLevelNeighbors_prefix
      left (separator :: right)
      hneighbors hleftSide
  · have hfirstAfterLeft :
        left.length ≤ first.1 := by
      omega
    exact Or.inr
      (listLevelNeighbors_after_head_separator
        left right separator hneighbors hrightSide)

def stitchInteriorRanks
    (separator : ρ) : List (List ρ) → List ρ
  | [] => []
  | [ranks] => ranks
  | ranks :: next :: rest =>
      ranks ++ separator ::
        stitchInteriorRanks separator (next :: rest)

theorem stitch_getElem_of_located_list
    (separator : ρ)
    (before : List (List ρ))
    (ranks : List ρ)
    (after : List (List ρ))
    (index :
      Fin
        (stitchInteriorRanks separator
          (before ++ ranks :: after)).length)
    (localIndex : Fin ranks.length)
    (hindex :
      index.1 =
        (before.map List.length).sum +
          before.length + localIndex.1) :
    (stitchInteriorRanks separator
      (before ++ ranks :: after))[index.1] =
        ranks[localIndex.1] := by
  induction before with
  | nil =>
      cases after with
      | nil =>
          have hindexValue :
              index.1 = localIndex.1 := by
            simpa using hindex
          have hbound :
              index.1 < ranks.length := by
            simpa only [List.nil_append,
              List.append_nil,
              stitchInteriorRanks] using index.2
          simpa only [List.nil_append,
            List.append_nil,
            stitchInteriorRanks] using
            (getElem_congr
              (c := ranks) (d := ranks)
              rfl hindexValue hbound)
      | cons next after =>
          have hwholeBound :
              index.1 <
                (ranks ++ separator ::
                  stitchInteriorRanks separator
                    (next :: after)).length := by
            simpa only [List.nil_append,
              stitchInteriorRanks] using index.2
          have hindexValue :
              index.1 = localIndex.1 := by
            simpa using hindex
          have heq :
              (ranks ++ separator ::
                stitchInteriorRanks separator
                  (next :: after))[
                    index.1]'hwholeBound =
              (ranks ++ separator ::
                stitchInteriorRanks separator
                  (next :: after))[localIndex.1] := by
                  congr 2
          rw [List.getElem_append_left
            localIndex.2] at heq
          simpa only [List.nil_append,
            stitchInteriorRanks] using heq
  | cons head before ih =>
      have hstitch :
          stitchInteriorRanks separator
              (head :: before ++ ranks :: after) =
            head ++ separator ::
              stitchInteriorRanks separator
                (before ++ ranks :: after) := by
        cases before <;>
          simp [stitchInteriorRanks]
      have hwholeBound :
          index.1 <
            (head ++ separator ::
              stitchInteriorRanks separator
                (before ++ ranks :: after)).length := by
        have hlength :=
          congrArg List.length hstitch
        have hbound := index.2
        omega
      let wholeIndex :
          Fin
            (head ++ separator ::
              stitchInteriorRanks separator
                (before ++ ranks :: after)).length :=
        ⟨index.1, hwholeBound⟩
      have hafterHead :
          head.length < wholeIndex.1 := by
        simp only [List.map_cons, List.sum_cons,
          List.length_cons] at hindex
        simp only [wholeIndex]
        omega
      let tailIndex :
          Fin
            (stitchInteriorRanks separator
              (before ++ ranks :: after)).length :=
        ⟨wholeIndex.1 - head.length - 1, by
          have hbound := wholeIndex.2
          simp only [List.length_append,
            List.length_cons] at hbound
          omega⟩
      have hglobal :
          wholeIndex.1 =
            head.length + 1 + tailIndex.1 := by
        simp only [tailIndex]
        omega
      have heq :
        (head ++ separator ::
            stitchInteriorRanks separator
              (before ++ ranks :: after))[wholeIndex.1] =
          (stitchInteriorRanks separator
            (before ++ ranks :: after))[tailIndex.1] :=
              getElem_after_head_separator
                head
                (stitchInteriorRanks separator
                  (before ++ ranks :: after))
                separator wholeIndex tailIndex hglobal
      have htail :
          (stitchInteriorRanks separator
            (before ++ ranks :: after))[tailIndex.1] =
              ranks[localIndex.1] := by
        apply ih tailIndex
        simp only [List.map_cons,
          List.sum_cons, List.length_cons]
          at hindex
        simp only [tailIndex, wholeIndex]
        omega
      calc
        (stitchInteriorRanks separator
          (head :: before ++ ranks :: after))[index.1] =
            (head ++ separator ::
              stitchInteriorRanks separator
                (before ++ ranks :: after))[index.1] :=
          List.getElem_of_eq hstitch index.2
        _ = ranks[localIndex.1] :=
          heq.trans htail

theorem listLevelNeighbors_stitch_cases
    {height : Nat}
    (separator : Fin height)
    (rankLists : List (List (Fin height)))
    (hbelow :
      ∀ ranks ∈ rankLists,
        ∀ rank ∈ ranks,
          rank.1 < separator.1)
    {first last :
      Fin
        (stitchInteriorRanks
          separator rankLists).length}
    (hneighbors :
      listLevelNeighbors
        (stitchInteriorRanks separator rankLists)
        first last) :
    (stitchInteriorRanks separator rankLists)[first.1] =
        separator ∨
      ∃ ranks ∈ rankLists,
        ∃ localFirst localLast : Fin ranks.length,
          listLevelNeighbors ranks
            localFirst localLast := by
  induction rankLists with
  | nil =>
      simp only [stitchInteriorRanks,
        List.length_nil] at first
      exact Fin.elim0 first
  | cons head rest ih =>
      cases rest with
      | nil =>
          apply Or.inr
          refine ⟨head, by simp, first, last, ?_⟩
          simpa only [stitchInteriorRanks]
            using hneighbors
      | cons next rest =>
          have hhead :
              ∀ rank ∈ head,
                rank.1 < separator.1 := by
            intro rank hrank
            exact hbelow head (by simp) rank hrank
          have htailBelow :
              ∀ ranks ∈ next :: rest,
                ∀ rank ∈ ranks,
                  rank.1 < separator.1 := by
            intro ranks hranks rank hrank
            exact hbelow ranks
              (by simp [hranks]) rank hrank
          change
            listLevelNeighbors
              (head ++ separator ::
                stitchInteriorRanks separator
                  (next :: rest))
              first last at hneighbors
          rcases
              listLevelNeighbors_head_separator_cases
                head
                (stitchInteriorRanks separator
                  (next :: rest))
                separator hhead hneighbors with
            hheadSide | hseparator | htailSide
          · apply Or.inr
            refine ⟨head, by simp, ?_⟩
            let localFirst : Fin head.length :=
              ⟨first.1, by
                have horder := hneighbors.1
                omega⟩
            let localLast : Fin head.length :=
              ⟨last.1, hheadSide⟩
            exact ⟨localFirst, localLast,
              listLevelNeighbors_prefix
                head
                (separator ::
                  stitchInteriorRanks separator
                    (next :: rest))
                hneighbors hheadSide⟩
          · exact Or.inl hseparator
          · obtain ⟨tailFirst, tailLast,
              hfirstMap, hlastMap,
              htailNeighbors⟩ :=
              listLevelNeighbors_after_head_separator
                head
                (stitchInteriorRanks separator
                  (next :: rest))
                separator hneighbors htailSide
            rcases ih htailBelow htailNeighbors with
              htailSeparator | hchild
            · apply Or.inl
              calc
                (head ++ separator ::
                    stitchInteriorRanks separator
                      (next :: rest))[first.1] =
                    (stitchInteriorRanks separator
                      (next :: rest))[tailFirst.1] :=
                  getElem_after_head_separator
                    head
                    (stitchInteriorRanks separator
                      (next :: rest))
                    separator first tailFirst
                    hfirstMap
                _ = separator := htailSeparator
            · apply Or.inr
              obtain ⟨ranks, hranks,
                localFirst, localLast,
                hlocal⟩ := hchild
              exact ⟨ranks, by simp [hranks],
                localFirst, localLast, hlocal⟩

theorem listLevelNeighbors_stitch_located_cases
    {height : Nat}
    (separator : Fin height)
    (rankLists : List (List (Fin height)))
    (hbelow :
      ∀ ranks ∈ rankLists,
        ∀ rank ∈ ranks,
          rank.1 < separator.1)
    {first last :
      Fin
        (stitchInteriorRanks
          separator rankLists).length}
    (hneighbors :
      listLevelNeighbors
        (stitchInteriorRanks separator rankLists)
        first last) :
    (stitchInteriorRanks separator rankLists)[first.1] =
        separator ∨
      ∃ before ranks after,
        rankLists = before ++ ranks :: after ∧
        ∃ localFirst localLast : Fin ranks.length,
          first.1 =
            (before.map List.length).sum +
              before.length + localFirst.1 ∧
          last.1 =
            (before.map List.length).sum +
              before.length + localLast.1 ∧
          listLevelNeighbors ranks
            localFirst localLast := by
  induction rankLists with
  | nil =>
      simp only [stitchInteriorRanks,
        List.length_nil] at first
      exact Fin.elim0 first
  | cons head rest ih =>
      cases rest with
      | nil =>
          apply Or.inr
          refine ⟨[], head, [], by simp,
            first, last, ?_, ?_, ?_⟩
          · simp
          · simp
          · simpa only [stitchInteriorRanks]
              using hneighbors
      | cons next rest =>
          have hhead :
              ∀ rank ∈ head,
                rank.1 < separator.1 := by
            intro rank hrank
            exact hbelow head (by simp) rank hrank
          have htailBelow :
              ∀ ranks ∈ next :: rest,
                ∀ rank ∈ ranks,
                  rank.1 < separator.1 := by
            intro ranks hranks rank hrank
            exact hbelow ranks
              (by simp [hranks]) rank hrank
          change
            listLevelNeighbors
              (head ++ separator ::
                stitchInteriorRanks separator
                  (next :: rest))
              first last at hneighbors
          rcases
              listLevelNeighbors_head_separator_cases
                head
                (stitchInteriorRanks separator
                  (next :: rest))
                separator hhead hneighbors with
            hheadSide | hseparator | htailSide
          · apply Or.inr
            let localFirst : Fin head.length :=
              ⟨first.1, by
                have horder := hneighbors.1
                omega⟩
            let localLast : Fin head.length :=
              ⟨last.1, hheadSide⟩
            refine ⟨[], head, next :: rest,
              by simp, localFirst, localLast,
              by simp [localFirst],
              by simp [localLast], ?_⟩
            exact listLevelNeighbors_prefix
              head
              (separator ::
                stitchInteriorRanks separator
                  (next :: rest))
              hneighbors hheadSide
          · exact Or.inl hseparator
          · obtain ⟨tailFirst, tailLast,
                hfirstMap, hlastMap,
                htailNeighbors⟩ :=
              listLevelNeighbors_after_head_separator
                head
                (stitchInteriorRanks separator
                  (next :: rest))
                separator hneighbors htailSide
            rcases ih htailBelow htailNeighbors with
              htailSeparator | hlocated
            · apply Or.inl
              calc
                (head ++ separator ::
                    stitchInteriorRanks separator
                      (next :: rest))[first.1] =
                    (stitchInteriorRanks separator
                      (next :: rest))[tailFirst.1] :=
                  getElem_after_head_separator
                    head
                    (stitchInteriorRanks separator
                      (next :: rest))
                    separator first tailFirst
                    hfirstMap
                _ = separator := htailSeparator
            · apply Or.inr
              obtain ⟨before, ranks, after,
                hdecomp, localFirst, localLast,
                hlocalFirst, hlocalLast,
                hlocalNeighbors⟩ := hlocated
              refine ⟨head :: before, ranks, after,
                ?_, localFirst, localLast,
                ?_, ?_, hlocalNeighbors⟩
              · simp only [List.cons_append]
                rw [← hdecomp]
              · simp only [List.map_cons,
                  List.sum_cons, List.length_cons]
                omega
              · simp only [List.map_cons,
                  List.sum_cons, List.length_cons]
                omega

theorem stitch_separator_index_decomposition
    {height : Nat}
    (separator : Fin height)
    (rankLists : List (List (Fin height)))
    (hbelow :
      ∀ ranks ∈ rankLists,
        ∀ rank ∈ ranks,
          rank.1 < separator.1)
    (index :
      Fin
        (stitchInteriorRanks
          separator rankLists).length)
    (hseparator :
      (stitchInteriorRanks separator
        rankLists)[index.1] = separator) :
    ∃ before after,
      rankLists = before ++ after ∧
      before ≠ [] ∧ after ≠ [] ∧
      index.1 + 1 =
        (before.map List.length).sum +
          before.length := by
  induction rankLists with
  | nil =>
      simp only [stitchInteriorRanks,
        List.length_nil] at index
      exact Fin.elim0 index
  | cons head rest ih =>
      cases rest with
      | nil =>
          have hindexBound :
              index.1 < head.length := by
            simpa only [stitchInteriorRanks]
              using index.2
          have hmember :
              head[index.1] ∈ head :=
            List.getElem_mem hindexBound
          have hbelowIndex :=
            hbelow head (by simp) head[index.1]
              hmember
          have heq :
              head[index.1] = separator := by
            simpa only [stitchInteriorRanks]
              using hseparator
          have hvalue := congrArg Fin.val heq
          omega
      | cons next rest =>
          have hheadBelow :
              ∀ rank ∈ head,
                rank.1 < separator.1 := by
            intro rank hrank
            exact hbelow head (by simp) rank hrank
          have htailBelow :
              ∀ ranks ∈ next :: rest,
                ∀ rank ∈ ranks,
                  rank.1 < separator.1 := by
            intro ranks hranks rank hrank
            exact hbelow ranks
              (by simp [hranks]) rank hrank
          have hwholeBound :
              index.1 <
                (head ++ separator ::
                  stitchInteriorRanks separator
                    (next :: rest)).length := by
            simpa only [stitchInteriorRanks]
              using index.2
          have hseparatorWhole :
              (head ++ separator ::
                stitchInteriorRanks separator
                  (next :: rest))[index.1]'hwholeBound =
                  separator := by
            simpa only [stitchInteriorRanks]
              using hseparator
          by_cases hbefore :
              index.1 < head.length
          · have hvalueBelow :
                ((head ++ separator ::
                    stitchInteriorRanks separator
                      (next :: rest))[
                        index.1]'hwholeBound).1 <
                  separator.1 := by
              rw [List.getElem_append_left hbefore]
              exact hheadBelow _
                (List.getElem_mem hbefore)
            have hvalue :=
              congrArg Fin.val hseparatorWhole
            omega
          · by_cases hat :
                index.1 = head.length
            · refine ⟨[head], next :: rest, ?_,
                by simp, by simp, ?_⟩
              · simp
              · simp only [List.map_cons, List.map_nil,
                  List.sum_cons, List.sum_nil,
                  List.length_cons, List.length_nil]
                omega
            · have hafter :
                head.length < index.1 := by
                omega
              let tailIndex :
                  Fin
                    (stitchInteriorRanks separator
                      (next :: rest)).length :=
                ⟨index.1 - head.length - 1, by
                  have hbound := index.2
                  simp only [stitchInteriorRanks,
                    List.length_append,
                    List.length_cons] at hbound
                  omega⟩
              have hindexMap :
                  index.1 =
                    head.length + 1 +
                      tailIndex.1 := by
                simp only [tailIndex]
                omega
              have htailSeparator :
                  (stitchInteriorRanks separator
                    (next :: rest))[tailIndex.1] =
                      separator := by
                calc
                  (stitchInteriorRanks separator
                    (next :: rest))[tailIndex.1] =
                      (head ++ separator ::
                        stitchInteriorRanks separator
                          (next :: rest))[index.1] := by
                    symm
                    exact getElem_after_head_separator
                      head
                      (stitchInteriorRanks separator
                        (next :: rest))
                      separator index tailIndex hindexMap
                  _ = separator := hseparatorWhole
              obtain ⟨before, after, hdecomp,
                hbeforeNonempty, hafterNonempty,
                hoffset⟩ :=
                ih htailBelow tailIndex
                  htailSeparator
              refine ⟨head :: before, after, ?_,
                by simp, hafterNonempty, ?_⟩
              · simp only [List.cons_append]
                rw [← hdecomp]
              · simp only [List.map_cons,
                  List.sum_cons, List.length_cons]
                simp only [tailIndex] at hoffset
                omega

theorem stitchInteriorRanks_length_succ
    (separator : ρ) :
    ∀ rankLists : List (List ρ), rankLists ≠ [] →
      (stitchInteriorRanks separator rankLists).length + 1 =
        (rankLists.map List.length).sum +
          rankLists.length := by
  intro rankLists hnonempty
  cases rankLists with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons first rest =>
      induction rest generalizing first with
      | nil =>
          simp [stitchInteriorRanks]
      | cons second rest ih =>
          simp only [stitchInteriorRanks,
            List.length_append, List.length_cons,
            List.map_cons, List.sum_cons]
          have htail := ih second (by simp)
          simp only [List.map_cons, List.sum_cons,
            List.length_cons] at htail
          omega

theorem property_of_mem_stitchInteriorRanks
    (separator : ρ) (rankLists : List (List ρ))
    (P : ρ → Prop)
    (hseparator : P separator)
    (hlists :
      ∀ ranks ∈ rankLists,
        ∀ rank ∈ ranks, P rank) :
    ∀ rank ∈ stitchInteriorRanks separator rankLists,
      P rank := by
  intro rank hrank
  induction rankLists with
  | nil =>
      simp [stitchInteriorRanks] at hrank
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp only [stitchInteriorRanks] at hrank
          exact hlists first (by simp) rank hrank
      | cons second rest =>
          simp only [stitchInteriorRanks,
            List.mem_append, List.mem_cons] at hrank
          rcases hrank with hfirst | rfl | htail
          · exact hlists first (by simp) rank hfirst
          · exact hseparator
          · apply ih
            · intro ranks hranks value hvalue
              exact hlists ranks (by simp [hranks])
                value hvalue
            · exact htail

theorem sum_rank_lengths_eq
    (trees : List (FactorTree α))
    (ranks : FactorTree α → List ρ)
    (haligned :
      ∀ tree ∈ trees,
        (ranks tree).length + 1 =
          tree.yield.length) :
    (trees.map (fun tree => (ranks tree).length)).sum +
        trees.length =
      (trees.map (fun tree => tree.yield.length)).sum := by
  induction trees with
  | nil =>
      rfl
  | cons tree rest ih =>
      simp only [List.map_cons, List.sum_cons,
        List.length_cons]
      have htree := haligned tree (by simp)
      have hrest :
          ∀ child ∈ rest,
            (ranks child).length + 1 =
              child.yield.length := by
        intro child hchild
        exact haligned child (by simp [hchild])
      have htail := ih hrest
      omega

theorem forestYield_length
    (trees : List (FactorTree α)) :
    (FactorTree.forestYield trees).length =
      (trees.map
        (fun tree => tree.yield.length)).sum := by
  induction trees with
  | nil =>
      rfl
  | cons tree rest ih =>
      simp only [FactorTree.forestYield,
        List.flatMap_cons, List.length_append,
        List.map_cons, List.sum_cons]
      exact congrArg (fun n => tree.yield.length + n) ih

theorem middleFactor_append_three
    (before middle after : Word α) :
    ControlMonoid.middleFactor
        (before ++ middle ++ after)
        before.length
        (before.length + middle.length) =
      middle := by
  unfold ControlMonoid.middleFactor
  rw [List.append_assoc]
  rw [List.drop_append_of_le_length
    (Nat.le_refl _)]
  have hlength :
      before.length + middle.length -
          before.length =
        middle.length := by
    omega
  rw [List.drop_length]
  simp only [List.nil_append]
  rw [hlength, List.take_left]

theorem middleFactor_append_shift
    (before middle after : Word α)
    (first last : Nat)
    (horder : first ≤ last)
    (hlast : last ≤ middle.length) :
    ControlMonoid.middleFactor
        (before ++ middle ++ after)
        (before.length + first)
        (before.length + last) =
      ControlMonoid.middleFactor
        middle first last := by
  unfold ControlMonoid.middleFactor
  rw [show
    before.length + last -
        (before.length + first) =
      last - first by omega]
  rw [← List.drop_drop
    (i := first) (j := before.length)]
  rw [List.append_assoc]
  rw [List.drop_append_of_le_length
    (Nat.le_refl _)]
  rw [List.drop_length]
  simp only [List.nil_append]
  rw [List.drop_append_of_le_length
    (by omega : first ≤ middle.length)]
  rw [List.take_append_of_le_length]
  simp only [List.length_drop]
  omega

theorem prefix_split_of_weight_lt
    (weight : β → Nat)
    {whole before later : List β}
    (hbefore : before <+: whole)
    (hlater : later <+: whole)
    (hlt :
      (before.map weight).sum <
        (later.map weight).sum) :
    ∃ middle,
      later = before ++ middle ∧
      middle ≠ [] := by
  rcases List.prefix_or_prefix_of_prefix
      hbefore hlater with
    hbeforeLater | hlaterBefore
  · obtain ⟨middle, hmiddle⟩ := hbeforeLater
    refine ⟨middle, hmiddle.symm, ?_⟩
    intro hempty
    subst middle
    simp only [List.append_nil] at hmiddle
    subst later
    omega
  · obtain ⟨middle, hmiddle⟩ := hlaterBefore
    have hsumAppend :
        ∀ xs ys : List Nat,
          (xs ++ ys).sum = xs.sum + ys.sum := by
      intro xs ys
      induction xs with
      | nil => simp
      | cons value rest ih =>
          simp only [List.sum_cons,
            List.cons_append, ih]
          omega
    have hweight :
        (before.map weight).sum =
          (later.map weight).sum +
            (middle.map weight).sum := by
      rw [← hmiddle]
      rw [List.map_append, hsumAppend]
    omega

theorem stitchInteriorRanks_aligned
    (separator : ρ)
    (trees : List (FactorTree α))
    (htrees : trees ≠ [])
    (ranks : FactorTree α → List ρ)
    (haligned :
      ∀ tree ∈ trees,
        (ranks tree).length + 1 =
          tree.yield.length) :
    (stitchInteriorRanks separator
      (trees.map ranks)).length + 1 =
        (FactorTree.forestYield trees).length := by
  have hmap : trees.map ranks ≠ [] := by
    simpa using htrees
  rw [stitchInteriorRanks_length_succ
    separator (trees.map ranks) hmap]
  simp only [List.map_map, Function.comp_def,
    List.length_map]
  rw [sum_rank_lengths_eq trees ranks haligned]
  exact (forestYield_length trees).symm

structure InteriorRankData
    (ρ : Type w) (tree : FactorTree α) where
  ranks : List ρ
  aligned :
    ranks.length + 1 = tree.yield.length

namespace InteriorRankData

def leaf
    (ρ : Type w) (value : α) :
    InteriorRankData ρ (.leaf value) where
  ranks := []
  aligned := by
    simp [FactorTree.yield]

noncomputable def node
    (separator : ρ)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData ρ child) :
    InteriorRankData ρ (.node children) where
  ranks := by
    classical
    let ranksOf : FactorTree α → List ρ :=
      fun child =>
        if hchild : child ∈ children then
          (data child hchild).ranks
        else
          []
    exact stitchInteriorRanks separator
      (children.map ranksOf)
  aligned := by
    classical
    let ranksOf : FactorTree α → List ρ :=
      fun child =>
        if hchild : child ∈ children then
          (data child hchild).ranks
        else
          []
    have haligned :
        ∀ child ∈ children,
          (ranksOf child).length + 1 =
            child.yield.length := by
      intro child hchild
      simp only [ranksOf]
      rw [dif_pos hchild]
      exact (data child hchild).aligned
    have hstitch :=
      stitchInteriorRanks_aligned separator
        children hchildren ranksOf
        haligned
    simpa only [FactorTree.yield_node] using hstitch

def binary
    (separator : ρ)
    {left right : FactorTree α}
    (leftData : InteriorRankData ρ left)
    (rightData : InteriorRankData ρ right) :
    InteriorRankData ρ
      (.node [left, right]) where
  ranks :=
    leftData.ranks ++ separator :: rightData.ranks
  aligned := by
    simp only [List.length_append, List.length_cons,
      FactorTree.yield, List.flatMap_cons,
      List.flatMap_nil, List.append_nil,
      List.length_append]
    have hleft := leftData.aligned
    have hright := rightData.aligned
    omega

theorem property_of_mem_binary
    (separator : ρ)
    {left right : FactorTree α}
    (leftData : InteriorRankData ρ left)
    (rightData : InteriorRankData ρ right)
    (P : ρ → Prop)
    (hseparator : P separator)
    (hleft :
      ∀ rank ∈ leftData.ranks, P rank)
    (hright :
      ∀ rank ∈ rightData.ranks, P rank) :
    ∀ rank ∈
        (InteriorRankData.binary separator
          leftData rightData).ranks,
      P rank := by
  intro rank hrank
  simp only [binary, List.mem_append,
    List.mem_cons] at hrank
  rcases hrank with hleftRank | rfl | hrightRank
  · exact hleft rank hleftRank
  · exact hseparator
  · exact hright rank hrightRank

theorem binary_listLevelNeighbors_cases
    {height : Nat}
    (separator : Fin height)
    {left right : FactorTree α}
    (leftData :
      InteriorRankData (Fin height) left)
    (rightData :
      InteriorRankData (Fin height) right)
    (hleft :
      ∀ rank ∈ leftData.ranks,
        rank.1 < separator.1)
    (hright :
      ∀ rank ∈ rightData.ranks,
        rank.1 < separator.1)
    {first last :
      Fin
        (InteriorRankData.binary separator
          leftData rightData).ranks.length}
    (hneighbors :
      listLevelNeighbors
        (InteriorRankData.binary separator
          leftData rightData).ranks
        first last) :
    (∃ localFirst localLast :
        Fin leftData.ranks.length,
      localFirst.1 = first.1 ∧
      localLast.1 = last.1 ∧
      listLevelNeighbors leftData.ranks
        localFirst localLast) ∨
    (∃ localFirst localLast :
        Fin rightData.ranks.length,
      first.1 =
        leftData.ranks.length + 1 + localFirst.1 ∧
      last.1 =
        leftData.ranks.length + 1 + localLast.1 ∧
      listLevelNeighbors rightData.ranks
        localFirst localLast) := by
  exact listLevelNeighbors_binary_cases
    leftData.ranks rightData.ranks separator
    hleft hright hneighbors

theorem binary_left_middleFactor_eq
    {height : Nat}
    (separator : Fin height)
    {left right : FactorTree α}
    (leftData :
      InteriorRankData (Fin height) left)
    (rightData :
      InteriorRankData (Fin height) right)
    (first last :
      Fin
        (InteriorRankData.binary separator
          leftData rightData).ranks.length)
    (localFirst localLast :
      Fin leftData.ranks.length)
    (hfirst : localFirst.1 = first.1)
    (hlast : localLast.1 = last.1)
    (horder : localFirst.1 ≤ localLast.1) :
    ControlMonoid.middleFactor
        (FactorTree.node [left, right]).yield
        (first.1 + 1) (last.1 + 1) =
      ControlMonoid.middleFactor left.yield
        (localFirst.1 + 1)
        (localLast.1 + 1) := by
  have hlastBound :
      localLast.1 + 1 ≤ left.yield.length := by
    have hbound := localLast.2
    have haligned := leftData.aligned
    omega
  have hyield :
      (FactorTree.node [left, right]).yield =
        left.yield ++ right.yield := by
    simp [FactorTree.yield]
  rw [hyield, ← hfirst, ← hlast]
  simpa only [List.nil_append, List.append_nil,
    List.length_nil, Nat.zero_add] using
    (middleFactor_append_shift
      ([] : Word α) left.yield right.yield
      (localFirst.1 + 1)
      (localLast.1 + 1)
      (by omega) hlastBound)

theorem binary_right_middleFactor_eq
    {height : Nat}
    (separator : Fin height)
    {left right : FactorTree α}
    (leftData :
      InteriorRankData (Fin height) left)
    (rightData :
      InteriorRankData (Fin height) right)
    (first last :
      Fin
        (InteriorRankData.binary separator
          leftData rightData).ranks.length)
    (localFirst localLast :
      Fin rightData.ranks.length)
    (hfirst :
      first.1 =
        leftData.ranks.length + 1 +
          localFirst.1)
    (hlast :
      last.1 =
        leftData.ranks.length + 1 +
          localLast.1)
    (horder : localFirst.1 ≤ localLast.1) :
    ControlMonoid.middleFactor
        (FactorTree.node [left, right]).yield
        (first.1 + 1) (last.1 + 1) =
      ControlMonoid.middleFactor right.yield
        (localFirst.1 + 1)
        (localLast.1 + 1) := by
  have hleftLength :
      leftData.ranks.length + 1 =
        left.yield.length :=
    leftData.aligned
  have hlastBound :
      localLast.1 + 1 ≤ right.yield.length := by
    have hbound := localLast.2
    have haligned := rightData.aligned
    omega
  have hfirstCut :
      first.1 + 1 =
        left.yield.length +
          (localFirst.1 + 1) := by
    omega
  have hlastCut :
      last.1 + 1 =
        left.yield.length +
          (localLast.1 + 1) := by
    omega
  have hyield :
      (FactorTree.node [left, right]).yield =
        left.yield ++ right.yield := by
    simp [FactorTree.yield]
  rw [hyield, hfirstCut, hlastCut]
  simpa only [List.append_nil] using
    (middleFactor_append_shift
      left.yield right.yield ([] : Word α)
      (localFirst.1 + 1)
      (localLast.1 + 1)
      (by omega) hlastBound)

theorem property_of_mem_node
    (separator : ρ)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData ρ child)
    (P : ρ → Prop)
    (hseparator : P separator)
    (hdata :
      ∀ child (hchild : child ∈ children),
        ∀ rank ∈ (data child hchild).ranks,
          P rank) :
    ∀ rank ∈
        (InteriorRankData.node separator
          children hchildren data).ranks,
      P rank := by
  classical
  intro rank hrank
  unfold InteriorRankData.node at hrank
  dsimp only at hrank
  apply property_of_mem_stitchInteriorRanks
    separator _ P hseparator _ rank hrank
  intro ranks hranks value hvalue
  simp only [List.mem_map] at hranks
  obtain ⟨child, hchild, rfl⟩ := hranks
  split at hvalue
  next hmember =>
    exact hdata child hmember value hvalue
  next hnot =>
    exact False.elim (hnot hchild)

theorem node_listLevelNeighbors_cases
    {height : Nat}
    (separator : Fin height)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData (Fin height) child)
    (hbelow :
      ∀ child (hchild : child ∈ children),
        ∀ rank ∈ (data child hchild).ranks,
          rank.1 < separator.1)
    {first last :
      Fin
        (InteriorRankData.node separator
          children hchildren data).ranks.length}
    (hneighbors :
      listLevelNeighbors
        (InteriorRankData.node separator
          children hchildren data).ranks
        first last) :
    (InteriorRankData.node separator
        children hchildren data).ranks[first.1] =
          separator ∨
      ∃ child, ∃ hchild : child ∈ children,
        ∃ localFirst localLast :
            Fin (data child hchild).ranks.length,
          listLevelNeighbors
            (data child hchild).ranks
            localFirst localLast := by
  classical
  let ranksOf : FactorTree α → List (Fin height) :=
    fun child =>
      if hchild : child ∈ children then
        (data child hchild).ranks
      else
        []
  have hmappedBelow :
      ∀ ranks ∈ children.map ranksOf,
        ∀ rank ∈ ranks,
          rank.1 < separator.1 := by
    intro ranks hranks rank hrank
    simp only [List.mem_map] at hranks
    obtain ⟨child, hchild, rfl⟩ := hranks
    change rank ∈
      (if hmember : child ∈ children then
        (data child hmember).ranks else []) at hrank
    rw [dif_pos hchild] at hrank
    exact hbelow child hchild rank hrank
  unfold InteriorRankData.node at hneighbors ⊢
  dsimp only at hneighbors ⊢
  rcases listLevelNeighbors_stitch_cases
      separator (children.map ranksOf)
      hmappedBelow hneighbors with
    hseparator | hlocal
  · exact Or.inl hseparator
  · apply Or.inr
    obtain ⟨ranks, hranks, localFirst,
      localLast, hlocalNeighbors⟩ := hlocal
    simp only [List.mem_map] at hranks
    obtain ⟨child, hchild, rfl⟩ := hranks
    have hranksOf :
        ranksOf child =
          (data child hchild).ranks := by
      simp only [ranksOf, dif_pos hchild]
    let childFirst :
        Fin (data child hchild).ranks.length :=
      ⟨localFirst.1, by
        have hbound := localFirst.2
        have hlength :=
          congrArg List.length hranksOf
        omega⟩
    let childLast :
        Fin (data child hchild).ranks.length :=
      ⟨localLast.1, by
        have hbound := localLast.2
        have hlength :=
          congrArg List.length hranksOf
        omega⟩
    refine ⟨child, hchild, childFirst,
      childLast, ?_⟩
    unfold listLevelNeighbors at hlocalNeighbors ⊢
    refine ⟨hlocalNeighbors.1, ?_, ?_⟩
    · calc
        (data child hchild).ranks[childFirst.1] =
            (ranksOf child)[localFirst.1] := by
              symm
              exact List.getElem_of_eq
                hranksOf localFirst.2
        _ = (ranksOf child)[localLast.1] :=
          hlocalNeighbors.2.1
        _ = (data child hchild).ranks[childLast.1] :=
          List.getElem_of_eq
            hranksOf localLast.2
    · intro middle hfirstMiddle hmiddleLast
      let sourceMiddle :
          Fin (ranksOf child).length :=
        ⟨middle.1, by
          have hbound := middle.2
          have hlength :=
            congrArg List.length hranksOf
          omega⟩
      have hsource :=
        hlocalNeighbors.2.2 sourceMiddle
          (by
            simpa only [sourceMiddle, childFirst]
              using hfirstMiddle)
          (by
            simpa only [sourceMiddle, childLast]
              using hmiddleLast)
      calc
        (data child hchild).ranks[middle.1].1 =
            (ranksOf child)[sourceMiddle.1].1 := by
              symm
              exact congrArg Fin.val
                (List.getElem_of_eq
                  hranksOf sourceMiddle.2)
        _ ≤ (ranksOf child)[localFirst.1].1 :=
          hsource
        _ = (data child hchild).ranks[
            childFirst.1].1 :=
          congrArg Fin.val
            (List.getElem_of_eq
              hranksOf localFirst.2)

theorem node_listLevelNeighbors_located_cases
    {height : Nat}
    (separator : Fin height)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData (Fin height) child)
    (hbelow :
      ∀ child (hchild : child ∈ children),
        ∀ rank ∈ (data child hchild).ranks,
          rank.1 < separator.1)
    {first last :
      Fin
        (InteriorRankData.node separator
          children hchildren data).ranks.length}
    (hneighbors :
      listLevelNeighbors
        (InteriorRankData.node separator
          children hchildren data).ranks
        first last) :
    (InteriorRankData.node separator
        children hchildren data).ranks[first.1] =
          separator ∨
      ∃ before child after,
        ∃ hchild : child ∈ children,
          children = before ++ child :: after ∧
          ∃ localFirst localLast :
              Fin (data child hchild).ranks.length,
            first.1 =
              (FactorTree.forestYield before).length +
                localFirst.1 ∧
            last.1 =
              (FactorTree.forestYield before).length +
                localLast.1 ∧
            listLevelNeighbors
              (data child hchild).ranks
              localFirst localLast ∧
            (InteriorRankData.node separator
              children hchildren data).ranks[first.1] =
                (data child hchild).ranks[
                  localFirst.1] ∧
            (InteriorRankData.node separator
              children hchildren data).ranks[last.1] =
                (data child hchild).ranks[
                  localLast.1] := by
  classical
  let ranksOf : FactorTree α → List (Fin height) :=
    fun child =>
      if hchild : child ∈ children then
        (data child hchild).ranks
      else
        []
  have hmappedBelow :
      ∀ ranks ∈ children.map ranksOf,
        ∀ rank ∈ ranks,
          rank.1 < separator.1 := by
    intro ranks hranks rank hrank
    simp only [List.mem_map] at hranks
    obtain ⟨child, hchild, rfl⟩ := hranks
    change rank ∈
      (if hmember : child ∈ children then
        (data child hmember).ranks else []) at hrank
    rw [dif_pos hchild] at hrank
    exact hbelow child hchild rank hrank
  unfold InteriorRankData.node at hneighbors ⊢
  dsimp only at hneighbors ⊢
  rcases listLevelNeighbors_stitch_located_cases
      separator (children.map ranksOf)
      hmappedBelow hneighbors with
    hseparator | hlocated
  · exact Or.inl hseparator
  · apply Or.inr
    obtain ⟨beforeRanks, ranks, afterRanks,
      hrankDecomp, rankFirst, rankLast,
      hfirstOffset, hlastOffset,
      hrankNeighbors⟩ := hlocated
    have hstitchDecomp :
        stitchInteriorRanks separator
            (children.map ranksOf) =
          stitchInteriorRanks separator
            (beforeRanks ++ ranks :: afterRanks) :=
      congrArg (stitchInteriorRanks separator)
        hrankDecomp
    let locatedFirst :
        Fin
          (stitchInteriorRanks separator
            (beforeRanks ++ ranks :: afterRanks)).length :=
      ⟨first.1, by
        have hlength :=
          congrArg List.length hstitchDecomp
        have hbound := first.2
        omega⟩
    let locatedLast :
        Fin
          (stitchInteriorRanks separator
            (beforeRanks ++ ranks :: afterRanks)).length :=
      ⟨last.1, by
        have hlength :=
          congrArg List.length hstitchDecomp
        have hbound := last.2
        omega⟩
    have hglobalFirstRank :
        (stitchInteriorRanks separator
          (children.map ranksOf))[first.1] =
            ranks[rankFirst.1] := by
      calc
        (stitchInteriorRanks separator
          (children.map ranksOf))[first.1] =
            (stitchInteriorRanks separator
              (beforeRanks ++ ranks :: afterRanks))[
                locatedFirst.1] := by
                  exact List.getElem_of_eq
                    hstitchDecomp first.2
        _ = ranks[rankFirst.1] := by
          apply stitch_getElem_of_located_list
          simpa only [locatedFirst]
            using hfirstOffset
    have hglobalLastRank :
        (stitchInteriorRanks separator
          (children.map ranksOf))[last.1] =
            ranks[rankLast.1] := by
      calc
        (stitchInteriorRanks separator
          (children.map ranksOf))[last.1] =
            (stitchInteriorRanks separator
              (beforeRanks ++ ranks :: afterRanks))[
                locatedLast.1] := by
                  exact List.getElem_of_eq
                    hstitchDecomp last.2
        _ = ranks[rankLast.1] := by
          apply stitch_getElem_of_located_list
          simpa only [locatedLast]
            using hlastOffset
    obtain ⟨before, remaining,
      hchildrenFirst, hbeforeMap,
      hremainingMap⟩ :=
      List.map_eq_append_iff.mp hrankDecomp
    cases remaining with
    | nil =>
        simp at hremainingMap
    | cons child after =>
        simp only [List.map_cons,
          List.cons.injEq] at hremainingMap
        obtain ⟨hranksOf, hafterMap⟩ :=
          hremainingMap
        have hchildrenDecomp :
            children = before ++ child :: after := by
          exact hchildrenFirst
        have hchild : child ∈ children := by
          rw [hchildrenDecomp]
          simp
        have hranksData :
            ranks =
              (data child hchild).ranks := by
          rw [← hranksOf]
          simp only [ranksOf, dif_pos hchild]
        let localFirst :
            Fin (data child hchild).ranks.length :=
          ⟨rankFirst.1, by
            have hbound := rankFirst.2
            have hlength :=
              congrArg List.length hranksData
            omega⟩
        let localLast :
            Fin (data child hchild).ranks.length :=
          ⟨rankLast.1, by
            have hbound := rankLast.2
            have hlength :=
              congrArg List.length hranksData
            omega⟩
        have hbeforeMember :
            ∀ tree ∈ before,
              tree ∈ children := by
          intro tree htree
          rw [hchildrenDecomp]
          simp [htree]
        have haligned :
            ∀ tree ∈ before,
              (ranksOf tree).length + 1 =
                tree.yield.length := by
          intro tree htree
          have hmember :=
            hbeforeMember tree htree
          simp only [ranksOf]
          rw [dif_pos hmember]
          exact (data tree hmember).aligned
        have hsum :=
          sum_rank_lengths_eq before
            ranksOf haligned
        have hforest :=
          forestYield_length before
        have hprefixWidth :
            (beforeRanks.map List.length).sum +
                beforeRanks.length =
              (FactorTree.forestYield before).length := by
          rw [← hbeforeMap]
          simp only [List.map_map,
            Function.comp_def, List.length_map]
          exact hsum.trans hforest.symm
        refine ⟨before, child, after, hchild,
          hchildrenDecomp, localFirst, localLast,
          ?_, ?_, ?_, ?_, ?_⟩
        · simp only [localFirst]
          omega
        · simp only [localLast]
          omega
        · unfold listLevelNeighbors at hrankNeighbors ⊢
          refine ⟨hrankNeighbors.1, ?_, ?_⟩
          · calc
              (data child hchild).ranks[
                  localFirst.1] =
                ranks[rankFirst.1] := by
                  symm
                  exact List.getElem_of_eq
                    hranksData rankFirst.2
              _ = ranks[rankLast.1] :=
                hrankNeighbors.2.1
              _ = (data child hchild).ranks[
                  localLast.1] :=
                List.getElem_of_eq
                  hranksData rankLast.2
          · intro middle hfirstMiddle hmiddleLast
            let rankMiddle : Fin ranks.length :=
              ⟨middle.1, by
                have hbound := middle.2
                have hlength :=
                  congrArg List.length hranksData
                omega⟩
            have hmiddle :=
              hrankNeighbors.2.2 rankMiddle
                (by
                  simpa only [rankMiddle,
                    localFirst] using hfirstMiddle)
                (by
                  simpa only [rankMiddle,
                    localLast] using hmiddleLast)
            calc
              (data child hchild).ranks[middle.1].1 =
                  ranks[rankMiddle.1].1 := by
                    symm
                    exact congrArg Fin.val
                      (List.getElem_of_eq
                        hranksData rankMiddle.2)
              _ ≤ ranks[rankFirst.1].1 :=
                hmiddle
              _ = (data child hchild).ranks[
                  localFirst.1].1 :=
                congrArg Fin.val
                  (List.getElem_of_eq
                    hranksData rankFirst.2)
        · calc
            (stitchInteriorRanks separator
              (children.map ranksOf))[first.1] =
                ranks[rankFirst.1] :=
              hglobalFirstRank
            _ = (data child hchild).ranks[
                localFirst.1] :=
              List.getElem_of_eq
                hranksData rankFirst.2
        · calc
            (stitchInteriorRanks separator
              (children.map ranksOf))[last.1] =
                ranks[rankLast.1] :=
              hglobalLastRank
            _ = (data child hchild).ranks[
                localLast.1] :=
              List.getElem_of_eq
                hranksData rankLast.2

theorem node_middleFactor_eq_child_middleFactor
    {height : Nat}
    (separator : Fin height)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData (Fin height) child)
    (before : List (FactorTree α))
    (child : FactorTree α)
    (after : List (FactorTree α))
    (hchild : child ∈ children)
    (hdecomp :
      children = before ++ child :: after)
    (first last :
      Fin
        (InteriorRankData.node separator
          children hchildren data).ranks.length)
    (localFirst localLast :
      Fin (data child hchild).ranks.length)
    (hfirst :
      first.1 =
        (FactorTree.forestYield before).length +
          localFirst.1)
    (hlast :
      last.1 =
        (FactorTree.forestYield before).length +
          localLast.1)
    (hlocalOrder :
      localFirst.1 ≤ localLast.1) :
    ControlMonoid.middleFactor
        (FactorTree.node children).yield
        (first.1 + 1) (last.1 + 1) =
      ControlMonoid.middleFactor
        child.yield
        (localFirst.1 + 1)
        (localLast.1 + 1) := by
  have hfirstCut :
      first.1 + 1 =
        (FactorTree.forestYield before).length +
          (localFirst.1 + 1) := by
    omega
  have hlastCut :
      last.1 + 1 =
        (FactorTree.forestYield before).length +
          (localLast.1 + 1) := by
    omega
  have hlocalLast :
      localLast.1 + 1 ≤ child.yield.length := by
    have hbound := localLast.2
    have haligned :=
      (data child hchild).aligned
    omega
  have hyield :
      (FactorTree.node children).yield =
        FactorTree.forestYield before ++
          child.yield ++
            FactorTree.forestYield after := by
    rw [FactorTree.yield_node, hdecomp]
    simp [FactorTree.forestYield,
      List.flatMap_append, List.append_assoc]
  calc
    ControlMonoid.middleFactor
        (FactorTree.node children).yield
        (first.1 + 1) (last.1 + 1) =
      ControlMonoid.middleFactor
        (FactorTree.forestYield before ++
          child.yield ++
            FactorTree.forestYield after)
        ((FactorTree.forestYield before).length +
          (localFirst.1 + 1))
        ((FactorTree.forestYield before).length +
          (localLast.1 + 1)) := by
            rw [hyield, hfirstCut, hlastCut]
    _ = ControlMonoid.middleFactor
        child.yield
        (localFirst.1 + 1)
        (localLast.1 + 1) :=
      middleFactor_append_shift
        (FactorTree.forestYield before)
        child.yield
        (FactorTree.forestYield after)
        (localFirst.1 + 1)
        (localLast.1 + 1)
        (by omega) hlocalLast

theorem node_separator_cut_decomposition
    {height : Nat}
    (separator : Fin height)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData (Fin height) child)
    (hbelow :
      ∀ child (hchild : child ∈ children),
        ∀ rank ∈ (data child hchild).ranks,
          rank.1 < separator.1)
    (index :
      Fin
        (InteriorRankData.node separator
          children hchildren data).ranks.length)
    (hseparator :
      (InteriorRankData.node separator
        children hchildren data).ranks[index.1] =
          separator) :
    ∃ before after,
      children = before ++ after ∧
      before ≠ [] ∧ after ≠ [] ∧
      index.1 + 1 =
        (FactorTree.forestYield before).length := by
  classical
  let ranksOf : FactorTree α → List (Fin height) :=
    fun child =>
      if hchild : child ∈ children then
        (data child hchild).ranks
      else
        []
  have hmappedBelow :
      ∀ ranks ∈ children.map ranksOf,
        ∀ rank ∈ ranks,
          rank.1 < separator.1 := by
    intro ranks hranks rank hrank
    simp only [List.mem_map] at hranks
    obtain ⟨child, hchild, rfl⟩ := hranks
    change rank ∈
      (if hmember : child ∈ children then
        (data child hmember).ranks else []) at hrank
    rw [dif_pos hchild] at hrank
    exact hbelow child hchild rank hrank
  unfold InteriorRankData.node at index hseparator
  dsimp only at index hseparator
  obtain ⟨beforeRanks, afterRanks, hrankDecomp,
      hbeforeRanks, hafterRanks, hoffset⟩ :=
    stitch_separator_index_decomposition
      separator (children.map ranksOf)
      hmappedBelow index hseparator
  obtain ⟨before, after, hchildrenDecomp,
      hbeforeMap, hafterMap⟩ :=
    List.map_eq_append_iff.mp hrankDecomp
  have hbefore : before ≠ [] := by
    intro hempty
    subst before
    simp only [List.map_nil] at hbeforeMap
    exact hbeforeRanks hbeforeMap.symm
  have hafter : after ≠ [] := by
    intro hempty
    subst after
    simp only [List.map_nil] at hafterMap
    exact hafterRanks hafterMap.symm
  have hbeforeMember :
      ∀ child ∈ before, child ∈ children := by
    intro child hchild
    rw [hchildrenDecomp]
    simp [hchild]
  have haligned :
      ∀ child ∈ before,
        (ranksOf child).length + 1 =
          child.yield.length := by
    intro child hchild
    have hmember := hbeforeMember child hchild
    simp only [ranksOf]
    rw [dif_pos hmember]
    exact (data child hmember).aligned
  have hsum :=
    sum_rank_lengths_eq before ranksOf haligned
  have hforestLength :=
    forestYield_length before
  refine ⟨before, after, hchildrenDecomp,
    hbefore, hafter, ?_⟩
  rw [hforestLength]
  rw [← hsum]
  rw [← hbeforeMap] at hoffset
  simpa only [List.map_map, Function.comp_def,
    List.length_map] using hoffset

theorem node_two_separator_cut_decomposition
    {height : Nat}
    (separator : Fin height)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData (Fin height) child)
    (hbelow :
      ∀ child (hchild : child ∈ children),
        ∀ rank ∈ (data child hchild).ranks,
          rank.1 < separator.1)
    (first last :
      Fin
        (InteriorRankData.node separator
          children hchildren data).ranks.length)
    (horder : first.1 < last.1)
    (hfirstSeparator :
      (InteriorRankData.node separator
        children hchildren data).ranks[first.1] =
          separator)
    (hlastSeparator :
      (InteriorRankData.node separator
        children hchildren data).ranks[last.1] =
          separator) :
    ∃ before middle after,
      children = before ++ middle ++ after ∧
      before ≠ [] ∧ middle ≠ [] ∧ after ≠ [] ∧
      first.1 + 1 =
        (FactorTree.forestYield before).length ∧
      last.1 + 1 =
        (FactorTree.forestYield
          (before ++ middle)).length := by
  obtain ⟨firstBefore, firstAfter,
      hfirstDecomp, hfirstBefore,
      hfirstAfter, hfirstOffset⟩ :=
    node_separator_cut_decomposition
      separator children hchildren data hbelow
      first hfirstSeparator
  obtain ⟨lastBefore, lastAfter,
      hlastDecomp, hlastBefore,
      hlastAfter, hlastOffset⟩ :=
    node_separator_cut_decomposition
      separator children hchildren data hbelow
      last hlastSeparator
  have hfirstPrefix :
      firstBefore <+: children :=
    ⟨firstAfter, hfirstDecomp.symm⟩
  have hlastPrefix :
      lastBefore <+: children :=
    ⟨lastAfter, hlastDecomp.symm⟩
  have hweightLt :
      (firstBefore.map
          (fun tree => tree.yield.length)).sum <
        (lastBefore.map
          (fun tree => tree.yield.length)).sum := by
    rw [← forestYield_length,
      ← forestYield_length]
    omega
  obtain ⟨middle, hmiddle,
      hmiddleNonempty⟩ :=
    prefix_split_of_weight_lt
      (fun tree : FactorTree α =>
        tree.yield.length)
      hfirstPrefix hlastPrefix hweightLt
  refine ⟨firstBefore, middle, lastAfter,
    ?_, hfirstBefore, hmiddleNonempty,
    hlastAfter, hfirstOffset, ?_⟩
  · rw [hmiddle] at hlastDecomp
    simpa only [List.append_assoc]
      using hlastDecomp
  · rw [← hmiddle]
    exact hlastOffset

theorem node_middleFactor_between_separators
    {height : Nat}
    (separator : Fin height)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData (Fin height) child)
    (hbelow :
      ∀ child (hchild : child ∈ children),
        ∀ rank ∈ (data child hchild).ranks,
          rank.1 < separator.1)
    (first last :
      Fin
        (InteriorRankData.node separator
          children hchildren data).ranks.length)
    (horder : first.1 < last.1)
    (hfirstSeparator :
      (InteriorRankData.node separator
        children hchildren data).ranks[first.1] =
          separator)
    (hlastSeparator :
      (InteriorRankData.node separator
        children hchildren data).ranks[last.1] =
          separator) :
    ∃ middle : List (FactorTree α),
      middle ≠ [] ∧
      (∀ child ∈ middle, child ∈ children) ∧
      ControlMonoid.middleFactor
          (FactorTree.node children).yield
          (first.1 + 1) (last.1 + 1) =
        FactorTree.forestYield middle := by
  obtain ⟨before, middle, after,
      hdecomp, hbefore, hmiddle, hafter,
      hfirstOffset, hlastOffset⟩ :=
    node_two_separator_cut_decomposition
      separator children hchildren data hbelow
      first last horder hfirstSeparator
      hlastSeparator
  refine ⟨middle, hmiddle, (by
    intro child hchild
    rw [hdecomp]
    simp [hchild]), ?_⟩
  have hyield :
      FactorTree.forestYield
          (before ++ middle ++ after) =
        FactorTree.forestYield before ++
          FactorTree.forestYield middle ++
            FactorTree.forestYield after := by
    simp [FactorTree.forestYield,
      List.flatMap_append]
  have happendLength :
      (FactorTree.forestYield
        (before ++ middle)).length =
      (FactorTree.forestYield before).length +
        (FactorTree.forestYield middle).length := by
    simp [FactorTree.forestYield,
      List.flatMap_append]
  calc
    ControlMonoid.middleFactor
        (FactorTree.node children).yield
        (first.1 + 1) (last.1 + 1) =
      ControlMonoid.middleFactor
        (FactorTree.forestYield
          (before ++ middle ++ after))
        (first.1 + 1) (last.1 + 1) := by
          apply congrArg
            (fun word =>
              ControlMonoid.middleFactor word
                (first.1 + 1) (last.1 + 1))
          rw [FactorTree.yield_node]
          exact congrArg FactorTree.forestYield
            hdecomp
    _ = ControlMonoid.middleFactor
        (FactorTree.forestYield before ++
          FactorTree.forestYield middle ++
            FactorTree.forestYield after)
        (FactorTree.forestYield before).length
        ((FactorTree.forestYield before).length +
          (FactorTree.forestYield middle).length) := by
            rw [hyield, hfirstOffset,
              hlastOffset, happendLength]
    _ = FactorTree.forestYield middle :=
      middleFactor_append_three
        (FactorTree.forestYield before)
        (FactorTree.forestYield middle)
        (FactorTree.forestYield after)

theorem node_eval_between_separators
    {height : Nat}
    (C : ControlMonoid M) (letter : α → M)
    (separator : Fin height)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData (Fin height) child)
    (hbelow :
      ∀ child (hchild : child ∈ children),
        ∀ rank ∈ (data child hchild).ranks,
          rank.1 < separator.1)
    (e : M)
    (he : C.Idempotent e)
    (hcontrols :
      ∀ child ∈ children,
        child.control C letter = e)
    (first last :
      Fin
        (InteriorRankData.node separator
          children hchildren data).ranks.length)
    (horder : first.1 < last.1)
    (hfirstSeparator :
      (InteriorRankData.node separator
        children hchildren data).ranks[first.1] =
          separator)
    (hlastSeparator :
      (InteriorRankData.node separator
        children hchildren data).ranks[last.1] =
          separator) :
    C.eval letter
        (ControlMonoid.middleFactor
          (FactorTree.node children).yield
          (first.1 + 1) (last.1 + 1)) =
      e := by
  obtain ⟨middle, hmiddle, hmiddleChildren,
      hmiddleFactor⟩ :=
    node_middleFactor_between_separators
      separator children hchildren data hbelow
      first last horder hfirstSeparator
      hlastSeparator
  rw [hmiddleFactor]
  apply FactorTree.eval_forestYield_eq_idempotent
    C letter he
  · intro child hchild
    exact hcontrols child
      (hmiddleChildren child hchild)
  · exact hmiddle

def NeighborEvalSound
    {height : Nat}
    (C : ControlMonoid M) (letter : α → M)
    (decode : Fin height → M)
    {tree : FactorTree α}
    (data : InteriorRankData (Fin height) tree) : Prop :=
  ∀ first last : Fin data.ranks.length,
    listLevelNeighbors data.ranks first last →
    C.eval letter
        (ControlMonoid.middleFactor tree.yield
          (first.1 + 1) (last.1 + 1)) =
      decode data.ranks[first.1]

theorem leaf_neighborEvalSound
    {height : Nat}
    (C : ControlMonoid M) (letter : α → M)
    (decode : Fin height → M)
    (value : α) :
    (InteriorRankData.leaf
      (Fin height) value).NeighborEvalSound
        C letter decode := by
  intro first
  exact Fin.elim0 first

theorem binary_neighborEvalSound
    {height : Nat}
    (C : ControlMonoid M) (letter : α → M)
    (decode : Fin height → M)
    (separator : Fin height)
    {left right : FactorTree α}
    (leftData :
      InteriorRankData (Fin height) left)
    (rightData :
      InteriorRankData (Fin height) right)
    (hleftBelow :
      ∀ rank ∈ leftData.ranks,
        rank.1 < separator.1)
    (hrightBelow :
      ∀ rank ∈ rightData.ranks,
        rank.1 < separator.1)
    (hleftSound :
      leftData.NeighborEvalSound
        C letter decode)
    (hrightSound :
      rightData.NeighborEvalSound
        C letter decode) :
    (InteriorRankData.binary separator
      leftData rightData).NeighborEvalSound
        C letter decode := by
  intro first last hneighbors
  rcases binary_listLevelNeighbors_cases
      separator leftData rightData
      hleftBelow hrightBelow hneighbors with
    hleft | hright
  · obtain ⟨localFirst, localLast,
      hfirst, hlast, hlocal⟩ := hleft
    rw [binary_left_middleFactor_eq
      separator leftData rightData
      first last localFirst localLast
      hfirst hlast
      (Nat.le_of_lt hlocal.1)]
    rw [hleftSound localFirst localLast hlocal]
    apply congrArg decode
    symm
    calc
      (InteriorRankData.binary separator
          leftData rightData).ranks[first.1] =
        leftData.ranks[first.1] := by
          exact List.getElem_append_left
            (by
              have hbound := localFirst.2
              omega)
      _ = leftData.ranks[localFirst.1] := by
        exact getElem_congr rfl hfirst.symm
          (by
            have hbound := localFirst.2
            omega)
  · obtain ⟨localFirst, localLast,
      hfirst, hlast, hlocal⟩ := hright
    rw [binary_right_middleFactor_eq
      separator leftData rightData
      first last localFirst localLast
      hfirst hlast
      (Nat.le_of_lt hlocal.1)]
    rw [hrightSound localFirst localLast hlocal]
    apply congrArg decode
    symm
    exact getElem_after_head_separator
      leftData.ranks rightData.ranks
      separator first localFirst hfirst

theorem node_neighborEvalSound
    {height : Nat}
    (C : ControlMonoid M) (letter : α → M)
    (decode : Fin height → M)
    (separator : Fin height)
    (children : List (FactorTree α))
    (hchildren : children ≠ [])
    (data :
      ∀ child ∈ children,
        InteriorRankData (Fin height) child)
    (hbelow :
      ∀ child (hchild : child ∈ children),
        ∀ rank ∈ (data child hchild).ranks,
          rank.1 < separator.1)
    (hsound :
      ∀ child (hchild : child ∈ children),
        (data child hchild).NeighborEvalSound
          C letter decode)
    (hseparatorEval :
      ∀ first last :
          Fin
            (InteriorRankData.node separator
              children hchildren data).ranks.length,
        first.1 < last.1 →
        (InteriorRankData.node separator
          children hchildren data).ranks[first.1] =
            separator →
        (InteriorRankData.node separator
          children hchildren data).ranks[last.1] =
            separator →
        C.eval letter
            (ControlMonoid.middleFactor
              (FactorTree.node children).yield
              (first.1 + 1) (last.1 + 1)) =
          decode separator) :
    (InteriorRankData.node separator
      children hchildren data).NeighborEvalSound
        C letter decode := by
  intro first last hneighbors
  rcases node_listLevelNeighbors_located_cases
      separator children hchildren data hbelow
      hneighbors with
    hseparator | hchildCase
  · have hlastSeparator :
        (InteriorRankData.node separator
          children hchildren data).ranks[last.1] =
            separator := by
      rw [← hneighbors.2.1]
      exact hseparator
    rw [hseparatorEval first last hneighbors.1
      hseparator hlastSeparator]
    exact congrArg decode hseparator.symm
  · obtain ⟨before, child, after, hchild,
      hdecomp, localFirst, localLast,
      hfirst, hlast, hlocal,
      hfirstRank, hlastRank⟩ := hchildCase
    rw [node_middleFactor_eq_child_middleFactor
      separator children hchildren data
      before child after hchild hdecomp
      first last localFirst localLast
      hfirst hlast (Nat.le_of_lt hlocal.1)]
    rw [hsound child hchild
      localFirst localLast hlocal]
    exact congrArg decode hfirstRank.symm

def fullRanks
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (left right : ρ) : List ρ :=
  left :: (data.ranks ++ [right])

theorem fullRanks_length
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (left right : ρ) :
    (data.fullRanks left right).length =
      tree.yield.length + 1 := by
  simp [fullRanks]
  have haligned := data.aligned
  omega

def rankAtCut
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (left right : ρ)
    (cut : WordCut tree.yield) : ρ :=
  (data.fullRanks left right)[cut.1]'(by
    rw [data.fullRanks_length left right]
    exact cut.2)

@[simp] theorem rankAtCut_start
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (left right : ρ) :
    data.rankAtCut left right
        ⟨0, by omega⟩ =
      left := by
  simp [rankAtCut, fullRanks]

theorem rankAtCut_endIndex
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (left right : ρ) :
    data.rankAtCut left right
        ⟨data.ranks.length + 1, by
          have haligned := data.aligned
          omega⟩ =
      right := by
  unfold rankAtCut fullRanks
  simp only [List.getElem_cons_succ]
  exact List.getElem_concat_length rfl _

@[simp] theorem rankAtCut_end
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (left right : ρ) :
    data.rankAtCut left right
        ⟨tree.yield.length, by omega⟩ =
      right := by
  have hcut :
      (⟨tree.yield.length, by omega⟩ :
          WordCut tree.yield) =
        ⟨data.ranks.length + 1, by
          have haligned := data.aligned
          omega⟩ := by
    apply Fin.ext
    exact data.aligned.symm
  rw [hcut]
  exact data.rankAtCut_endIndex left right

theorem rankAtCut_mem_interior
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (left right : ρ)
    (cut : WordCut tree.yield)
    (hpositive : 0 < cut.1)
    (hstrict : cut.1 < tree.yield.length) :
    data.rankAtCut left right cut ∈ data.ranks := by
  let index := cut.1 - 1
  have hindex : index < data.ranks.length := by
    have haligned := data.aligned
    omega
  have hcutValue : index + 1 = cut.1 := by
    dsimp [index]
    omega
  have hcut :
      cut =
        ⟨index + 1, by
          have haligned := data.aligned
          omega⟩ := by
    apply Fin.ext
    exact hcutValue.symm
  rw [hcut]
  unfold rankAtCut fullRanks
  simp only [List.getElem_cons_succ]
  rw [List.getElem_append_left hindex]
  exact List.getElem_mem hindex

def interiorIndex
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (cut : WordCut tree.yield)
    (hpositive : 0 < cut.1)
    (hstrict : cut.1 < tree.yield.length) :
    Fin data.ranks.length :=
  ⟨cut.1 - 1, by
    have haligned := data.aligned
    omega⟩

@[simp] theorem interiorIndex_val
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (cut : WordCut tree.yield)
    (hpositive : 0 < cut.1)
    (hstrict : cut.1 < tree.yield.length) :
    (data.interiorIndex cut hpositive hstrict).1 =
      cut.1 - 1 :=
  rfl

theorem rankAtCut_eq_interiorIndex
    {tree : FactorTree α}
    (data : InteriorRankData ρ tree)
    (left right : ρ)
    (cut : WordCut tree.yield)
    (hpositive : 0 < cut.1)
    (hstrict : cut.1 < tree.yield.length) :
    data.rankAtCut left right cut =
      data.ranks[
        (data.interiorIndex cut hpositive hstrict).1] := by
  let index := data.interiorIndex cut hpositive hstrict
  have hcutValue : index.1 + 1 = cut.1 := by
    simp only [index, interiorIndex_val]
    omega
  have hcut :
      cut =
        ⟨index.1 + 1, by
          have haligned := data.aligned
          omega⟩ := by
    apply Fin.ext
    exact hcutValue.symm
  change data.rankAtCut left right cut =
    data.ranks[index.1]
  rw [hcut]
  unfold rankAtCut fullRanks
  simp only [List.getElem_cons_succ]
  rw [List.getElem_append_left index.2]

theorem listLevelNeighbors_of_levelNeighbors
    {height : Nat}
    {tree : FactorTree α}
    (data : InteriorRankData (Fin height) tree)
    (outerLeft outerRight : Fin height)
    {left right : WordCut tree.yield}
    (hneighbors :
      levelNeighbors
        (data.rankAtCut outerLeft outerRight)
        left right)
    (hleftPositive : 0 < left.1)
    (hleftStrict : left.1 < tree.yield.length)
    (hrightPositive : 0 < right.1)
    (hrightStrict : right.1 < tree.yield.length) :
    listLevelNeighbors data.ranks
      (data.interiorIndex left hleftPositive
        hleftStrict)
      (data.interiorIndex right hrightPositive
        hrightStrict) := by
  have horder := hneighbors.1
  let leftIndex :=
    data.interiorIndex left hleftPositive hleftStrict
  let rightIndex :=
    data.interiorIndex right hrightPositive hrightStrict
  have hleftRank :=
    data.rankAtCut_eq_interiorIndex
      outerLeft outerRight left hleftPositive hleftStrict
  have hrightRank :=
    data.rankAtCut_eq_interiorIndex
      outerLeft outerRight right hrightPositive hrightStrict
  refine ⟨?_, ?_, ?_⟩
  · simp only [leftIndex, rightIndex, interiorIndex_val]
    omega
  · rw [← hleftRank, ← hrightRank]
    exact hneighbors.2.1
  · intro middle hleftMiddle hmiddleRight
    let middleCut : WordCut tree.yield :=
      ⟨middle.1 + 1, by
        have haligned := data.aligned
        have hmiddleBound := middle.2
        omega⟩
    have hmiddlePositive : 0 < middleCut.1 := by
      simp only [middleCut]
      omega
    have hmiddleStrict :
        middleCut.1 < tree.yield.length := by
      simp only [middleCut]
      have haligned := data.aligned
      have hmiddleBound := middle.2
      omega
    have hleftCut : left.1 < middleCut.1 := by
      simp only [middleCut, leftIndex, interiorIndex_val]
        at hleftMiddle ⊢
      omega
    have hcutRight : middleCut.1 < right.1 := by
      simp only [middleCut, rightIndex, interiorIndex_val]
        at hmiddleRight ⊢
      omega
    have hmiddleRank :=
      data.rankAtCut_eq_interiorIndex
        outerLeft outerRight middleCut
        hmiddlePositive hmiddleStrict
    have hmiddleIndex :
        data.interiorIndex middleCut
            hmiddlePositive hmiddleStrict =
          middle := by
      apply Fin.ext
      simp only [middleCut, interiorIndex_val]
      omega
    rw [hmiddleIndex] at hmiddleRank
    rw [← hmiddleRank, ← hleftRank]
    exact hneighbors.2.2 middleCut hleftCut hcutRight

end InteriorRankData

end NSSE
