import NSSE.AdjacentCutIntervals

/-!
# Forests outside the span of the top-ranked cuts

Before the first top cut and after the last top cut there are no further
top-ranked cuts.  Removing the one boundary letter therefore leaves an
interval whose split height can be lowered.
-/

namespace NSSE

universe u v

namespace RamseyanSplit

theorem rank_lt_top_of_before_first
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (first : WordCut word)
    (rest : List (WordCut word))
    (hcuts : split.topCuts = first :: rest)
    (cut : WordCut word)
    (hbefore : cut.1 < first.1) :
    (split.rank cut).1 < height := by
  have hbound := (split.rank cut).2
  have hnotTop :
      (split.rank cut).1 ≠ height := by
    intro htop
    have hmem :
        cut ∈ first :: rest := by
      rw [← hcuts]
      exact (split.mem_topCuts_iff cut).2 htop
    simp only [List.mem_cons] at hmem
    rcases hmem with heq | hrest
    · subst cut
      exact Nat.lt_irrefl _ hbefore
    · have hpair := split.topCuts_pairwise_lt
      rw [hcuts, List.pairwise_cons] at hpair
      have hfirstCut := hpair.1 cut hrest
      exact (Nat.not_lt_of_ge
        (Nat.le_of_lt hbefore)) hfirstCut
  omega

def startCut (word : Word α) : WordCut word :=
  ⟨0, by omega⟩

def prefixCoreRight
    {word : Word α} (first : WordCut word)
    (hpositive : 0 < first.1) :
    WordCut word :=
  ⟨first.1 - 1, by
    have hfirst := first.val_le_length
    omega⟩

def prefixCoreSplit
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (first : WordCut word)
    (rest : List (WordCut word))
    (hcuts : split.topCuts = first :: rest)
    (hpositive : 0 < first.1) :
    RamseyanSplit C letter
      (WordCut.interval word (startCut word)
        (prefixCoreRight first hpositive))
      height := by
  let left := startCut word
  let right := prefixCoreRight first hpositive
  have hle : left.1 ≤ right.1 := by
    simp [left, right, startCut, prefixCoreRight]
  apply split.restrictBelowTop left right hle
  intro cut
  let embedded :=
    WordCut.intoInterval word left right hle cut
  have hembeddedLe :
      embedded.1 ≤ right.1 := by
    have hlength :
        (WordCut.interval word left right).length =
          right.1 - left.1 :=
      ControlMonoid.middleFactor_length word hle
        right.val_le_length
    have hcut := cut.2
    have hcutLe :
        cut.1 ≤ right.1 - left.1 := by
      omega
    simp only [embedded, WordCut.intoInterval_val]
    omega
  have hbefore : embedded.1 < first.1 := by
    simp only [right, prefixCoreRight] at hembeddedLe
    omega
  exact split.rank_lt_top_of_before_first
    first rest hcuts embedded hbefore

theorem prefix_decomposition
    {word : Word α}
    (first : WordCut word)
    (hpositive : 0 < first.1) :
    WordCut.interval word (startCut word)
          (prefixCoreRight first hpositive) ++
        [word[first.1 - 1]] =
      WordCut.interval word (startCut word) first := by
  let coreRight := prefixCoreRight first hpositive
  have hcoreFirst : coreRight.1 ≤ first.1 := by
    simp [coreRight, prefixCoreRight]
  have hlast :
      WordCut.interval word coreRight first =
        [word[first.1 - 1]] := by
    have hlastBound :
        first.1 - 1 < word.length := by
      have hfirst := first.val_le_length
      omega
    have hsucc :
        first.1 - 1 + 1 = first.1 := by
      omega
    simpa [coreRight, prefixCoreRight, hsucc] using
      WordCut.interval_succ_eq_singleton
        word (first.1 - 1) hlastBound
  rw [← hlast]
  exact WordCut.interval_append word
    (startCut word) coreRight first
    (by simp [startCut]) hcoreFirst

noncomputable def prefixForest
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height bound : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (first : WordCut word)
    (rest : List (WordCut word))
    (hcuts : split.topCuts = first :: rest)
    (hpositive : 0 < first.1)
    (lowerForest :
      ∀ {lowerWord : Word α},
        RamseyanSplit C letter lowerWord height →
        lowerWord ≠ [] →
        FactorTree.HeightBoundedForest
          C letter lowerWord bound) :
    FactorTree.HeightBoundedForest C letter
      (WordCut.interval word (startCut word) first)
      (bound + 1) := by
  by_cases hlong : 1 < first.1
  · let coreSplit :=
      split.prefixCoreSplit first rest hcuts hpositive
    have hcoreNonempty :
        WordCut.interval word (startCut word)
          (prefixCoreRight first hpositive) ≠ [] := by
      apply WordCut.interval_ne_nil
      simp [startCut, prefixCoreRight]
      omega
    let core := lowerForest coreSplit hcoreNonempty
    let last :=
      FactorTree.HeightBoundedForest.singleton
        C letter word[first.1 - 1] bound
    let joined :=
      FactorTree.HeightBoundedForest.binary core last
    exact joined.rewriteWord
      (WordCut.interval word (startCut word) first)
      (prefix_decomposition first hpositive)
  · have hprefixNonempty :
        WordCut.interval word (startCut word) first ≠ [] :=
      WordCut.interval_ne_nil word (by
        simp [startCut]
        exact hpositive)
    let tree :=
      FactorTree.binaryOfWord
        (WordCut.interval word (startCut word) first)
        hprefixNonempty
    exact {
      tree := tree
      isForest :=
        FactorTree.binaryOfWord_isForest
          C letter _ hprefixNonempty
      yield_eq :=
        FactorTree.binaryOfWord_yield _
          hprefixNonempty
      height_le := by
        have hheight :=
          FactorTree.binaryOfWord_height_lt_length
            _ hprefixNonempty
        have hlength :
            (WordCut.interval word
              (startCut word) first).length =
              first.1 :=
          ControlMonoid.middleFactor_length word
            (by simp [startCut])
            first.val_le_length
        dsimp [tree]
        rw [hlength] at hheight
        omega
    }

private theorem val_lt_last_of_mem_before
    {word : Word α}
    (last cut : WordCut word) :
    ∀ before : List (WordCut word),
      (before ++ [last]).Pairwise
        (fun first second => first.1 < second.1) →
      cut ∈ before →
      cut.1 < last.1 := by
  intro before
  induction before with
  | nil =>
      intro _ hmem
      simp at hmem
  | cons head tail ih =>
      intro hpair hmem
      simp only [List.cons_append] at hpair
      rw [List.pairwise_cons] at hpair
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact hpair.1 last (by simp)
      · exact ih hpair.2 htail

theorem rank_lt_top_of_after_last
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (before : List (WordCut word))
    (last : WordCut word)
    (hcuts : split.topCuts = before ++ [last])
    (cut : WordCut word)
    (hafter : last.1 < cut.1) :
    (split.rank cut).1 < height := by
  have hbound := (split.rank cut).2
  have hnotTop :
      (split.rank cut).1 ≠ height := by
    intro htop
    have hmem :
        cut ∈ before ++ [last] := by
      rw [← hcuts]
      exact (split.mem_topCuts_iff cut).2 htop
    rw [List.mem_append] at hmem
    rcases hmem with hbefore | hlast
    · have hpair : (before ++ [last]).Pairwise
          (fun first second => first.1 < second.1) := by
        rw [← hcuts]
        exact split.topCuts_pairwise_lt
      have hcutLast :=
        val_lt_last_of_mem_before
          last cut before hpair hbefore
      exact (Nat.not_lt_of_ge
        (Nat.le_of_lt hafter)) hcutLast
    · simp only [List.mem_singleton] at hlast
      subst cut
      exact Nat.lt_irrefl _ hafter
  omega

def endCut (word : Word α) : WordCut word :=
  ⟨word.length, by omega⟩

def suffixCoreLeft
    {word : Word α} (last : WordCut word)
    (hbeforeEnd : last.1 < word.length) :
    WordCut word :=
  ⟨last.1 + 1, by omega⟩

def suffixCoreSplit
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (before : List (WordCut word))
    (last : WordCut word)
    (hcuts : split.topCuts = before ++ [last])
    (hbeforeEnd : last.1 < word.length) :
    RamseyanSplit C letter
      (WordCut.interval word
        (suffixCoreLeft last hbeforeEnd)
        (endCut word))
      height := by
  let left := suffixCoreLeft last hbeforeEnd
  let right := endCut word
  have hle : left.1 ≤ right.1 := by
    change last.1 + 1 ≤ word.length
    omega
  apply split.restrictBelowTop left right hle
  intro cut
  let embedded :=
    WordCut.intoInterval word left right hle cut
  have hafter : last.1 < embedded.1 := by
    simp only [embedded, WordCut.intoInterval_val,
      left, suffixCoreLeft]
    omega
  exact split.rank_lt_top_of_after_last
    before last hcuts embedded hafter

theorem suffix_decomposition
    {word : Word α}
    (last : WordCut word)
    (hbeforeEnd : last.1 < word.length) :
    [word[last.1]] ++
        WordCut.interval word
          (suffixCoreLeft last hbeforeEnd)
          (endCut word) =
      WordCut.interval word last (endCut word) := by
  let coreLeft := suffixCoreLeft last hbeforeEnd
  have hlastCore : last.1 ≤ coreLeft.1 := by
    simp [coreLeft, suffixCoreLeft]
  have hfirst :
      WordCut.interval word last coreLeft =
        [word[last.1]] := by
    simpa [coreLeft, suffixCoreLeft] using
      WordCut.interval_succ_eq_singleton
        word last.1 hbeforeEnd
  rw [← hfirst]
  exact WordCut.interval_append word
    last coreLeft (endCut word)
    hlastCore (by
      change last.1 + 1 ≤ word.length
      omega)

noncomputable def suffixForest
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height bound : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (before : List (WordCut word))
    (last : WordCut word)
    (hcuts : split.topCuts = before ++ [last])
    (hbeforeEnd : last.1 < word.length)
    (lowerForest :
      ∀ {lowerWord : Word α},
        RamseyanSplit C letter lowerWord height →
        lowerWord ≠ [] →
        FactorTree.HeightBoundedForest
          C letter lowerWord bound) :
    FactorTree.HeightBoundedForest C letter
      (WordCut.interval word last (endCut word))
      (bound + 1) := by
  by_cases hlong : last.1 + 1 < word.length
  · let coreSplit :=
      split.suffixCoreSplit before last hcuts hbeforeEnd
    have hcoreNonempty :
        WordCut.interval word
          (suffixCoreLeft last hbeforeEnd)
          (endCut word) ≠ [] := by
      apply WordCut.interval_ne_nil
      simp [suffixCoreLeft, endCut]
      exact hlong
    let core := lowerForest coreSplit hcoreNonempty
    let first :=
      FactorTree.HeightBoundedForest.singleton
        C letter word[last.1] bound
    let joined :=
      FactorTree.HeightBoundedForest.binary first core
    exact joined.rewriteWord
      (WordCut.interval word last (endCut word))
      (suffix_decomposition last hbeforeEnd)
  · have hsuffixNonempty :
        WordCut.interval word last (endCut word) ≠ [] :=
      WordCut.interval_ne_nil word (by
        simp [endCut]
        exact hbeforeEnd)
    let tree :=
      FactorTree.binaryOfWord
        (WordCut.interval word last (endCut word))
        hsuffixNonempty
    exact {
      tree := tree
      isForest :=
        FactorTree.binaryOfWord_isForest
          C letter _ hsuffixNonempty
      yield_eq :=
        FactorTree.binaryOfWord_yield _
          hsuffixNonempty
      height_le := by
        have hheight :=
          FactorTree.binaryOfWord_height_lt_length
            _ hsuffixNonempty
        have hlength :
            (WordCut.interval word last
              (endCut word)).length =
              word.length - last.1 :=
          ControlMonoid.middleFactor_length word
            (by
              simp [endCut]
              exact last.val_le_length)
            (by simp [endCut])
        dsimp [tree]
        rw [hlength] at hheight
        omega
    }

theorem topSpan_decomposition
    {word : Word α}
    (first last : WordCut word)
    (hfirstLast : first.1 ≤ last.1) :
    WordCut.interval word (startCut word) first ++
        WordCut.interval word first last ++
        WordCut.interval word last (endCut word) =
      word := by
  rw [WordCut.interval_append word
    (startCut word) first last
    (by simp [startCut]) hfirstLast]
  rw [WordCut.interval_append word
    (startCut word) last (endCut word)
    (by simp [startCut])
    (by simp [endCut]; exact last.val_le_length)]
  simp [WordCut.interval, ControlMonoid.middleFactor,
    startCut, endCut]

noncomputable def wholeForest_of_two_topCuts
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height bound : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (first second : WordCut word)
    (rest : List (WordCut word))
    (hcuts :
      split.topCuts = first :: second :: rest)
    (lowerForest :
      ∀ {lowerWord : Word α},
        RamseyanSplit C letter lowerWord height →
        lowerWord ≠ [] →
        FactorTree.HeightBoundedForest
          C letter lowerWord bound) :
    FactorTree.HeightBoundedForest C letter word
      (bound + 5) := by
  let tail := second :: rest
  let last := tail.getLast (by simp)
  let beforeLast := first :: tail.dropLast
  have hlastCuts :
      split.topCuts = beforeLast ++ [last] := by
    rw [hcuts]
    have htail :
        tail.dropLast ++
            [tail.getLast (by simp)] =
          tail :=
      List.dropLast_concat_getLast (by simp)
    change first :: tail =
      first :: (tail.dropLast ++
        [tail.getLast (by simp)])
    rw [htail]
  have hfirstLast : first.1 ≤ last.1 := by
    have hpair := split.topCuts_pairwise_lt
    rw [hcuts, List.pairwise_cons] at hpair
    exact Nat.le_of_lt
      (hpair.1 last (by
        simp only [last, tail]
        exact List.getLast_mem (by simp)))
  let span :=
    split.topSpanForest first second rest
      hcuts lowerForest
  apply FactorTree.HeightBoundedForest.surround
    (bound := bound + 3)
    (beforeWord :=
      WordCut.interval word (startCut word) first)
    (middleWord :=
      WordCut.interval word first last)
    (afterWord :=
      WordCut.interval word last (endCut word))
    (wholeWord := word)
    span
  · intro hprefix
    have hpositive : 0 < first.1 := by
      by_cases hzero : first.1 = 0
      · exact False.elim (hprefix (by
          simp [WordCut.interval,
            ControlMonoid.middleFactor,
            startCut, hzero]))
      · omega
    exact
      (split.prefixForest first tail hcuts
        hpositive lowerForest).weaken
          (bound + 3) (by omega)
  · intro hsuffix
    have hbeforeEnd : last.1 < word.length := by
      by_cases hend : last.1 = word.length
      · exact False.elim (hsuffix (by
          simp [WordCut.interval,
            ControlMonoid.middleFactor,
            endCut, hend]))
      · have hlastBound := last.val_le_length
        omega
    exact
      (split.suffixForest beforeLast last
        hlastCuts hbeforeEnd lowerForest).weaken
          (bound + 3) (by omega)
  · exact topSpan_decomposition
      first last hfirstLast

noncomputable def wholeForest_of_one_topCut
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height bound : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (only : WordCut word)
    (hcuts : split.topCuts = [only])
    (hword : word ≠ [])
    (lowerForest :
      ∀ {lowerWord : Word α},
        RamseyanSplit C letter lowerWord height →
        lowerWord ≠ [] →
        FactorTree.HeightBoundedForest
          C letter lowerWord bound) :
    FactorTree.HeightBoundedForest C letter word
      (bound + 2) := by
  have hlengthPositive : 0 < word.length :=
    List.length_pos_iff.mpr hword
  by_cases hstart : only.1 = 0
  · have hbeforeEnd : only.1 < word.length := by
      omega
    let suffix :=
      split.suffixForest [] only hcuts
        hbeforeEnd lowerForest
    apply suffix.weaken (bound + 2) (by omega) |>.rewriteWord
      word
    simp [WordCut.interval,
      ControlMonoid.middleFactor,
      endCut, hstart]
  · by_cases hend : only.1 = word.length
    · have hpositive : 0 < only.1 := by
        omega
      let prefixBuilt :=
        split.prefixForest only [] hcuts
          hpositive lowerForest
      apply prefixBuilt.weaken (bound + 2) (by omega) |>.rewriteWord
        word
      simp [WordCut.interval,
        ControlMonoid.middleFactor,
        startCut, hend]
    · have hpositive : 0 < only.1 := by
        omega
      have hbeforeEnd : only.1 < word.length := by
        have hbound := only.val_le_length
        omega
      let prefixBuilt :=
        split.prefixForest only [] hcuts
          hpositive lowerForest
      let suffixBuilt :=
        split.suffixForest [] only hcuts
          hbeforeEnd lowerForest
      let joined :=
        FactorTree.HeightBoundedForest.binary
          prefixBuilt suffixBuilt
      apply joined.rewriteWord word
      rw [WordCut.interval_append word
        (startCut word) only (endCut word)
        (by simp [startCut])
        (by simp [endCut]; exact only.val_le_length)]
      simp [WordCut.interval,
        ControlMonoid.middleFactor,
        startCut, endCut]

end RamseyanSplit

end NSSE
