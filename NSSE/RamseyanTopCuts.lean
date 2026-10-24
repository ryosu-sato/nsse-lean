import NSSE.RamseyanSplit

/-!
# Ordered enumeration of the top-ranked cuts

The conversion from a Ramseyan split to a factorization forest decomposes a
word at the cuts carrying the greatest used rank.  This file provides their
finite, complete, strictly ordered enumeration.
-/

namespace NSSE

universe u v

namespace WordCut

def all (word : Word α) : List (WordCut word) :=
  List.ofFn id

theorem mem_all
    (word : Word α) (cut : WordCut word) :
    cut ∈ all word := by
  rw [all, List.mem_ofFn]
  exact ⟨cut, rfl⟩

theorem all_pairwise_lt
    (word : Word α) :
    (all word).Pairwise
      (fun left right => left.1 < right.1) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [all, List.length_ofFn] at hi hj
  simp only [all, List.getElem_ofFn]
  exact hij

end WordCut

namespace RamseyanSplit

private theorem nodup_of_pairwise_val_lt
    {word : Word α} :
    ∀ cuts : List (WordCut word),
      cuts.Pairwise
          (fun left right => left.1 < right.1) →
        cuts.Nodup := by
  intro cuts hpair
  induction cuts with
  | nil =>
      exact .nil
  | cons head tail ih =>
      rw [List.pairwise_cons] at hpair
      exact .cons
        (by
          intro other hmem heq
          subst other
          have hlt := hpair.1 head hmem
          exact Nat.lt_irrefl _ hlt)
        (ih hpair.2)

private theorem no_member_strictly_between_adjacent
    {word : Word α}
    (left right middle : WordCut word) :
    ∀ before after : List (WordCut word),
      (before ++ left :: right :: after).Pairwise
        (fun first second => first.1 < second.1) →
      middle ∈ before ++ left :: right :: after →
      ¬(left.1 < middle.1 ∧
        middle.1 < right.1) := by
  intro before
  induction before with
  | nil =>
      intro after hpair hmem hbetween
      simp only [List.nil_append, List.mem_cons] at hmem
      simp only [List.nil_append] at hpair
      rw [List.pairwise_cons] at hpair
      rw [List.pairwise_cons] at hpair
      rcases hmem with rfl | rfl | hafter
      · exact Nat.lt_irrefl _ hbetween.1
      · exact Nat.lt_irrefl _ hbetween.2
      · have hrightMiddle :=
          hpair.2.1 middle hafter
        exact (Nat.not_lt_of_ge
          (Nat.le_of_lt hrightMiddle)) hbetween.2
  | cons head tail ih =>
      intro after hpair hmem hbetween
      simp only [List.cons_append, List.mem_cons] at hmem
      simp only [List.cons_append] at hpair
      rw [List.pairwise_cons] at hpair
      rcases hmem with rfl | htail
      · have hheadLeft :
            middle.1 < left.1 :=
          hpair.1 left (by simp)
        exact (Nat.not_lt_of_ge
          (Nat.le_of_lt hbetween.1)) hheadLeft
      · exact ih after hpair.2 htail hbetween

private theorem adjacent_lt_of_pairwise
    {word : Word α}
    (left right : WordCut word) :
    ∀ before after : List (WordCut word),
      (before ++ left :: right :: after).Pairwise
        (fun first second => first.1 < second.1) →
      left.1 < right.1 := by
  intro before
  induction before with
  | nil =>
      intro after hpair
      simp only [List.nil_append] at hpair
      rw [List.pairwise_cons] at hpair
      exact hpair.1 right (by simp)
  | cons head tail ih =>
      intro after hpair
      simp only [List.cons_append] at hpair
      rw [List.pairwise_cons] at hpair
      exact ih after hpair.2

def topCuts
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1)) :
    List (WordCut word) :=
  (WordCut.all word).filter
    (fun cut => (split.rank cut).1 == height)

theorem mem_topCuts_iff
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (cut : WordCut word) :
    cut ∈ split.topCuts ↔
      (split.rank cut).1 = height := by
  simp [topCuts, WordCut.mem_all]

theorem topCuts_pairwise_lt
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1)) :
    split.topCuts.Pairwise
      (fun left right => left.1 < right.1) := by
  exact (WordCut.all_pairwise_lt word).filter _

theorem topCuts_nodup
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1)) :
    split.topCuts.Nodup := by
  exact nodup_of_pairwise_val_lt
    split.topCuts split.topCuts_pairwise_lt

theorem topCuts_nonempty_iff
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1)) :
    split.topCuts ≠ [] ↔
      ∃ cut : WordCut word,
        (split.rank cut).1 = height := by
  constructor
  · intro hnonempty
    obtain ⟨cut, hcut⟩ :=
      List.exists_mem_of_ne_nil split.topCuts hnonempty
    exact ⟨cut, (split.mem_topCuts_iff cut).1 hcut⟩
  · rintro ⟨cut, hcut⟩ hempty
    have hmem :=
      (split.mem_topCuts_iff cut).2 hcut
    rw [hempty] at hmem
    exact List.not_mem_nil hmem

theorem topNeighbors_of_adjacent_topCuts
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (before after : List (WordCut word))
    (left right : WordCut word)
    (hcuts :
      split.topCuts =
        before ++ left :: right :: after) :
    split.TopNeighbors left right := by
  have hpair :
      (before ++ left :: right :: after).Pairwise
        (fun first second => first.1 < second.1) := by
    rw [← hcuts]
    exact split.topCuts_pairwise_lt
  have hleftTop :
      (split.rank left).1 = height := by
    apply (split.mem_topCuts_iff left).1
    rw [hcuts]
    simp
  have hrightTop :
      (split.rank right).1 = height := by
    apply (split.mem_topCuts_iff right).1
    rw [hcuts]
    simp
  refine ⟨?_, hleftTop, hrightTop, ?_⟩
  · exact adjacent_lt_of_pairwise
      left right before after hpair
  · intro middle hleft hright
    have hbound := (split.rank middle).2
    have hnotTop :
        (split.rank middle).1 ≠ height := by
      intro htop
      have hmem :
          middle ∈ before ++ left :: right :: after := by
        rw [← hcuts]
        exact (split.mem_topCuts_iff middle).2 htop
      exact no_member_strictly_between_adjacent
        left right middle before after hpair hmem
        ⟨hleft, hright⟩
    omega

theorem adjacent_topCuts_control
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (before after : List (WordCut word))
    (left right : WordCut word)
    (hcuts :
      split.topCuts =
        before ++ left :: right :: after) :
    C.eval letter
        (WordCut.interval word left right) =
      split.idempotentAt
        ⟨height, by omega⟩ := by
  exact split.topNeighbors_control
    (split.topNeighbors_of_adjacent_topCuts
      before after left right hcuts)

def topCoreLeft
    {word : Word α}
    (left right : WordCut word)
    (hwide : left.1 + 2 ≤ right.1) :
    WordCut word :=
  ⟨left.1 + 1, by
    have hright := right.val_le_length
    omega⟩

def topCoreRight
    {word : Word α}
    (left right : WordCut word)
    (hwide : left.1 + 2 ≤ right.1) :
    WordCut word :=
  ⟨right.1 - 1, by
    have hright := right.val_le_length
    omega⟩

theorem topCoreLeft_le_right
    {word : Word α}
    (left right : WordCut word)
    (hwide : left.1 + 2 ≤ right.1) :
    (topCoreLeft left right hwide).1 ≤
      (topCoreRight left right hwide).1 := by
  simp only [topCoreLeft, topCoreRight]
  omega

theorem topCore_interval_length
    {word : Word α}
    (left right : WordCut word)
    (hwide : left.1 + 2 ≤ right.1) :
    (WordCut.interval word
      (topCoreLeft left right hwide)
      (topCoreRight left right hwide)).length =
        right.1 - left.1 - 2 := by
  unfold WordCut.interval
  rw [ControlMonoid.middleFactor_length]
  · simp only [topCoreLeft, topCoreRight]
    omega
  · exact topCoreLeft_le_right left right hwide
  · exact (topCoreRight left right hwide).val_le_length

theorem topCore_interval_ne_nil
    {word : Word α}
    (left right : WordCut word)
    (hwide : left.1 + 3 ≤ right.1) :
    WordCut.interval word
      (topCoreLeft left right (by omega))
      (topCoreRight left right (by omega)) ≠ [] := by
  apply ControlMonoid.middleFactor_ne_nil
  · simp only [topCoreLeft, topCoreRight]
    omega
  · exact
      (topCoreRight left right (by omega)).val_le_length

def topCoreSplit
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    {left right : WordCut word}
    (htop : split.TopNeighbors left right)
    (hwide : left.1 + 2 ≤ right.1) :
    RamseyanSplit C letter
      (WordCut.interval word
        (topCoreLeft left right hwide)
        (topCoreRight left right hwide))
      height := by
  let coreLeft := topCoreLeft left right hwide
  let coreRight := topCoreRight left right hwide
  have hcore :
      coreLeft.1 ≤ coreRight.1 :=
    topCoreLeft_le_right left right hwide
  apply split.restrictBelowTop
    coreLeft coreRight hcore
  intro cut
  let embedded :=
    WordCut.intoInterval
      word coreLeft coreRight hcore cut
  have hleftEmbedded :
      left.1 < embedded.1 := by
    simp only [embedded, WordCut.intoInterval_val,
      coreLeft, topCoreLeft]
    omega
  have hembeddedLe :
      embedded.1 ≤ coreRight.1 := by
    have hlength :
        (WordCut.interval word
          coreLeft coreRight).length =
          coreRight.1 - coreLeft.1 :=
      ControlMonoid.middleFactor_length word hcore
        coreRight.val_le_length
    have hcut := cut.2
    have hcutLe :
        cut.1 ≤ coreRight.1 - coreLeft.1 := by
      omega
    simp only [embedded, WordCut.intoInterval_val]
    omega
  have hrightEmbedded :
      embedded.1 < right.1 := by
    have hcoreRight :
        coreRight.1 = right.1 - 1 := rfl
    omega
  exact htop.2.2.2 embedded
    hleftEmbedded hrightEmbedded

end RamseyanSplit

end NSSE
