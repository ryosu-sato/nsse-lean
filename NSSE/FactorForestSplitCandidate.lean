import NSSE.FactorForestColoredRanks

/-!
# The Ramseyan-split candidate carried by a factor forest

The colored boundary ranks are transported from the tree yield to the word
certified by `HeightBoundedForest.yield_eq`.  Rank construction,
idempotent decoding, and total idempotence are separated from the remaining
neighbor-interval soundness theorem.
-/

namespace NSSE

universe u v

namespace WordCut

def transport
    {source target : Word α}
    (hlength : source.length = target.length) :
    WordCut source → WordCut target :=
  fun cut =>
    ⟨cut.1, by
      have hbound := cut.2
      omega⟩

@[simp] theorem transport_val
    {source target : Word α}
    (hlength : source.length = target.length)
    (cut : WordCut source) :
    (transport hlength cut).1 = cut.1 :=
  rfl

end WordCut

structure FactorForestRamseyanCandidate
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (height : Nat) where
  rank : WordCut word → Fin height
  idempotentAt : Fin height → M
  idempotent :
    ∀ level, C.Idempotent (idempotentAt level)

namespace FactorForestRamseyanCandidate

def toRamseyanSplit
    (candidate :
      FactorForestRamseyanCandidate
        C letter word height)
    (neighbor_control :
      ∀ left right,
        levelNeighbors candidate.rank left right →
        C.eval letter
            (WordCut.interval word left right) =
          candidate.idempotentAt
            (candidate.rank left)) :
    RamseyanSplit C letter word height where
  rank := candidate.rank
  idempotentAt := candidate.idempotentAt
  idempotent := candidate.idempotent
  neighbor_control := neighbor_control

end FactorForestRamseyanCandidate

namespace FactorTree.HeightBoundedForest

def wordToYieldCut
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    WordCut word → WordCut forest.tree.yield :=
  WordCut.transport
    (congrArg List.length forest.yield_eq).symm

@[simp] theorem wordToYieldCut_val
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound)
    (cut : WordCut word) :
    (forest.wordToYieldCut cut).1 = cut.1 :=
  rfl

theorem interval_eq_yield_interval
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound)
    (left right : WordCut word) :
    WordCut.interval word left right =
      WordCut.interval forest.tree.yield
        (forest.wordToYieldCut left)
        (forest.wordToYieldCut right) := by
  change
    ControlMonoid.middleFactor word left.1 right.1 =
      ControlMonoid.middleFactor
        forest.tree.yield left.1 right.1
  exact congrArg
    (fun current =>
      ControlMonoid.middleFactor
        current left.1 right.1)
    forest.yield_eq.symm

noncomputable def ramseyanCandidate
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    FactorForestRamseyanCandidate
      C letter word
      ((bound + 2) * elements.colorWidth) where
  rank := fun cut =>
    forest.coloredRank elements
      (forest.wordToYieldCut cut)
  idempotentAt :=
    C.coloredIdempotentAt elements
  idempotent := by
    intro level
    exact C.coloredIdempotentAt_idempotent
      elements level

@[simp] theorem ramseyanCandidate_rank_start
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    (forest.ramseyanCandidate elements).rank
        ⟨0, by omega⟩ =
      elements.leftMarkerLevel
        (FactorTree.HeightBoundedForest.outerLayer
          bound) := by
  unfold ramseyanCandidate wordToYieldCut
  exact forest.coloredRank_start elements

@[simp] theorem ramseyanCandidate_rank_end
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    (forest.ramseyanCandidate elements).rank
        ⟨word.length, by omega⟩ =
      elements.rightMarkerLevel
        (FactorTree.HeightBoundedForest.outerLayer
          bound) := by
  change
    forest.coloredRank elements
        (forest.wordToYieldCut
          ⟨word.length, by omega⟩) =
      elements.rightMarkerLevel
        (FactorTree.HeightBoundedForest.outerLayer
          bound)
  have hcut :
      forest.wordToYieldCut
          ⟨word.length, by omega⟩ =
        (⟨forest.tree.yield.length, by omega⟩ :
          WordCut forest.tree.yield) := by
    apply Fin.ext
    exact congrArg List.length
      forest.yield_eq |>.symm
  rw [hcut]
  exact forest.coloredRank_end elements

theorem ramseyanCandidate_rank_lt_outerLeft_of_interior
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound)
    (cut : WordCut word)
    (hpositive : 0 < cut.1)
    (hstrict : cut.1 < word.length) :
    ((forest.ramseyanCandidate elements).rank cut).1 <
      (elements.leftMarkerLevel
        (FactorTree.HeightBoundedForest.outerLayer
          bound)).1 := by
  change
    (forest.coloredRank elements
      (forest.wordToYieldCut cut)).1 <
      (elements.leftMarkerLevel
        (FactorTree.HeightBoundedForest.outerLayer
          bound)).1
  apply forest.coloredRank_lt_outerLeft_of_interior
    elements
  · simpa using hpositive
  · have hlength :=
      congrArg List.length forest.yield_eq
    simpa using (show cut.1 <
      forest.tree.yield.length by omega)

theorem ramseyanCandidate_neighbors_strict_interior
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound)
    {left right : WordCut word}
    (hneighbors :
      levelNeighbors
        (forest.ramseyanCandidate elements).rank
        left right) :
    0 < left.1 ∧ right.1 < word.length := by
  have hrankEq := hneighbors.2.1
  constructor
  · by_cases hzero : left.1 = 0
    · have hleft :
          left = (⟨0, by omega⟩ : WordCut word) := by
        apply Fin.ext
        exact hzero
      rw [hleft,
        forest.ramseyanCandidate_rank_start elements]
        at hrankEq
      by_cases hend : right.1 = word.length
      · have hright :
            right =
              (⟨word.length, by omega⟩ :
                WordCut word) := by
          apply Fin.ext
          exact hend
        rw [hright,
          forest.ramseyanCandidate_rank_end elements]
          at hrankEq
        have hlt :=
          elements.leftMarker_lt_rightMarker
            (FactorTree.HeightBoundedForest.outerLayer
              bound)
        have hval := congrArg Fin.val hrankEq
        omega
      · have hrightBound := right.val_le_length
        have hrightStrict : right.1 < word.length := by
          omega
        have hrightPositive : 0 < right.1 := by
          have horder := hneighbors.1
          omega
        have hlt :=
          forest.ramseyanCandidate_rank_lt_outerLeft_of_interior
            elements right hrightPositive hrightStrict
        have hval := congrArg Fin.val hrankEq
        omega
    · omega
  · by_cases hend : right.1 = word.length
    · have hright :
          right =
            (⟨word.length, by omega⟩ :
              WordCut word) := by
        apply Fin.ext
        exact hend
      rw [hright,
        forest.ramseyanCandidate_rank_end elements]
        at hrankEq
      by_cases hstart : left.1 = 0
      · have hleft :
            left =
              (⟨0, by omega⟩ :
                WordCut word) := by
          apply Fin.ext
          exact hstart
        rw [hleft,
          forest.ramseyanCandidate_rank_start elements]
          at hrankEq
        have hlt :=
          elements.leftMarker_lt_rightMarker
            (FactorTree.HeightBoundedForest.outerLayer
              bound)
        have hval := congrArg Fin.val hrankEq
        omega
      · have hleftPositive : 0 < left.1 := by
          omega
        have hleftStrict : left.1 < word.length := by
          have horder := hneighbors.1
          omega
        have hlt :=
          forest.ramseyanCandidate_rank_lt_outerLeft_of_interior
            elements left hleftPositive hleftStrict
        have hval := congrArg Fin.val hrankEq
        have hmarkers :=
          elements.leftMarker_lt_rightMarker
            (FactorTree.HeightBoundedForest.outerLayer
              bound)
        omega
    · have hrightBound := right.val_le_length
      omega

theorem ramseyanCandidate_listLevelNeighbors
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound)
    {left right : WordCut word}
    (hneighbors :
      levelNeighbors
        (forest.ramseyanCandidate elements).rank
        left right) :
    let data := forest.coloredInteriorRanks elements
    let yieldLeft := forest.wordToYieldCut left
    let yieldRight := forest.wordToYieldCut right
    listLevelNeighbors data.ranks
      (data.interiorIndex yieldLeft
        (by
          have hstrict :=
            forest.ramseyanCandidate_neighbors_strict_interior
              elements hneighbors
          simpa using hstrict.1)
        (by
          have hstrict :=
            forest.ramseyanCandidate_neighbors_strict_interior
              elements hneighbors
          have horder := hneighbors.1
          have hlength :=
            congrArg List.length forest.yield_eq
          simpa using (show left.1 <
            forest.tree.yield.length by omega)))
      (data.interiorIndex yieldRight
        (by
          have horder := hneighbors.1
          have hstrict :=
            forest.ramseyanCandidate_neighbors_strict_interior
              elements hneighbors
          simpa using (show 0 < right.1 by omega))
        (by
          have hstrict :=
            forest.ramseyanCandidate_neighbors_strict_interior
              elements hneighbors
          have hlength :=
            congrArg List.length forest.yield_eq
          simpa using (show right.1 <
            forest.tree.yield.length by omega))) := by
  dsimp only
  have hstrict :=
    forest.ramseyanCandidate_neighbors_strict_interior
      elements hneighbors
  have horder := hneighbors.1
  have hlength :=
    congrArg List.length forest.yield_eq
  have hleftPositive :
      0 < (forest.wordToYieldCut left).1 := by
    simpa using hstrict.1
  have hleftStrict :
      (forest.wordToYieldCut left).1 <
        forest.tree.yield.length := by
    simpa using (show left.1 <
      forest.tree.yield.length by omega)
  have hrightPositive :
      0 < (forest.wordToYieldCut right).1 := by
    simpa using (show 0 < right.1 by omega)
  have hrightStrict :
      (forest.wordToYieldCut right).1 <
        forest.tree.yield.length := by
    simpa using (show right.1 <
      forest.tree.yield.length by omega)
  refine
    (forest.coloredInteriorRanks elements
      ).listLevelNeighbors_of_levelNeighbors
        (elements.leftMarkerLevel
          (FactorTree.HeightBoundedForest.outerLayer
            bound))
        (elements.rightMarkerLevel
          (FactorTree.HeightBoundedForest.outerLayer
            bound))
        ?_ hleftPositive hleftStrict
        hrightPositive hrightStrict
  change
    levelNeighbors
      (forest.coloredRank elements)
      (forest.wordToYieldCut left)
      (forest.wordToYieldCut right)
  refine ⟨hneighbors.1, ?_, ?_⟩
  · exact hneighbors.2.1
  · intro middle hleftMiddle hmiddleRight
    let wordMiddle : WordCut word :=
      WordCut.transport
        (congrArg List.length forest.yield_eq)
        middle
    have hmiddleRank :
        (forest.ramseyanCandidate elements).rank
            wordMiddle =
          forest.coloredRank elements middle := by
      unfold ramseyanCandidate wordToYieldCut wordMiddle
      congr 1
    rw [← hmiddleRank]
    apply hneighbors.2.2 wordMiddle
    · simpa [wordMiddle] using hleftMiddle
    · simpa [wordMiddle] using hmiddleRight

theorem ramseyanCandidate_neighbor_control
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    ∀ left right,
      levelNeighbors
          (forest.ramseyanCandidate elements).rank
          left right →
        C.eval letter
            (WordCut.interval word left right) =
          (forest.ramseyanCandidate elements
            ).idempotentAt
              ((forest.ramseyanCandidate elements
                ).rank left) := by
  intro left right hneighbors
  let data := forest.coloredInteriorRanks elements
  let yieldLeft := forest.wordToYieldCut left
  let yieldRight := forest.wordToYieldCut right
  have hstrict :=
    forest.ramseyanCandidate_neighbors_strict_interior
      elements hneighbors
  have horder := hneighbors.1
  have hlength :=
    congrArg List.length forest.yield_eq
  have hleftPositive : 0 < yieldLeft.1 := by
    simpa [yieldLeft] using hstrict.1
  have hleftStrict :
      yieldLeft.1 < forest.tree.yield.length := by
    simpa [yieldLeft] using (show
      left.1 < forest.tree.yield.length by omega)
  have hrightPositive : 0 < yieldRight.1 := by
    simpa [yieldRight] using
      (show 0 < right.1 by omega)
  have hrightStrict :
      yieldRight.1 < forest.tree.yield.length := by
    simpa [yieldRight] using (show
      right.1 < forest.tree.yield.length by omega)
  let leftIndex :=
    data.interiorIndex yieldLeft
      hleftPositive hleftStrict
  let rightIndex :=
    data.interiorIndex yieldRight
      hrightPositive hrightStrict
  have hlist :=
    forest.ramseyanCandidate_listLevelNeighbors
      elements hneighbors
  dsimp only at hlist
  have hsound :=
    forest.coloredInteriorRanks_neighborEvalSound
      elements leftIndex rightIndex hlist
  have hleftCut :
      leftIndex.1 + 1 = yieldLeft.1 := by
    simp only [leftIndex,
      InteriorRankData.interiorIndex_val]
    omega
  have hrightCut :
      rightIndex.1 + 1 = yieldRight.1 := by
    simp only [rightIndex,
      InteriorRankData.interiorIndex_val]
    omega
  have hleftRank :=
    data.rankAtCut_eq_interiorIndex
      (elements.leftMarkerLevel
        (FactorTree.HeightBoundedForest.outerLayer
          bound))
      (elements.rightMarkerLevel
        (FactorTree.HeightBoundedForest.outerLayer
          bound))
      yieldLeft hleftPositive hleftStrict
  rw [forest.interval_eq_yield_interval
    left right]
  change
    C.eval letter
        (ControlMonoid.middleFactor
          forest.tree.yield yieldLeft.1 yieldRight.1) =
      C.coloredIdempotentAt elements
        (forest.coloredRank elements yieldLeft)
  calc
    C.eval letter
        (ControlMonoid.middleFactor
          forest.tree.yield yieldLeft.1 yieldRight.1) =
      C.eval letter
        (ControlMonoid.middleFactor
          forest.tree.yield
          (leftIndex.1 + 1)
          (rightIndex.1 + 1)) := by
            rw [hleftCut, hrightCut]
    _ = C.coloredIdempotentAt elements
        data.ranks[leftIndex.1] :=
      hsound
    _ = C.coloredIdempotentAt elements
        (forest.coloredRank elements yieldLeft) := by
      apply congrArg
        (C.coloredIdempotentAt elements)
      symm
      exact hleftRank

noncomputable def ramseyanSplit
    [DecidableEq M]
    (elements : Enumeration M)
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {bound : Nat}
    (forest :
      FactorTree.HeightBoundedForest
        C letter word bound) :
    RamseyanSplit C letter word
      ((bound + 2) * elements.colorWidth) :=
  (forest.ramseyanCandidate elements).toRamseyanSplit
    (forest.ramseyanCandidate_neighbor_control
      elements)

end FactorTree.HeightBoundedForest

end NSSE
