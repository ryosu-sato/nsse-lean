import NSSE.PivotGapDecomposition
import NSSE.FinitePrefixControlLoop

/-!
# Ramseyan splits of finite control words

Ramseyan splits label cut positions rather than disjoint factors.  This is the
right intermediate object for local-divisor induction because neighboring
pivot-delimited intervals may share their endpoint cut without duplicating a
letter.

Two cuts are `levelNeighbors` when they carry the same level and no cut
strictly between them has a larger level.  A Ramseyan split assigns one
idempotent control to every level and requires every neighboring interval at
that level to have that control.
-/

namespace NSSE

universe u v

def WordCut (word : Word α) :=
  Fin (word.length + 1)

namespace WordCut

theorem val_le_length
    {word : Word α} (cut : WordCut word) :
    cut.1 ≤ word.length := by
  omega

def interval
    (word : Word α) (left right : WordCut word) :
    Word α :=
  ControlMonoid.middleFactor word left.1 right.1

theorem interval_append
    (word : Word α)
    (left middle right : WordCut word)
    (hlm : left.1 ≤ middle.1)
    (hmr : middle.1 ≤ right.1) :
    interval word left middle ++
        interval word middle right =
      interval word left right := by
  unfold interval ControlMonoid.middleFactor
  have hdrop :
      (word.drop left.1).drop (middle.1 - left.1) =
        word.drop middle.1 := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [← hdrop, ← List.take_add]
  congr 1
  omega

theorem eval_interval_append
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α)
    (left middle right : WordCut word)
    (hlm : left.1 ≤ middle.1)
    (hmr : middle.1 ≤ right.1) :
    C.eval letter (interval word left right) =
      C.mul
        (C.eval letter (interval word left middle))
        (C.eval letter (interval word middle right)) := by
  rw [← C.eval_append]
  exact congrArg (C.eval letter)
    (interval_append word left middle right hlm hmr).symm

theorem interval_ne_nil
    (word : Word α)
    {left right : WordCut word}
    (hlt : left.1 < right.1) :
    interval word left right ≠ [] :=
  ControlMonoid.middleFactor_ne_nil
    word hlt right.val_le_length

def toControlWord
    (letter : α → M) (word : Word α) :
    WordCut word → WordCut (word.map letter) :=
  fun cut => ⟨cut.1, by simp [cut.2]⟩

def ofControlWord
    (letter : α → M) (word : Word α) :
    WordCut (word.map letter) → WordCut word :=
  fun cut => ⟨cut.1, by simpa using cut.2⟩

@[simp] theorem toControlWord_val
    (letter : α → M) (word : Word α)
    (cut : WordCut word) :
    (toControlWord letter word cut).1 = cut.1 :=
  rfl

@[simp] theorem ofControlWord_val
    (letter : α → M) (word : Word α)
    (cut : WordCut (word.map letter)) :
    (ofControlWord letter word cut).1 = cut.1 :=
  rfl

theorem eval_interval_controlWord
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (left right : WordCut word) :
    C.eval letter (interval word left right) =
      C.eval id
        (interval (word.map letter)
          (toControlWord letter word left)
          (toControlWord letter word right)) := by
  have hinter :
      interval (word.map letter)
          (toControlWord letter word left)
          (toControlWord letter word right) =
        (interval word left right).map letter := by
    simp [interval, ControlMonoid.middleFactor]
  rw [hinter]
  simp [ControlMonoid.eval, List.map_map, Function.comp_def]

def intoInterval
    (word : Word α) (left right : WordCut word)
    (hle : left.1 ≤ right.1)
    (cut : WordCut (interval word left right)) :
    WordCut word :=
  ⟨left.1 + cut.1, by
    have hlength :
        (interval word left right).length =
          right.1 - left.1 :=
      ControlMonoid.middleFactor_length word hle
        right.val_le_length
    have hcut := cut.2
    have hcutBound :
        cut.1 < right.1 - left.1 + 1 := by
      simpa only [hlength] using hcut
    have hright := right.val_le_length
    omega⟩

@[simp] theorem intoInterval_val
    (word : Word α) (left right : WordCut word)
    (hle : left.1 ≤ right.1)
    (cut : WordCut (interval word left right)) :
    (intoInterval word left right hle cut).1 =
      left.1 + cut.1 :=
  rfl

theorem interval_intoInterval
    (word : Word α) (left right : WordCut word)
    (hle : left.1 ≤ right.1)
    (innerLeft innerRight :
      WordCut (interval word left right))
    (hinner : innerLeft.1 ≤ innerRight.1) :
    interval (interval word left right)
        innerLeft innerRight =
      interval word
        (intoInterval word left right hle innerLeft)
        (intoInterval word left right hle innerRight) := by
  change
    ControlMonoid.middleFactor
        (ControlMonoid.middleFactor word left.1 right.1)
        innerLeft.1 innerRight.1 =
      ControlMonoid.middleFactor word
        (left.1 + innerLeft.1)
        (left.1 + innerRight.1)
  unfold interval ControlMonoid.middleFactor
  rw [List.drop_take, List.drop_drop, List.take_take]
  have hright := right.val_le_length
  have hinnerRight :
      innerRight.1 < right.1 - left.1 + 1 := by
    have hlength :
        (interval word left right).length =
          right.1 - left.1 :=
      ControlMonoid.middleFactor_length word hle
        right.val_le_length
    have hbound := innerRight.2
    omega
  congr 2 <;> omega

end WordCut

def levelNeighbors
    {word : Word α} {height : Nat}
    (rank : WordCut word → Fin height)
    (left right : WordCut word) : Prop :=
  left.1 < right.1 ∧
  rank left = rank right ∧
  ∀ middle : WordCut word,
    left.1 < middle.1 →
    middle.1 < right.1 →
    (rank middle).1 ≤ (rank left).1

structure RamseyanSplit
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) (height : Nat) where
  rank : WordCut word → Fin height
  idempotentAt : Fin height → M
  idempotent :
    ∀ level, C.Idempotent (idempotentAt level)
  neighbor_control :
    ∀ left right,
      levelNeighbors rank left right →
      C.eval letter (WordCut.interval word left right) =
        idempotentAt (rank left)

namespace RamseyanSplit

theorem not_nonempty_height_zero
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) :
    ¬ Nonempty (RamseyanSplit C letter word 0) := by
  intro hsplit
  obtain ⟨split⟩ := hsplit
  let start : WordCut word := ⟨0, by omega⟩
  exact Fin.elim0 (split.rank start)

private def lexRank
    {coarseHeight fineHeight : Nat}
    (coarse : Fin coarseHeight)
    (fine : Fin fineHeight) :
    Fin (coarseHeight * fineHeight) :=
  ⟨coarse.1 * fineHeight + fine.1, by
    have hsucc : coarse.1 + 1 ≤ coarseHeight :=
      Nat.succ_le_of_lt coarse.2
    have hmul :=
      Nat.mul_le_mul_right fineHeight hsucc
    calc
      coarse.1 * fineHeight + fine.1 <
          coarse.1 * fineHeight + fineHeight := by
            exact Nat.add_lt_add_left fine.2 _
      _ = (coarse.1 + 1) * fineHeight := by
            rw [Nat.add_mul, Nat.one_mul]
      _ ≤ coarseHeight * fineHeight := hmul⟩

@[simp] private theorem lexRank_val
    {coarseHeight fineHeight : Nat}
    (coarse : Fin coarseHeight)
    (fine : Fin fineHeight) :
    (lexRank coarse fine).1 =
      coarse.1 * fineHeight + fine.1 :=
  rfl

private theorem coarse_le_of_lexRank_le
    {coarseHeight fineHeight : Nat}
    {coarse₁ coarse₂ : Fin coarseHeight}
    {fine₁ fine₂ : Fin fineHeight}
    (hle :
      (lexRank coarse₁ fine₁).1 ≤
        (lexRank coarse₂ fine₂).1) :
    coarse₁.1 ≤ coarse₂.1 := by
  apply Nat.le_of_not_lt
  intro hnot
  have hsucc : coarse₂.1 + 1 ≤ coarse₁.1 :=
    by omega
  have hmul :=
    Nat.mul_le_mul_right fineHeight hsucc
  have hbelow :
      coarse₂.1 * fineHeight + fine₂.1 <
        (coarse₂.1 + 1) * fineHeight := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_lt_add_left fine₂.2 _
  have habove :
      coarse₁.1 * fineHeight ≤
        coarse₁.1 * fineHeight + fine₁.1 :=
    Nat.le_add_right _ _
  simp only [lexRank_val] at hle
  omega

private theorem coarse_eq_of_lexRank_eq
    {coarseHeight fineHeight : Nat}
    {coarse₁ coarse₂ : Fin coarseHeight}
    {fine₁ fine₂ : Fin fineHeight}
    (heq : lexRank coarse₁ fine₁ =
      lexRank coarse₂ fine₂) :
    coarse₁ = coarse₂ := by
  apply Fin.ext
  apply Nat.le_antisymm
  · apply coarse_le_of_lexRank_le
    exact Nat.le_of_eq
      (congrArg Fin.val heq)
  · apply coarse_le_of_lexRank_le
    exact Nat.le_of_eq
      (congrArg Fin.val heq).symm

private def lexCoarse
    {coarseHeight fineHeight : Nat}
    (hfine : 0 < fineHeight)
    (level : Fin (coarseHeight * fineHeight)) :
    Fin coarseHeight :=
  ⟨level.1 / fineHeight,
    (Nat.div_lt_iff_lt_mul hfine).2 level.2⟩

@[simp] private theorem lexCoarse_lexRank
    {coarseHeight fineHeight : Nat}
    (hfine : 0 < fineHeight)
    (coarse : Fin coarseHeight)
    (fine : Fin fineHeight) :
    lexCoarse hfine (lexRank coarse fine) = coarse := by
  apply Fin.ext
  simp only [lexCoarse, lexRank_val]
  rw [Nat.mul_comm coarse.1 fineHeight,
    Nat.mul_add_div hfine]
  simp [Nat.div_eq_of_lt fine.2]

def refine
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {coarseHeight fineHeight : Nat}
    (split :
      RamseyanSplit C letter word coarseHeight)
    (hfine : 0 < fineHeight)
    (fine : WordCut word → Fin fineHeight) :
    RamseyanSplit C letter word
      (coarseHeight * fineHeight) where
  rank := fun cut => lexRank (split.rank cut) (fine cut)
  idempotentAt := fun level =>
    split.idempotentAt (lexCoarse hfine level)
  idempotent := by
    intro level
    exact split.idempotent (lexCoarse hfine level)
  neighbor_control := by
    intro left right hneighbors
    have hcoarse :
        levelNeighbors split.rank left right := by
      refine ⟨hneighbors.1, ?_, ?_⟩
      · exact coarse_eq_of_lexRank_eq hneighbors.2.1
      · intro middle hleft hright
        exact coarse_le_of_lexRank_le
          (hneighbors.2.2 middle hleft hright)
    rw [split.neighbor_control left right hcoarse]
    simp only [lexCoarse_lexRank]

def lowerOfTopUnused
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (hunused :
      ∀ cut : WordCut word,
        (split.rank cut).1 < height) :
    RamseyanSplit C letter word height where
  rank := fun cut =>
    ⟨(split.rank cut).1, hunused cut⟩
  idempotentAt := fun level =>
    split.idempotentAt
      ⟨level.1, Nat.lt.step level.2⟩
  idempotent := by
    intro level
    exact split.idempotent
      ⟨level.1, Nat.lt.step level.2⟩
  neighbor_control := by
    intro left right hneighbors
    have hsource :
        levelNeighbors split.rank left right := by
      refine ⟨hneighbors.1, ?_, ?_⟩
      · apply Fin.ext
        exact congrArg
          (fun level : Fin height => level.1)
          hneighbors.2.1
      · intro middle hleft hright
        exact hneighbors.2.2 middle hleft hright
    exact split.neighbor_control left right hsource

theorem topUsed_or_lower
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1)) :
    (∃ cut : WordCut word,
      (split.rank cut).1 = height) ∨
    Nonempty
      (RamseyanSplit C letter word height) := by
  classical
  by_cases hused :
      ∃ cut : WordCut word,
        (split.rank cut).1 = height
  · exact Or.inl hused
  · exact Or.inr
      ⟨split.lowerOfTopUnused (by
        intro cut
        have hbound := (split.rank cut).2
        have hne :
            (split.rank cut).1 ≠ height := by
          intro heq
          exact hused ⟨cut, heq⟩
        omega)⟩

def TopNeighbors
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (left right : WordCut word) : Prop :=
  left.1 < right.1 ∧
  (split.rank left).1 = height ∧
  (split.rank right).1 = height ∧
  ∀ middle : WordCut word,
    left.1 < middle.1 →
    middle.1 < right.1 →
    (split.rank middle).1 < height

theorem topNeighbors_levelNeighbors
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    {left right : WordCut word}
    (htop : split.TopNeighbors left right) :
    levelNeighbors split.rank left right := by
  refine ⟨htop.1, ?_, ?_⟩
  · apply Fin.ext
    exact htop.2.1.trans htop.2.2.1.symm
  · intro middle hleft hright
    have hmiddle :=
      htop.2.2.2 middle hleft hright
    rw [htop.2.1]
    exact Nat.le_of_lt hmiddle

theorem topNeighbors_control
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    {left right : WordCut word}
    (htop : split.TopNeighbors left right) :
    C.eval letter
        (WordCut.interval word left right) =
      split.idempotentAt
        ⟨height, by omega⟩ := by
  rw [split.neighbor_control left right
    (split.topNeighbors_levelNeighbors htop)]
  congr 1
  apply Fin.ext
  exact htop.2.1

def ofControlWord
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) {height : Nat}
    (split :
      RamseyanSplit C id (word.map letter) height) :
    RamseyanSplit C letter word height where
  rank := fun cut =>
    split.rank (WordCut.toControlWord letter word cut)
  idempotentAt := split.idempotentAt
  idempotent := split.idempotent
  neighbor_control := by
    intro left right hneighbors
    let cuts := WordCut.toControlWord letter word
    have hsource :
        levelNeighbors split.rank
          (cuts left) (cuts right) := by
      refine ⟨hneighbors.1, hneighbors.2.1, ?_⟩
      intro middle hleft hright
      let original : WordCut word :=
        WordCut.ofControlWord letter word middle
      have hleftOriginal : left.1 < original.1 := by
        simpa [original, cuts] using hleft
      have hrightOriginal : original.1 < right.1 := by
        simpa [original, cuts] using hright
      have hmiddle :=
        hneighbors.2.2 original
          hleftOriginal hrightOriginal
      simpa [original, cuts] using hmiddle
    rw [WordCut.eval_interval_controlWord
      C letter word left right]
    exact split.neighbor_control _ _ hsource

def restrict
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split : RamseyanSplit C letter word height)
    (left right : WordCut word)
    (hle : left.1 ≤ right.1) :
    RamseyanSplit C letter
      (WordCut.interval word left right) height where
  rank := fun cut =>
    split.rank
      (WordCut.intoInterval word left right hle cut)
  idempotentAt := split.idempotentAt
  idempotent := split.idempotent
  neighbor_control := by
    intro innerLeft innerRight hneighbors
    let embed :=
      WordCut.intoInterval word left right hle
    have hsource :
        levelNeighbors split.rank
          (embed innerLeft) (embed innerRight) := by
      refine ⟨?_, hneighbors.2.1, ?_⟩
      · simpa [embed] using hneighbors.1
      · intro middle hleft hright
        have hmiddleLower :
            left.1 ≤ middle.1 := by
          have hnonnegative : 0 ≤ innerLeft.1 :=
            Nat.zero_le _
          simp only [embed, WordCut.intoInterval_val]
            at hleft
          omega
        let localValue := middle.1 - left.1
        have hlocalBound :
            localValue <
              (WordCut.interval word left right).length + 1 := by
          have hlength :
              (WordCut.interval word left right).length =
                right.1 - left.1 :=
            ControlMonoid.middleFactor_length word hle
              right.val_le_length
          have hrightBoundary :
              middle.1 < right.1 := by
            simp only [embed, WordCut.intoInterval_val]
              at hright
            have hinnerRightBound := innerRight.2
            have hinnerRightBound' :
                innerRight.1 < right.1 - left.1 + 1 := by
              simpa only [hlength] using hinnerRightBound
            omega
          simp only [hlength]
          omega
        let localCut :
            WordCut (WordCut.interval word left right) :=
          ⟨localValue, hlocalBound⟩
        have hleftLocal :
            innerLeft.1 < localCut.1 := by
          simp only [embed, WordCut.intoInterval_val]
            at hleft
          simp only [localCut, localValue]
          omega
        have hrightLocal :
            localCut.1 < innerRight.1 := by
          simp only [embed, WordCut.intoInterval_val]
            at hright
          simp only [localCut, localValue]
          omega
        have hlocal :=
          hneighbors.2.2 localCut hleftLocal hrightLocal
        change
          (split.rank (embed localCut)).1 ≤
            (split.rank (embed innerLeft)).1
          at hlocal
        have hembedLocal : embed localCut = middle := by
          apply Fin.ext
          simp only [embed, WordCut.intoInterval_val,
            localCut, localValue]
          omega
        rw [hembedLocal] at hlocal
        exact hlocal
    rw [WordCut.interval_intoInterval
      word left right hle innerLeft innerRight
      (Nat.le_of_lt hneighbors.1)]
    exact split.neighbor_control _ _ hsource

def restrictBelowTop
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split :
      RamseyanSplit C letter word (height + 1))
    (left right : WordCut word)
    (hle : left.1 ≤ right.1)
    (hbelow :
      ∀ cut :
          WordCut (WordCut.interval word left right),
        (split.rank
          (WordCut.intoInterval
            word left right hle cut)).1 < height) :
    RamseyanSplit C letter
      (WordCut.interval word left right) height :=
  (split.restrict left right hle).lowerOfTopUnused
    hbelow

def byDistinctCuts
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) :
    RamseyanSplit C letter word (word.length + 1) where
  rank := fun cut => cut
  idempotentAt := fun _ => C.one
  idempotent := by
    intro level
    exact C.mul_one C.one
  neighbor_control := by
    intro left right hneighbors
    have heq : left = right :=
      Fin.ext (congrArg Fin.val hneighbors.2.1)
    subst right
    exact False.elim (Nat.lt_irrefl _ hneighbors.1)

theorem exists_length_bound
    (C : ControlMonoid M) (letter : α → M)
    (word : Word α) :
    Nonempty
      (RamseyanSplit C letter word (word.length + 1)) :=
  ⟨byDistinctCuts C letter word⟩

theorem neighboring_control_idempotent
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split : RamseyanSplit C letter word height)
    {left right : WordCut word}
    (hneighbors :
      levelNeighbors split.rank left right) :
    C.Idempotent
      (C.eval letter (WordCut.interval word left right)) := by
  rw [split.neighbor_control left right hneighbors]
  exact split.idempotent (split.rank left)

def weaken
    {C : ControlMonoid M} {letter : α → M}
    {word : Word α} {height : Nat}
    (split : RamseyanSplit C letter word height)
    (larger : Nat) (hle : height ≤ larger) :
    RamseyanSplit C letter word larger where
  rank := fun cut =>
    ⟨(split.rank cut).1,
      Nat.lt_of_lt_of_le (split.rank cut).2 hle⟩
  idempotentAt := fun level =>
    if hlevel : level.1 < height then
      split.idempotentAt ⟨level.1, hlevel⟩
    else
      C.one
  idempotent := by
    intro level
    split
    · exact split.idempotent _
    · exact C.mul_one C.one
  neighbor_control := by
    intro left right hneighbors
    have hneighborsOld :
        levelNeighbors split.rank left right := by
      rcases hneighbors with ⟨hlt, heq, hmiddle⟩
      have hval :
          (split.rank left).1 =
            (split.rank right).1 :=
        congrArg
          (fun level : Fin larger => level.1) heq
      refine ⟨hlt, Fin.ext hval, ?_⟩
      intro middle hl hm
      exact hmiddle middle hl hm
    have hrankLt : (split.rank left).1 < height :=
      (split.rank left).2
    simpa [hrankLt] using
      split.neighbor_control left right hneighborsOld

end RamseyanSplit

end NSSE
