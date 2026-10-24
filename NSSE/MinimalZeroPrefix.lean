import NSSE.BilateralSimonStep

/-!
# The first zero-valued prefix

For a nontrivial two-sided zero, every nonempty zero-valued word has a
least positive prefix whose control is zero.  All of its proper prefix
controls are nonzero, so any four-prefix repetition inside that block has
a proper right stabilizer.
-/

namespace NSSE

universe u v

namespace ControlMonoid

structure FirstZeroPrefix
    (C : ControlMonoid M) (letter : α → M)
    (zero : M) (word : Word α) where
  cut : Nat
  positive : 0 < cut
  bounded : cut ≤ word.length
  control_eq : C.eval letter (word.take cut) = zero
  minimal :
    ∀ index, index < cut →
      C.eval letter (word.take index) ≠ zero

theorem exists_least_nat_witness
    (predicate : Nat → Prop)
    (hexists : ∃ index, predicate index) :
    ∃ least,
      predicate least ∧
      ∀ index, index < least → ¬ predicate index := by
  obtain ⟨bound, hbound⟩ := hexists
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
      by_cases hearlier :
          ∃ index, index < bound ∧ predicate index
      · obtain ⟨index, hindex, hpredicate⟩ := hearlier
        exact ih index hindex hpredicate
      · exact ⟨bound, hbound, by
          intro index hindex hpredicate
          exact hearlier ⟨index, hindex, hpredicate⟩⟩

theorem firstZeroPrefix_nonempty
    (C : ControlMonoid M) (letter : α → M)
    (zero : M) (hzeroOne : zero ≠ C.one)
    (word : Word α) (hword : word ≠ [])
    (hcontrol : C.eval letter word = zero) :
    Nonempty (FirstZeroPrefix C letter zero word) := by
  have hlength : 0 < word.length :=
    List.length_pos_iff.mpr hword
  let predicate : Nat → Prop :=
    fun cut =>
      0 < cut ∧ cut ≤ word.length ∧
        C.eval letter (word.take cut) = zero
  have hexists : ∃ cut, predicate cut := by
    refine ⟨word.length, hlength, Nat.le_refl _, ?_⟩
    simpa [predicate] using hcontrol
  obtain ⟨cut, hcut, hleast⟩ :=
    exists_least_nat_witness predicate hexists
  refine ⟨{
    cut := cut
    positive := hcut.1
    bounded := hcut.2.1
    control_eq := hcut.2.2
    minimal := ?_
  }⟩
  intro index hindex hindexZero
  rcases Nat.eq_zero_or_pos index with rfl | hpositive
  · simp [ControlMonoid.eval] at hindexZero
    exact hzeroOne hindexZero.symm
  · exact hleast index hindex
      ⟨hpositive,
        Nat.le_trans (Nat.le_of_lt hindex) hcut.2.1,
        hindexZero⟩

noncomputable def firstZeroPrefix
    (C : ControlMonoid M) (letter : α → M)
    (zero : M) (hzeroOne : zero ≠ C.one)
    (word : Word α) (hword : word ≠ [])
    (hcontrol : C.eval letter word = zero) :
    FirstZeroPrefix C letter zero word :=
  Classical.choice
    (firstZeroPrefix_nonempty
      C letter zero hzeroOne word hword hcontrol)

theorem FirstZeroPrefix.prefix_ne_nil
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α}
    (first : FirstZeroPrefix C letter zero word) :
    word.take first.cut ≠ [] := by
  intro hempty
  have hlength := congrArg List.length hempty
  simp only [List.length_take, List.length_nil] at hlength
  have hmin :
      min first.cut word.length = first.cut :=
    Nat.min_eq_left first.bounded
  rw [hmin] at hlength
  exact (Nat.ne_of_gt first.positive) hlength

theorem FirstZeroPrefix.proper_rightStabilizer_of_fourCuts
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α}
    (first : FirstZeroPrefix C letter zero word)
    (hzeroRight : ∀ value : M, C.mul value zero = zero)
    (cuts :
      C.FourPrefixControlCuts letter (word.take first.cut)) :
    (C.rightStabilizer cuts.anchor).Proper := by
  apply cuts.rightStabilizer_proper_of_minimal_zero
    zero hzeroRight
  intro index hindex
  have hindexCut : index < first.cut := by
    simpa [List.length_take,
      Nat.min_eq_left first.bounded] using hindex
  have hminimal := first.minimal index hindexCut
  simpa [List.take_take,
    Nat.min_eq_left (Nat.le_of_lt hindexCut)] using hminimal

noncomputable def FirstZeroPrefix.assembleWord
    {C : ControlMonoid M} {letter : α → M}
    {zero : M} {word : Word α} {bound : Nat}
    (first : FirstZeroPrefix C letter zero word)
    (prefixForest :
      FactorTree.HeightBoundedForest
        C letter (word.take first.cut) bound)
    (suffixForest :
      word.drop first.cut ≠ [] →
        FactorTree.HeightBoundedForest
          C letter (word.drop first.cut) bound) :
    FactorTree.HeightBoundedForest
      C letter word (bound + 1) := by
  by_cases hsuffix : word.drop first.cut = []
  · exact (prefixForest.weaken (bound + 1) (by omega)).rewriteWord
      word (by
        simpa [hsuffix] using
          List.take_append_drop first.cut word)
  · let suffix := suffixForest hsuffix
    let joined :=
      FactorTree.HeightBoundedForest.binary
        prefixForest suffix
    exact joined.rewriteWord word
      (List.take_append_drop first.cut word)

end ControlMonoid

end NSSE
