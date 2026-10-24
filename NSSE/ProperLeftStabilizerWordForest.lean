import NSSE.UniformFactorForestBound
import NSSE.BilateralSimonStep

/-!
# Whole-word forest for the proper-left-stabilizer branch

Four equal suffix controls give three consecutive blocks in one proper
left stabilizer.  The finite list of cuts is unpacked, its block forest is
grafted, and the two exterior pieces are reattached.
-/

namespace NSSE

universe u v

namespace ControlMonoid.FourSuffixControlCuts

theorem exists_properLeftWordForest
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {letter : α → M} {word : Word α}
    (cuts : C.FourSuffixControlCuts letter word)
    (innerBound outerBound : Nat)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        (C.leftStabilizer cuts.anchor).toControlMonoid outerBound)
    (recursive :
      ∀ subword : Word α,
        subword.length < word.length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest
          C letter subword innerBound) :
    Nonempty
      (FactorTree.HeightBoundedForest C letter word
        (innerBound + outerBound + 2)) := by
  cases hindices : cuts.indices with
  | nil =>
      have hlength := cuts.length_eq
      simp [hindices] at hlength
  | cons i₀ rest₀ =>
      cases rest₀ with
      | nil =>
          have hlength := cuts.length_eq
          simp [hindices] at hlength
      | cons i₁ rest₁ =>
          cases rest₁ with
          | nil =>
              have hlength := cuts.length_eq
              simp [hindices] at hlength
          | cons i₂ rest₂ =>
              cases rest₂ with
              | nil =>
                  have hlength := cuts.length_eq
                  simp [hindices] at hlength
              | cons i₃ tail =>
                  have htailLength : tail.length = 0 := by
                    have hlength := cuts.length_eq
                    rw [hindices] at hlength
                    simp only [List.length_cons,
                      List.length_nil] at hlength
                    omega
                  have htail : tail = [] :=
                    List.length_eq_zero_iff.mp htailLength
                  subst tail
                  let indices := [i₀, i₁, i₂, i₃]
                  have hindiciesEq : cuts.indices = indices := by
                    simp [indices, hindices]
                  have hordered :
                      indices.Pairwise (· < ·) := by
                    rw [← hindiciesEq]
                    exact cuts.ordered
                  have hbounded :
                      ∀ index ∈ indices,
                        index ≤ word.length := by
                    intro index hindex
                    apply cuts.bounded index
                    rwa [hindiciesEq]
                  have hcontrol :
                      ∀ index ∈ indices,
                        C.eval letter (word.drop index) =
                          cuts.anchor := by
                    intro index hindex
                    apply cuts.equal_control index
                    rwa [hindiciesEq]
                  have h01 : i₀ < i₁ := by
                    simpa [indices] using
                      (List.pairwise_cons.mp hordered).1 i₁ (by simp)
                  have h12 : i₁ < i₂ := by
                    have htailOrdered :=
                      (List.pairwise_cons.mp hordered).2
                    simpa [indices] using
                      (List.pairwise_cons.mp htailOrdered).1 i₂
                        (by simp)
                  have h23 : i₂ < i₃ := by
                    have htailOrdered :=
                      (List.pairwise_cons.mp
                        (List.pairwise_cons.mp
                          (List.pairwise_cons.mp hordered).2).2).1
                          i₃ (by simp)
                    exact htailOrdered
                  have hi3 : i₃ ≤ word.length :=
                    hbounded i₃ (by simp [indices])
                  let block₀₁ := middleFactor word i₀ i₁
                  let block₁₂ := middleFactor word i₁ i₂
                  let block₂₃ := middleFactor word i₂ i₃
                  have hblock₀₁Ne : block₀₁ ≠ [] :=
                    middleFactor_ne_nil word h01
                      (Nat.le_trans (Nat.le_of_lt h12)
                        (Nat.le_trans (Nat.le_of_lt h23) hi3))
                  have hblock₁₂Ne : block₁₂ ≠ [] :=
                    middleFactor_ne_nil word h12
                      (Nat.le_trans (Nat.le_of_lt h23) hi3)
                  have hblock₂₃Ne : block₂₃ ≠ [] :=
                    middleFactor_ne_nil word h23 hi3
                  have hwhole :
                      word.take i₀ ++ block₀₁ ++ block₁₂ ++
                          block₂₃ ++ word.drop i₃ =
                        word := by
                    dsimp [block₀₁, block₁₂, block₂₃]
                    calc
                      word.take i₀ ++ middleFactor word i₀ i₁ ++
                            middleFactor word i₁ i₂ ++
                            middleFactor word i₂ i₃ ++ word.drop i₃ =
                          (word.take i₀ ++
                              middleFactor word i₀ i₁) ++
                            middleFactor word i₁ i₂ ++
                            middleFactor word i₂ i₃ ++ word.drop i₃ := by
                              simp [List.append_assoc]
                      _ =
                          (word.take i₁ ++
                              middleFactor word i₁ i₂) ++
                            middleFactor word i₂ i₃ ++ word.drop i₃ := by
                              rw [take_append_middleFactor word
                                (Nat.le_of_lt h01)]
                      _ =
                          (word.take i₂ ++
                              middleFactor word i₂ i₃) ++
                            word.drop i₃ := by
                              rw [take_append_middleFactor word
                                (Nat.le_of_lt h12)]
                      _ = word.take i₃ ++ word.drop i₃ := by
                            rw [take_append_middleFactor word
                              (Nat.le_of_lt h23)]
                      _ = word := List.take_append_drop i₃ word
                  have hblock₀₁Lt :
                      block₀₁.length < word.length := by
                    have hlength := congrArg List.length hwhole
                    simp only [List.length_append] at hlength
                    have h₁ := List.length_pos_iff.mpr hblock₁₂Ne
                    have h₂ := List.length_pos_iff.mpr hblock₂₃Ne
                    omega
                  have hblock₁₂Lt :
                      block₁₂.length < word.length := by
                    have hlength := congrArg List.length hwhole
                    simp only [List.length_append] at hlength
                    have h₀ := List.length_pos_iff.mpr hblock₀₁Ne
                    have h₂ := List.length_pos_iff.mpr hblock₂₃Ne
                    omega
                  have hblock₂₃Lt :
                      block₂₃.length < word.length := by
                    have hlength := congrArg List.length hwhole
                    simp only [List.length_append] at hlength
                    have h₀ := List.length_pos_iff.mpr hblock₀₁Ne
                    have h₁ := List.length_pos_iff.mpr hblock₁₂Ne
                    omega
                  have replacementNonempty :
                      ∀ block ∈
                          ControlMonoid.blocksBetweenCuts word indices,
                        Nonempty
                          (FactorTree.HeightBoundedForest
                            C letter block innerBound) := by
                    intro block hblock
                    simp [indices, ControlMonoid.blocksBetweenCuts,
                      block₀₁, block₁₂, block₂₃] at hblock
                    rcases hblock with rfl | rfl | rfl
                    · exact ⟨recursive block₀₁
                        hblock₀₁Lt hblock₀₁Ne⟩
                    · exact ⟨recursive block₁₂
                        hblock₁₂Lt hblock₁₂Ne⟩
                    · exact ⟨recursive block₂₃
                        hblock₂₃Lt hblock₂₃Ne⟩
                  let replacement :
                      ∀ block ∈
                          ControlMonoid.blocksBetweenCuts word indices,
                        FactorTree.HeightBoundedForest
                          C letter block innerBound :=
                    fun block hblock =>
                      Classical.choice
                        (replacementNonempty block hblock)
                  let middle :=
                    Classical.choice
                      (UniformFactorForestBound.graft_equal_suffix_blocks
                        letter word cuts.anchor indices
                        (by simp [indices])
                        hordered hbounded hcontrol
                        uniformOuter replacement)
                  have hbeforeLt :
                      (word.take i₀).length < word.length := by
                    simp only [List.length_take]
                    have hi0Lt :
                        i₀ < word.length :=
                      Nat.lt_of_lt_of_le h01
                        (Nat.le_trans (Nat.le_of_lt h12)
                          (Nat.le_trans (Nat.le_of_lt h23) hi3))
                    omega
                  have hafterLt :
                      word.drop i₃ ≠ [] →
                        (word.drop i₃).length < word.length := by
                    intro hafter
                    have hi3Positive : 0 < i₃ := by omega
                    have hwordPositive :
                        0 < word.length := by omega
                    simp only [List.length_drop]
                    omega
                  exact ⟨
                    FactorTree.HeightBoundedForest.surround
                      middle
                      (fun hnonempty =>
                        (recursive (word.take i₀)
                          hbeforeLt hnonempty).weaken
                            (innerBound + outerBound) (by omega))
                      (fun hnonempty =>
                        (recursive (word.drop i₃)
                          (hafterLt hnonempty) hnonempty).weaken
                            (innerBound + outerBound) (by omega))
                      (by
                        simpa [indices, block₀₁, block₁₂, block₂₃,
                          ControlMonoid.blocksBetweenCuts,
                          List.append_assoc] using hwhole)
                    ⟩

noncomputable def properLeftWordForest
    {M : Type v} {α : Type u}
    {C : ControlMonoid M} {letter : α → M} {word : Word α}
    (cuts : C.FourSuffixControlCuts letter word)
    (innerBound outerBound : Nat)
    (uniformOuter :
      UniformFactorForestBound.{u, v}
        (C.leftStabilizer cuts.anchor).toControlMonoid outerBound)
    (recursive :
      ∀ subword : Word α,
        subword.length < word.length →
        subword ≠ [] →
        FactorTree.HeightBoundedForest
          C letter subword innerBound) :
    FactorTree.HeightBoundedForest C letter word
      (innerBound + outerBound + 2) :=
  Classical.choice
    (exists_properLeftWordForest
      cuts innerBound outerBound uniformOuter recursive)

end ControlMonoid.FourSuffixControlCuts

end NSSE
