import NSSE.P0DZSingleCut

/-! An actual one-color cotree node gives a literal, strictly shorter
accepted word of no larger rank. The complete four-rail Entry is derived
from its external module rule, not supplied as an extra hypothesis. -/
namespace NSSE.P0DZModuleCut
open P0DZBranch P0DZTrace P0DZRelations P0DZRankColor P0DZCotree P0DZSingleCut
open P0DZCutSafety P0WordCuts P0SingleCut P0SuffixRank
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A]

theorem entry_of_module (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (S : Finset Nat) (hm : ColoredModule J w S) (a b : Nat) (ha : a ∈ S) (hb : b ∈ S)
    (hlo : ∀ z ∈ S, a ≤ z) (hhi : ∀ z ∈ S, z ≤ b) (hab : a < b) (hbn : b ≤ w.length)
    (hcol : color J w a = color J w b) : FullEntry (single w a b hab hbn) J := by
  apply entry_of_equality _ J hc
  intro s t
  apply P0ModuleCut.entry_of_external w (labelAt J w s) (labelAt J w t) a b hab hbn
  intro z hz hout
  have hzu : z ∉ S := by
    intro hzin
    have := hlo z hzin
    have := hhi z hzin
    omega
  have haz : a ≠ z := by omega
  have hbz : b ≠ z := by omega
  have hh := hm a ha b hb hcol z hz hzu s t
  simpa only [comparison_eq J w hc a z haz s t,comparison_eq J w hc b z hbz s t,
    comparison_eq J w hc z a (Ne.symm haz) s t,comparison_eq J w hc z b (Ne.symm hbz) s t] using hh

theorem shorten_extremes (J : Branch Q Z A H) (w : List A) (S : Finset Nat)
    (hm : ColoredModule J w S) (a b : Nat) (ha : a ∈ S) (hb : b ∈ S)
    (hlo : ∀ z ∈ S, a ≤ z) (hhi : ∀ z ∈ S, z ≤ b) (hab : a < b) (hbn : b ≤ w.length)
    (hcol : color J w a = color J w b) (hends : J.endX ≠ J.endY) (hw : Accepted J w) :
    Accepted J (w.take a ++ w.drop b) ∧ (w.take a ++ w.drop b).length < w.length ∧
      maxRank J (w.take a ++ w.drop b) ≤ maxRank J w := by
  have he := entry_of_module J w hw.1 S hm a b ha hb hlo hhi hab hbn hcol
  have hl := state_of_color J w hw.1 a b (by omega) hbn hcol
  simpa only [word_single] using accepted_rank_single J w a b hab hbn hends hw hl he

theorem one_color_shorten (J : Branch Q Z A H) (w : List A) (S : Finset Nat)
    (hm : ColoredModule J w S) (hbound : ∀ z ∈ S, z ≤ w.length)
    (hone : ∀ a ∈ S, ∀ b ∈ S, color J w a = color J w b)
    (hsize : 1 < S.card) (hends : J.endX ≠ J.endY) (hw : Accepted J w) :
    ∃ v, Accepted J v ∧ v.length < w.length ∧ maxRank J v ≤ maxRank J w := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  let a := S.min' hne
  let b := S.max' hne
  have ha : a ∈ S := S.min'_mem hne
  have hb : b ∈ S := S.max'_mem hne
  exact ⟨w.take a ++ w.drop b,shorten_extremes J w S hm a b ha hb
    (fun z hz => S.min'_le z hz) (fun z hz => S.le_max' z hz)
    (S.min'_lt_max'_of_card hsize) (hbound b hb) (hone a ha b hb) hends hw⟩

/-- Shortest among accepted words of no greater rank than this word. -/
def RankMinimal (J : Branch Q Z A H) (w : List A) : Prop :=
  ∀ v, Accepted J v → maxRank J v ≤ maxRank J w → w.length ≤ v.length

theorem shortest_one_color (J : Branch Q Z A H) (w : List A) (S : Finset Nat)
    (hm : ColoredModule J w S) (hbound : ∀ z ∈ S, z ≤ w.length)
    (hone : ∀ a ∈ S, ∀ b ∈ S, color J w a = color J w b)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) (hmin : RankMinimal J w) : S.card ≤ 1 := by
  by_contra h
  obtain ⟨v,hv,hlen,hrank⟩ := one_color_shorten J w S hm hbound hone (by omega) hends hw
  have := hmin v hv hrank
  omega

theorem minimal_tree (J : Branch Q Z A H) (w : List A) (hw : Accepted J w)
    (hends : J.endX ≠ J.endY) (hmin : RankMinimal J w) :
    ∃ t : P0Cotree.Tree Nat, P0Cotree.leaves t = Finset.range (w.length+1) ∧
      P0Cotree.Valid (P0DZSuffixWords.Adjacent J w) t ∧ ∀ u, P0Cotree.Below u t →
        ColoredModule J w (P0Cotree.leaves u) ∧
        ((∀ a ∈ P0Cotree.leaves u, ∀ b ∈ P0Cotree.leaves u, color J w a = color J w b) →
          (P0Cotree.leaves u).card ≤ 1) := by
  obtain ⟨t,hleaf,ht,hm⟩ := actual_modules J w hw.1 hends
  refine ⟨t,hleaf,ht,?_⟩
  intro u hu
  refine ⟨hm u hu,fun hone => shortest_one_color J w _ (hm u hu) ?_ hone hends hw hmin⟩
  intro z hz
  have hh := P0Cotree.below_subset hu hz
  rw [hleaf,Finset.mem_range] at hh
  omega

end NSSE.P0DZModuleCut
