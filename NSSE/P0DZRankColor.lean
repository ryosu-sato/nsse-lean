import NSSE.P0DZSuffixWords
import Mathlib.Data.Fintype.Prod

/-! Refined actual colors are (proper state, suffix rank), with one extra
terminal color. Their equality forbids every off-diagonal four-rail
conflict. A rank cap B gives at most 1 + |Q|*B colors. -/
namespace NSSE.P0DZRankColor
open P0DZBranch P0DZTrace P0DZRelations P0DZSuffixWords P0SuffixConflict P0SuffixRank
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A]

def color (J : Branch Q Z A H) (w : List A) (k : Nat) : Option (Q × Nat) :=
  if k < w.length then (properAt J w k).map (fun q => (q,rank J w k)) else none

theorem terminal_color (J : Branch Q Z A H) (w : List A) : color J w w.length = none := by
  simp [color]

theorem terminal_color_iff (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (a : Nat) (ha : a ≤ w.length) : color J w a = none ↔ a = w.length := by
  by_cases hap : a < w.length
  · obtain ⟨q,hq⟩ := complete_prefix J w hc a hap
    simp [color,hap,hq,show a ≠ w.length by omega]
  · have he : a = w.length := by omega
    simp [he,terminal_color]

theorem proper_equal_color (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (ha : a < w.length) (hb : b < w.length)
    (he : color J w a = color J w b) :
    properAt J w a = properAt J w b ∧ rank J w a = rank J w b := by
  obtain ⟨q,hq⟩ := complete_prefix J w hc a ha
  obtain ⟨r,hr⟩ := complete_prefix J w hc b hb
  simp only [color,if_pos ha,if_pos hb,hq,hr] at he
  change some (q,rank J w a) = some (r,rank J w b) at he
  simp only [Option.some.injEq,Prod.mk.injEq] at he
  exact ⟨by rw [hq,hr,he.1],he.2⟩

theorem ordered_compatible (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (a b : Nat) (hab : a < b) (hb : b < w.length)
    (he : color J w a = color J w b) : AllCompatible J w a b := by
  have hs := proper_equal_color J w hc a b (by omega) hb he
  by_contra hn
  have hl := (conflict_iff_linked J w hc hends a b hab hb hs.1).mp hn
  have hh := rank_strict J w a b hl
  omega

theorem proper_coloring (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length)
    (hne : a ≠ b) (he : color J w a = color J w b) : ¬ Adjacent J w a b := by
  have hap : a < w.length := by
    by_contra hn
    have hea : a = w.length := by omega
    have hbn : color J w b = none := by rw [← he,hea,terminal_color]
    have heb := (terminal_color_iff J w hc b hb).mp hbn
    exact hne (hea.trans heb.symm)
  have hbp : b < w.length := by
    by_contra hn
    have heb : b = w.length := by omega
    have han : color J w a = none := by rw [he,heb,terminal_color]
    have hea := (terminal_color_iff J w hc a ha).mp han
    exact hne (hea.trans heb.symm)
  intro hn
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact hn (ordered_compatible J w hc hends a b hab hbp he)
  · exact hn (all_symm J w b a (ordered_compatible J w hc hends b a hba hap he.symm))

theorem color_count [Fintype Q] (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (B : Nat) (hB : maxRank J w ≤ B) :
    ((Finset.range (w.length+1)).image (color J w)).card ≤ 1+Fintype.card Q*B := by
  let S : Finset (Q × Nat) := Finset.univ ×ˢ Finset.range B
  let f : Q × Nat → Option (Q × Nat) := fun p => some (p.1,p.2+1)
  have hsub : (Finset.range (w.length+1)).image (color J w) ⊆ insert none (S.image f) := by
    intro c hmem
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hmem
    have hab : a ≤ w.length := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using ha
    by_cases hap : a < w.length
    · obtain ⟨q,hq⟩ := complete_prefix J w hc a hap
      have hrp := rank_positive J w a hap
      have hrb := (rank_le_max J w a hap).trans hB
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨(q,rank J w a-1),?_,?_⟩
      · simp only [S,Finset.mem_product,Finset.mem_univ,Finset.mem_range,true_and]
        omega
      · simp only [f,color,if_pos hap,hq,Option.map_some]
        congr 2
        omega
    · have he : a = w.length := by omega
      rw [he,terminal_color]
      exact Finset.mem_insert_self _ _
  calc
    _ ≤ (insert none (S.image f)).card := Finset.card_le_card hsub
    _ ≤ (S.image f).card+1 := Finset.card_insert_le _ _
    _ ≤ S.card+1 := Nat.add_le_add_right (Finset.card_image_le) 1
    _ = 1+Fintype.card Q*B := by simp [S,Finset.card_product,Nat.add_comm]

end NSSE.P0DZRankColor
