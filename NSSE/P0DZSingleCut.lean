import NSSE.P0DZCotree
import NSSE.P0DZCutRank
import NSSE.P0ModuleCut

/-! Single actual D/Z intervals and an equality-Entry bridge. Comparing
distinct retained positions uses actual completeness, so the equality
certificate also proves proper-constructor agreement on every rail. -/
namespace NSSE.P0DZSingleCut
open P0DZBranch P0DZTrace P0DZRelations P0DZRankColor P0DZCutTrace P0DZCutSafety
open P0WordCuts P0SingleCut P0SuffixRank
variable {Q Z A H : Type*}

theorem entry_of_equality {w : List A} {n : Nat} (C : Cut w n) (J : Branch Q Z A H)
    (hc : Complete J w)
    (he : ∀ s t, P0CutComparison.Entry C (labelAt J w s) (labelAt J w t)) : FullEntry C J := by
  intro s t i hi j hj hij hs hcomp
  have hh : P0CutComparison.Compatible w (labelAt J w s) (labelAt J w t)
      (C.source i) (C.source j) := fun l hl ha hb hm => agree_eq (hcomp l hl ha hb hm)
  exact (comparison_eq J w hc (C.lift i) (C.lift j)
    (fun h => hij (C.lift_injective i j hi hj h)) s t).mpr (he s t i hi j hj hij hs hh)

theorem loops_single (J : Branch Q Z A H) (w : List A) (a b : Nat)
    (hab : a < b) (hb : b ≤ w.length) (he : stateAt J w a = stateAt J w b) :
    Loops (single w a b hab hb) J := by
  intro k _
  rw [source_single]
  by_cases hk : k = a
  · subst k
    simp only [if_pos rfl,single,lt_self_iff_false,if_false]
    simpa only [show a+(b-a) = b by omega] using he
  · rw [if_neg hk]

variable [DecidableEq Q] [DecidableEq A]

theorem state_of_color (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length)
    (he : color J w a = color J w b) : stateAt J w a = stateAt J w b := by
  by_cases hap : a < w.length
  · have hbp : b < w.length := by
      by_contra hn
      have heb : b = w.length := by omega
      have han : color J w a = none := by rw [he,heb,terminal_color]
      have hea := (terminal_color_iff J w hc a ha).mp han
      omega
    have hq := (proper_equal_color J w hc a b hap hbp he).1
    rw [proper_state J w a hap,proper_state J w b hbp]
    exact congrArg (Option.map Sum.inl) hq
  · have hea : a = w.length := by omega
    have hbn : color J w b = none := by rw [← he,hea,terminal_color]
    have heb := (terminal_color_iff J w hc b hb).mp hbn
    rw [hea,heb]

theorem accepted_rank_single (J : Branch Q Z A H) (w : List A) (a b : Nat)
    (hab : a < b) (hb : b ≤ w.length) (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hloop : stateAt J w a = stateAt J w b) (he : FullEntry (single w a b hab hb) J) :
    Accepted J (single w a b hab hb).word ∧ (single w a b hab hb).word.length < w.length ∧
      maxRank J (single w a b hab hb).word ≤ maxRank J w := by
  have hl := loops_single J w a b hab hb hloop
  exact ⟨accepted_cut _ J hends hw hl he,shorter w a b hab hb,
    P0DZCutRank.maximum _ J hw.1 hends hl he⟩

end NSSE.P0DZSingleCut
