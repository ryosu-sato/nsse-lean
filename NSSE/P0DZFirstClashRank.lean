import NSSE.P0DZClashChains
import NSSE.P0DZNormalization

/-! The global first-D-clash theorem: every same-state suffix chain
injects into Q, including the possible one early origin. Thus the whole
word has rank at most |Q| and accepted virtual-unsafe words have an
input-only short witness bound. -/
namespace NSSE.P0DZFirstClashRank
open P0DZBranch P0DZTrace P0DZVirtualTrace P0DZFirstClash P0DZClashChains
open P0SuffixRank P0DZNormalization
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A] [Fintype Q]

omit [DecidableEq A] in
theorem chain_bound (J : Branch Q Z A H) (w : List A) (hf : FirstUnsafe J w)
    (o : Nat) (S : Finset Nat) (hS : ChainAt J w o S) : S.card ≤ Fintype.card Q := by
  obtain ⟨a,b,l,hab,hend,h⟩ := ordered_witness J w hf
  let q := dState J w o
  have hpos (c : Nat) (hc : c ∈ S) : c < w.length := Finset.mem_range.mp (hS.1 hc)
  have hsame (c : Nat) (hc : c ∈ S) : dState J w c = q := by
    rcases lt_or_eq_of_le (hS.2.2.1 c hc) with hoc | he
    · have hh := hS.2.2.2 o hS.2.1 c hc hoc
      exact (states_of_proper J w o c hh.2.2.1).symm
    · subst c; rfl
  have hlate (c : Nat) (hc : c ∈ S) (hbc : b < c) : aligned J w a b c ≠ q := by
    rw [← hsame c hc]
    exact aligned_ne_self J w hf.complete a b l hab hend h c (by omega) (Nat.le_of_lt (hpos c hc))
  let f : Nat → Q := fun c => if c ≤ b then q else aligned J w a b c
  have hinj : Set.InjOn f S := by
    intro c hc d hd he
    by_cases hcb : c ≤ b
    · by_cases hdb : d ≤ b
      · by_contra hn
        rcases lt_or_gt_of_ne hn with hcd | hdc
        · exact no_two_early J w hf a b l hab hend h c d (hS.2.2.2 c hc d hd hcd) hdb
        · exact no_two_early J w hf a b l hab hend h d c (hS.2.2.2 d hd c hc hdc) hcb
      · simp only [f,if_pos hcb,if_neg hdb] at he
        exact False.elim (hlate d hd (by omega) he.symm)
    · by_cases hdb : d ≤ b
      · simp only [f,if_neg hcb,if_pos hdb] at he
        exact False.elim (hlate c hc (by omega) he)
      · simp only [f,if_neg hcb,if_neg hdb] at he
        by_contra hn
        rcases lt_or_gt_of_ne hn with hcd | hdc
        · exact aligned_distinct J w hf a b l hab hend h c d (by omega) (hS.2.2.2 c hc d hd hcd) he
        · exact aligned_distinct J w hf a b l hab hend h d c (by omega) (hS.2.2.2 d hd c hc hdc) he.symm
  have hcard := Finset.card_image_iff.mpr hinj
  calc
    S.card = (S.image f).card := hcard.symm
    _ ≤ Fintype.card Q := Finset.card_le_univ _

theorem rank_bound (J : Branch Q Z A H) (w : List A) (hf : FirstUnsafe J w) :
    maxRank J w ≤ Fintype.card Q :=
  P0SuffixRankRecurrence.max_le_of_chains J w (Fintype.card Q) (chain_bound J w hf)

theorem first_short (J : Branch Q Z A H) (w : List A) (hends : J.endX ≠ J.endY)
    (hw : Accepted J w) (hf : FirstUnsafe J w) :
    ∃ v, Accepted J v ∧ maxRank J v ≤ Fintype.card Q ∧ v.length ≤ w.length ∧
      v.length ≤ lengthBound (Fintype.card Q) (Fintype.card Q) :=
  normalize J w hends hw _ (rank_bound J w hf)

theorem virtual_unsafe_short (J : Branch Q Z A H) (w : List A) (hends : J.endX ≠ J.endY)
    (hw : Accepted J w) (hc : DComplete J w) (hu : ∃ a b l, Clash J w a b l) :
    ∃ v, Accepted J v ∧ maxRank J v ≤ Fintype.card Q ∧ v.length ≤ w.length ∧
      v.length ≤ lengthBound (Fintype.card Q) (Fintype.card Q) :=
  first_short J w hends hw (accepted_first J w hw hc hu)

end NSSE.P0DZFirstClashRank
