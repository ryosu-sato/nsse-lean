import NSSE.P0DZVirtualTrace
import NSSE.P0DZNormalization

/-! Endpoint conditions discharge the rank cap: an absent final D
alternative, or a proper virtual endpoint with no outgoing D edge,
forbids all same-state nested proper suffix pairs. -/
namespace NSSE.P0DZEndpointRank
open P0DZBranch P0DZTrace P0DZVirtualTrace P0SuffixRank P0DZNormalization
variable {Q Z A H : Type*}

theorem no_links_absent (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hend : properAt J w w.length = none) (a b : Nat) : ¬ Linked J w a b := by
  intro hab
  have ha := hab.1
  have hb := hab.2.1
  have hh := linked_states J w a b hab w.length (by omega) (by omega)
  obtain ⟨q,hq⟩ := complete_prefix J w hc (a+(w.length-b)) (by omega)
  rw [hend,hq] at hh
  cases hh

theorem no_links_dead (J : Branch Q Z A H) (w : List A)
    (q : Q) (hend : properAt J w w.length = some q) (hdead : ∀ a, J.next q a = none)
    (a b : Nat) : ¬ Linked J w a b := by
  intro hab
  have hc : DComplete J w := by unfold DComplete; rw [hend]; rfl
  have ha := hab.1
  have hb := hab.2.1
  have hh := linked_states J w a b hab w.length (by omega) (by omega)
  rw [hend] at hh
  obtain ⟨r,hr⟩ := d_succ J w hc (a+(w.length-b)) (by omega) q hh
  rw [hdead] at hr
  cases hr

variable [DecidableEq Q] [DecidableEq A]

theorem rank_one_of_no_links (J : Branch Q Z A H) (w : List A)
    (h : ∀ a b, ¬ Linked J w a b) : maxRank J w ≤ 1 := by
  apply P0SuffixRankRecurrence.max_le_of_chains
  intro a S hS
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hn
  rcases lt_or_gt_of_ne hn with hpq | hqp
  · exact h p q (hS.2.2.2 p hp q hq hpq)
  · exact h q p (hS.2.2.2 q hq p hp hqp)

theorem absent_rank (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hend : properAt J w w.length = none) : maxRank J w ≤ 1 :=
  rank_one_of_no_links J w (no_links_absent J w hc hend)

theorem dead_rank (J : Branch Q Z A H) (w : List A)
    (q : Q) (hend : properAt J w w.length = some q) (hdead : ∀ a, J.next q a = none) :
    maxRank J w ≤ 1 := rank_one_of_no_links J w (no_links_dead J w q hend hdead)

theorem absent_short [Fintype Q] (J : Branch Q Z A H) (w : List A)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) (hend : properAt J w w.length = none) :
    ∃ v, Accepted J v ∧ maxRank J v ≤ 1 ∧ v.length ≤ w.length ∧
      v.length ≤ lengthBound (Fintype.card Q) 1 :=
  normalize J w hends hw 1 (absent_rank J w hw.1 hend)

theorem dead_short [Fintype Q] (J : Branch Q Z A H) (w : List A)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (q : Q) (hend : properAt J w w.length = some q) (hdead : ∀ a, J.next q a = none) :
    ∃ v, Accepted J v ∧ maxRank J v ≤ 1 ∧ v.length ≤ w.length ∧
      v.length ≤ lengthBound (Fintype.card Q) 1 :=
  normalize J w hends hw 1 (dead_rank J w q hend hdead)

end NSSE.P0DZEndpointRank
