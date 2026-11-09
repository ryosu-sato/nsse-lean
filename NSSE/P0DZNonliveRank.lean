import NSSE.P0NonliveChains
import NSSE.P0DZProperMachine
import NSSE.P0DZNormalization

/-! The nonlive proper-good branch of full D/Z normalization. The
explicit invalid sink gives the conservative cap (|Q|+1)^2. -/
namespace NSSE.P0DZNonliveRank
open P0DZBranch P0DZTrace P0DZProperMachine P0SuffixRank P0ProperWords
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A] [Fintype Q] [DecidableEq H]

theorem rank_bound (J : Branch Q Z A H) (w : List A)
    (hw : GoodWord (machine J) w) (hn : ¬Live J w) :
    maxRank J w ≤ (Fintype.card Q + 1)^2 := by
  apply P0SuffixRankRecurrence.max_le_of_chains J w
  intro a S hS
  have hh := P0NonliveChains.chain_bound (machine J) w hw hn S hS.1
    (fun u hu v hv huv =>
      ⟨(hS.2.2.2 u hu v hv huv).2.2.1,(hS.2.2.2 u hu v hv huv).2.2.2⟩)
  simpa using hh

theorem nonlive_short (J : Branch Q Z A H) (w : List A)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hg : GoodWord (machine J) w) (hn : ¬Live J w) :
    ∃ v, Accepted J v ∧ maxRank J v ≤ (Fintype.card Q+1)^2 ∧
      v.length ≤ w.length ∧
      v.length ≤ P0DZNormalization.lengthBound (Fintype.card Q) ((Fintype.card Q+1)^2) :=
  P0DZNormalization.normalize J w hends hw _ (rank_bound J w hg hn)

end NSSE.P0DZNonliveRank
