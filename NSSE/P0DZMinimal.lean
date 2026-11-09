import NSSE.P0DZModuleCut

/-! Every accepted word has a shortest representative among accepted
words of bounded rank. This existence lemma is used in the normalization
proof; executable decisions do not invoke this selection. -/
namespace NSSE.P0DZMinimal
open P0DZBranch P0SuffixRank P0DZModuleCut P0DZRankColor P0DZCotree
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A]

theorem representative (J : Branch Q Z A H) (w : List A) (hw : Accepted J w) :
    ∃ v, Accepted J v ∧ v.length ≤ w.length ∧ maxRank J v ≤ maxRank J w ∧ RankMinimal J v := by
  classical
  have hn : ∃ n, ∃ v, Accepted J v ∧ maxRank J v ≤ maxRank J w ∧ v.length = n :=
    ⟨w.length,w,hw,le_rfl,rfl⟩
  obtain ⟨v,hv,hr,hlen⟩ := Nat.find_spec hn
  refine ⟨v,hv,?_,hr,?_⟩
  · rw [hlen]
    exact Nat.find_min' hn ⟨w,hw,le_rfl,rfl⟩
  · intro u hu hur
    rw [hlen]
    exact Nat.find_min' hn ⟨u,hu,hur.trans hr,rfl⟩

theorem representative_tree [Fintype Q] (J : Branch Q Z A H) (w : List A) (hw : Accepted J w)
    (hends : J.endX ≠ J.endY) (B : Nat) (hB : maxRank J w ≤ B) :
    ∃ v, Accepted J v ∧ v.length ≤ w.length ∧ maxRank J v ≤ B ∧
      ((Finset.range (v.length+1)).image (color J v)).card ≤ 1+Fintype.card Q*B ∧
      ∃ t : P0Cotree.Tree Nat, P0Cotree.leaves t = Finset.range (v.length+1) ∧
        P0Cotree.Valid (P0DZSuffixWords.Adjacent J v) t ∧ ∀ u, P0Cotree.Below u t →
          ColoredModule J v (P0Cotree.leaves u) ∧
          ((∀ a ∈ P0Cotree.leaves u, ∀ b ∈ P0Cotree.leaves u, color J v a = color J v b) →
            (P0Cotree.leaves u).card ≤ 1) := by
  obtain ⟨v,hv,hlen,hr,hmin⟩ := representative J w hw
  have hrB := hr.trans hB
  exact ⟨v,hv,hlen,hrB,color_count J v hv.1 B hrB,minimal_tree J v hv hends hmin⟩

end NSSE.P0DZMinimal
