import NSSE.P0DZColorBound
import NSSE.P0NormalizedActual

/-! Quantitative color induction for actual D/Z cotrees. It gives an
explicit length bound while preserving a supplied rank cap. The bound
itself is a computable number, independent of any minimum selection. -/
namespace NSSE.P0DZNormalization
open P0Cotree P0CotreeNormalize P0CotreeColors
open P0DZBranch P0DZRankColor P0DZSuffixWords P0DZCotree P0DZModuleCut P0DZMinimal
open P0DZUnionProfileBound P0DZColorBound P0SuffixRank
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A]

theorem proper_below (J : Branch Q Z A H) (w : List A) (hc : Complete J w)
    (hends : J.endX ≠ J.endY) (t u : P0Cotree.Tree Nat)
    (hleaves : leaves t = Finset.range (w.length+1)) (hu : Below u t) :
    Proper (Adjacent J w) (color J w) u := by
  have hb (a : Nat) (ha : a ∈ leaves u) : a ≤ w.length := by
    have hh := below_subset hu ha
    rw [hleaves,Finset.mem_range] at hh
    omega
  intro a ha b hb' hne he
  exact proper_coloring J w hc hends a b (hb a ha) (hb b hb') hne he

theorem one_color (J : Branch Q Z A H) (w : List A) (t u : P0Cotree.Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hu : Below u t) (hk : (palette (color J w) u).card ≤ 1)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) (hmin : RankMinimal J w) :
    (leaves u).card ≤ 1 := by
  apply shortest_one_color J w (leaves u) (node_module J w hw.1 hends t u hleaves ht hu)
    ?_ ?_ hends hw hmin
  · intro p hp
    have hh := below_subset hu hp
    rw [hleaves,Finset.mem_range] at hh
    omega
  · intro a ha b hb
    exact Finset.card_le_one.mp hk _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
      _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)

theorem node_bound (J : Branch Q Z A H) (w : List A) (t : P0Cotree.Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) (hmin : RankMinimal J w) :
    ∀ k u, Below u t → (palette (color J w) u).card ≤ k → (leaves u).card ≤ bound k := by
  intro k
  induction k with
  | zero =>
    intro u hu hk
    have hp := Finset.card_pos.mpr (palette_nonempty (color J w) u)
    omega
  | succ k ih =>
    intro u hu hk
    by_cases hsmall : (palette (color J w) u).card ≤ 1
    · exact (one_color J w t u ht hleaves hu hsmall hends hw hmin).trans
        (Nat.succ_le_of_lt (positive (k+1)))
    have hjoin (l r : P0Cotree.Tree Nat) (hn : Below (.fork true l r) t)
        (hp : (palette (color J w) (.fork true l r)).card ≤ k+1) :
        (leaves (.fork true l r)).card ≤ (k+1)*bound k := by
      have hv := below_valid (Adjacent J w) hn ht
      have hproper := proper_below J w hw.1 hends t (.fork true l r) hleaves hn
      have hb : ∀ c ∈ children (.fork true l r), (leaves c).card ≤ bound k := by
        intro c hc
        have hf := join_child_fewer (Adjacent J w) (color J w) l r c hv hproper hc
        exact ih c (P0NormalizedActual.below_trans (children_below true l r c hc) hn) (by omega)
      exact (join_size_le (Adjacent J w) (color J w) l r (bound k) hv hproper hb).trans
        (Nat.mul_le_mul_right _ hp)
    cases u with
    | leaf v => simpa only [leaves,Finset.card_singleton] using Nat.succ_le_of_lt (positive (k+1))
    | fork j l r =>
      cases j with
      | true => exact (hjoin l r hu hk).trans (join_le k)
      | false =>
        have hB : ∀ c ∈ children (.fork false l r), (leaves c).card ≤ (k+1)*bound k := by
          intro c hc
          have hct := P0NormalizedActual.below_trans (children_below false l r c hc) hu
          have hcp : (palette (color J w) c).card ≤ k+1 :=
            (Finset.card_le_card (palette_below (color J w) (children_below false l r c hc))).trans hk
          rcases union_child_leaf_or_join l r c hc with ⟨v,rfl⟩ | ⟨a,b,rfl⟩
          · simp only [leaves,Finset.card_singleton]
            exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (positive k))
          · exact hjoin a b hct hcp
        exact (union_size_bound J w t l r ht hleaves hu (k+1) ((k+1)*bound k)
          hk hB hends hw hmin).trans (union_le k)

def lengthBound (N B : Nat) : Nat := bound (1+N*B)-1

theorem minimal_bound [Fintype Q] (J : Branch Q Z A H) (w : List A)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) (hmin : RankMinimal J w)
    (B : Nat) (hB : maxRank J w ≤ B) : w.length ≤ lengthBound (Fintype.card Q) B := by
  obtain ⟨t,hleaves,ht⟩ := exists_tree J w hw.1 hends
  have hk : (palette (color J w) t).card ≤ 1+Fintype.card Q*B := by
    simpa only [palette,hleaves] using color_count J w hw.1 B hB
  have hh := node_bound J w t ht hleaves hends hw hmin (1+Fintype.card Q*B) t (.refl t) hk
  rw [hleaves,Finset.card_range] at hh
  dsimp only [lengthBound]
  omega

theorem normalize [Fintype Q] (J : Branch Q Z A H) (w : List A)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) (B : Nat) (hB : maxRank J w ≤ B) :
    ∃ v, Accepted J v ∧ maxRank J v ≤ B ∧ v.length ≤ w.length ∧
      v.length ≤ lengthBound (Fintype.card Q) B := by
  obtain ⟨v,hv,hlen,hr,hmin⟩ := representative J w hw
  have hrB := hr.trans hB
  exact ⟨v,hv,hrB,hlen,minimal_bound J v hends hv hmin B hrB⟩

end NSSE.P0DZNormalization
