import NSSE.P0ColorBound

/-! Quantitative induction on actual cotree palettes. A union child can
use the entire parent palette; its join children have fewer colors, which
is the precise reason the induction is well founded. -/
namespace NSSE.P0ShortestWordBound
open P0Cotree P0CotreeNormalize P0CotreeColors P0NormalizedActual P0ActualCotree
open P0DDeadReader P0DDeadColor P0ModuleCut P0UnionProfileBound P0ColorBound
variable {Q A H : Type*} [DecidableEq Q]

theorem one_color (J : Reader Q A H) (w : List A) (t u : Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hu : Below u t) (hk : (palette (color J w) u).card ≤ 1)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hmin : ∀ v, Accepted J v → w.length ≤ v.length) : (leaves u).card ≤ 1 := by
  apply shortest_one_color J w (leaves u) (node_module J w hw.1 hends t u hleaves ht hu)
    ?_ ?_ hends hw hmin
  · intro p hp
    have hh := below_subset hu hp
    rw [hleaves,Finset.mem_range] at hh
    omega
  · intro a ha b hb
    exact Finset.card_le_one.mp hk _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
      _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)

theorem node_bound (J : Reader Q A H) (w : List A) (t : Tree Nat)
    (ht : Valid (Adjacent J w) t) (hleaves : leaves t = Finset.range (w.length+1))
    (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hmin : ∀ v, Accepted J v → w.length ≤ v.length) :
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
    have hjoin (l r : Tree Nat) (hn : Below (.fork true l r) t)
        (hp : (palette (color J w) (.fork true l r)).card ≤ k+1) :
        (leaves (.fork true l r)).card ≤ (k+1)*bound k := by
      have hv := below_valid (Adjacent J w) hn ht
      have hproper := actual_proper J w hw.1 (.fork true l r)
      have hb : ∀ c ∈ children (.fork true l r), (leaves c).card ≤ bound k := by
        intro c hc
        have hf := join_child_fewer (Adjacent J w) (color J w) l r c hv hproper hc
        exact ih c (below_trans (children_below true l r c hc) hn) (by omega)
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
          have hct := below_trans (children_below false l r c hc) hu
          have hcp : (palette (color J w) c).card ≤ k+1 :=
            (Finset.card_le_card (palette_below (color J w) (children_below false l r c hc))).trans hk
          rcases union_child_leaf_or_join l r c hc with ⟨v,rfl⟩ | ⟨a,b,rfl⟩
          · simp only [leaves,Finset.card_singleton]
            exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (positive k))
          · exact hjoin a b hct hcp
        exact (union_size_bound J w t l r ht hleaves hu (k+1) ((k+1)*bound k)
          hk hB hends hw hmin).trans (union_le k)

theorem shortest_bound [Fintype Q] (J : Reader Q A H) (w : List A)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hmin : ∀ v, Accepted J v → w.length ≤ v.length) :
    w.length ≤ bound (Fintype.card Q+1)-1 := by
  obtain ⟨t,hleaves,ht⟩ := exists_tree J w hw.1 hends
  have hk : (palette (color J w) t).card ≤ Fintype.card Q+1 := by
    simpa using Finset.card_le_univ (palette (color J w) t)
  have hh := node_bound J w t ht hleaves hends hw hmin (Fintype.card Q+1) t (.refl t) hk
  rw [hleaves,Finset.card_range] at hh
  omega

theorem exists_short [Fintype Q] (J : Reader Q A H) (hends : J.endX ≠ J.endY)
    (hex : ∃ w, Accepted J w) :
    ∃ w, Accepted J w ∧ w.length ≤ bound (Fintype.card Q+1)-1 := by
  classical
  have hn : ∃ n, ∃ w, Accepted J w ∧ w.length = n := by
    obtain ⟨w,hw⟩ := hex
    exact ⟨w.length,w,hw,rfl⟩
  obtain ⟨w,hw,hlen⟩ := Nat.find_spec hn
  have hmin (v : List A) (hv : Accepted J v) : w.length ≤ v.length := by
    rw [hlen]
    exact Nat.find_min' hn ⟨v,hv,rfl⟩
  exact ⟨w,hw,shortest_bound J w hends hw hmin⟩

end NSSE.P0ShortestWordBound
