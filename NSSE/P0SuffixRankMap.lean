import NSSE.P0SuffixRankRecurrence

/-! Pointwise rank monotonicity under an increasing map that preserves
actual same-state nested suffix links. Cut simulation will supply the
link-preservation premise; it is explicit at this intermediate layer. -/
namespace NSSE.P0SuffixRankMap
open P0DZBranch P0SuffixRank
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A]

omit [DecidableEq Q] [DecidableEq A] in
theorem chain_image (J : Branch Q Z A H) (v w : List A) (f : Nat → Nat)
    (hbound : ∀ i, i < v.length → f i < w.length)
    (hinc : ∀ i j, i < j → j < v.length → f i < f j)
    (hlink : ∀ a b, Linked J v a b → Linked J w (f a) (f b))
    (a : Nat) (S : Finset Nat) (hS : ChainAt J v a S) : ChainAt J w (f a) (S.image f) := by
  have hpos (i : Nat) (hi : i ∈ S) : i < v.length := Finset.mem_range.mp (hS.1 hi)
  refine ⟨?_,Finset.mem_image.mpr ⟨a,hS.2.1,rfl⟩,?_,?_⟩
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_range.mpr (hbound i (hpos i hi))
  · intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    rcases lt_or_eq_of_le (hS.2.2.1 i hi) with hai | rfl
    · exact Nat.le_of_lt (hinc a i hai (hpos i hi))
    · exact le_rfl
  · intro p hp q hq hpq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    have hij : i < j := by
      by_contra hn
      rcases lt_or_eq_of_le (show j ≤ i by omega) with hji | he
      · have hh := hinc j i hji (hpos i hi)
        omega
      · subst j; omega
    exact hlink i j (hS.2.2.2 i hi j hj hij)

theorem pointwise (J : Branch Q Z A H) (v w : List A) (f : Nat → Nat)
    (hbound : ∀ i, i < v.length → f i < w.length)
    (hinc : ∀ i j, i < j → j < v.length → f i < f j)
    (hlink : ∀ a b, Linked J v a b → Linked J w (f a) (f b))
    (a : Nat) (ha : a < v.length) : rank J v a ≤ rank J w (f a) := by
  obtain ⟨S,hS,hcard⟩ := rank_attained J v a ha
  have hpos (i : Nat) (hi : i ∈ S) : i < v.length := Finset.mem_range.mp (hS.1 hi)
  have hinj : Set.InjOn f S := by
    intro i hi j hj he
    by_contra hn
    rcases lt_or_gt_of_ne hn with hij | hji
    · have hh := hinc i j hij (hpos j hj); omega
    · have hh := hinc j i hji (hpos i hi); omega
  have hc := Finset.card_image_iff.mpr hinj
  have hh := chain_le_rank J w (f a) (S.image f) (chain_image J v w f hbound hinc hlink a S hS)
  rw [hc,hcard] at hh
  exact hh

theorem maximum (J : Branch Q Z A H) (v w : List A) (f : Nat → Nat)
    (hbound : ∀ i, i < v.length → f i < w.length)
    (hinc : ∀ i j, i < j → j < v.length → f i < f j)
    (hlink : ∀ a b, Linked J v a b → Linked J w (f a) (f b)) : maxRank J v ≤ maxRank J w := by
  apply Finset.sup_le
  intro a ha
  have hp := Finset.mem_range.mp ha
  exact (pointwise J v w f hbound hinc hlink a hp).trans (rank_le_max J w (f a) (hbound a hp))

end NSSE.P0SuffixRankMap
