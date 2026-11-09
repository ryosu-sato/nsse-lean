import NSSE.P0ProperLiveness
import Mathlib.Order.Interval.Finset.Nat

/-! Same-state nested suffix chains of a nonlive Good word inject into
positive safe-pair image sizes. No bound on earlier internal factors is claimed. -/
namespace NSSE.P0NonliveChains
open P0ProperMachine P0ProperWords P0PairImages P0ProperLiveness
variable {Q A H : Type*} [DecidableEq Q] [Fintype Q] [DecidableEq H]
variable (M : Machine Q A H) [DecidablePred M.valid]

theorem card_distinct (w : List A) (hw : GoodWord M w) (hn : ¬Live M w)
    (a b : Nat) (hab : a < b) (hb : b ≤ w.length)
    (hq : state M w a = state M w b) (hp : (w.drop b).IsPrefix (w.drop a)) :
    (image M (w.drop a)).card ≠ (image M (w.drop b)).card := by
  intro he
  exact hn (nested_live M w hw a b hab hb hq hp he)

theorem chain_bound (w : List A) (hw : GoodWord M w) (hn : ¬Live M w)
    (S : Finset Nat) (hS : S ⊆ Finset.range w.length)
    (hc : ∀ a ∈ S, ∀ b ∈ S, a < b →
      state M w a = state M w b ∧ (w.drop b).IsPrefix (w.drop a)) :
    S.card ≤ Fintype.card Q ^ 2 := by
  let f := fun a => (image M (w.drop a)).card
  have hinj : Set.InjOn f S := by
    intro a ha b hb he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    · obtain ⟨hq,hp⟩ := hc a ha b hb hab
      exact card_distinct M w hw hn a b hab
        (by have := Finset.mem_range.mp (hS hb); omega) hq hp he
    · obtain ⟨hq,hp⟩ := hc b hb a ha hba
      exact card_distinct M w hw hn b a hba
        (by have := Finset.mem_range.mp (hS ha); omega) hq hp he.symm
  have hsub : S.image f ⊆ Finset.Icc 1 (Fintype.card Q ^ 2) := by
    intro k hk
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr ⟨suffix_image_positive M w hw a,card_bound M (w.drop a)⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj] at hh
  simpa using hh

end NSSE.P0NonliveChains
