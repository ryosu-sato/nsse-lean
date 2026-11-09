import NSSE.P0SafePairs
import Mathlib.Data.Fintype.Card

/-! Exact finite images of all safe starting pairs. These sets are
independent of which pairs are born in a particular source word. -/
namespace NSSE.P0PairImages
open P0ProperMachine P0SafePairs
variable {Q A H : Type*} [DecidableEq Q] [Fintype Q] [DecidableEq H]
variable (M : Machine Q A H) [DecidablePred M.valid]

def image (w : List A) : Finset (Q × Q) :=
  (Finset.univ.filter (Safe M w)).image (finish M w)

theorem mem_image (w : List A) (p : Q × Q) :
    p ∈ image M w ↔ ∃ q, Safe M w q ∧ finish M w q = p := by
  simp [image]

theorem image_valid (w : List A) (p : Q × Q) (hp : p ∈ image M w) :
    ValidPair M p := by
  obtain ⟨q,hq,rfl⟩ := (mem_image M w p).mp hp
  exact safe_finish M w q hq

theorem image_append (u v : List A) :
    image M (u ++ v) = ((image M u).filter (Safe M v)).image (finish M v) := by
  ext p
  simp only [mem_image,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨q,hq,he⟩
    obtain ⟨hu,hv⟩ := (safe_append M u v q).mp hq
    exact ⟨finish M u q,⟨⟨q,hu,rfl⟩,hv⟩,by simpa only [finish_append] using he⟩
  · rintro ⟨s,⟨⟨q,hu,rfl⟩,hv⟩,he⟩
    exact ⟨q,(safe_append M u v q).mpr ⟨hu,hv⟩,by simpa only [finish_append] using he⟩

theorem suffix_subset (u v : List A) : image M (u ++ v) ⊆ image M v := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := (mem_image M (u ++ v) p).mp hp
  rw [finish_append]
  exact (mem_image M v _).mpr ⟨finish M u q,((safe_append M u v q).mp hq).2,rfl⟩

theorem card_bound (w : List A) : (image M w).card ≤ Fintype.card Q ^ 2 := by
  have h := (image M w).card_le_univ
  simpa only [Fintype.card_prod,pow_two] using h

theorem image_nonempty (w : List A) (q : Q)
    (hv : ∀ k, k ≤ w.length → M.valid ((w.take k).foldl M.step q)) :
    (image M w).Nonempty :=
  ⟨finish M w (q,q),(mem_image M w _).mpr ⟨(q,q),diagonal_safe M w q hv,rfl⟩⟩

theorem good_nonempty (w : List A) (hw : P0ProperWords.GoodWord M w) :
    (image M w).Nonempty := image_nonempty M w M.initial hw.1

theorem stable_total (r c : List A)
    (hcard : (image M (r ++ c)).card = (image M r).card) :
    ∀ p ∈ image M r, Safe M c p := by
  have hle : (image M r).card ≤ ((image M r).filter (Safe M c)).card := by
    rw [← hcard,image_append]
    exact Finset.card_image_le
  have he := Finset.eq_of_subset_of_card_le (Finset.filter_subset (Safe M c) (image M r)) hle
  intro p hp
  rw [← he] at hp
  exact (Finset.mem_filter.mp hp).2

theorem stable_image (r c : List A)
    (hsuffix : ∃ u, r ++ c = u ++ r)
    (hcard : (image M (r ++ c)).card = (image M r).card) :
    image M (r ++ c) = image M r := by
  obtain ⟨u,hu⟩ := hsuffix
  apply Finset.eq_of_subset_of_card_le
  · rw [hu]
    exact suffix_subset M u r
  · exact hcard.ge

theorem stable_closed (r c : List A)
    (hsuffix : ∃ u, r ++ c = u ++ r)
    (hcard : (image M (r ++ c)).card = (image M r).card) :
    ∀ p ∈ image M r, finish M c p ∈ image M r := by
  intro p hp
  rw [← stable_image M r c hsuffix hcard,image_append]
  exact Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr
    ⟨hp,stable_total M r c hcard p hp⟩,rfl⟩

theorem stable_permutation (r c : List A)
    (hsuffix : ∃ u, r ++ c = u ++ r)
    (hcard : (image M (r ++ c)).card = (image M r).card) :
    Set.BijOn (finish M c) (image M r) (image M r) := by
  have hf : (image M r).filter (Safe M c) = image M r :=
    Finset.filter_eq_self.mpr (stable_total M r c hcard)
  have hi : (image M r).image (finish M c) = image M r := by
    have he := image_append M r c
    rw [hf] at he
    exact he.symm.trans (stable_image M r c hsuffix hcard)
  refine ⟨stable_closed M r c hsuffix hcard,?_,?_⟩
  · exact Finset.card_image_iff.mp (congrArg Finset.card hi)
  · intro p hp
    have hp' : p ∈ (image M r).image (finish M c) := by rwa [hi]
    exact Finset.mem_image.mp hp'

end NSSE.P0PairImages
