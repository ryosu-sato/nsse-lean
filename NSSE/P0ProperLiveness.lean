import NSSE.P0WordMarker
import NSSE.P0SuffixConflict

/-! Liveness preserves the entire finite history. A same-state nested
suffix with equal safe-pair image size supplies an actual extension. -/
namespace NSSE.P0ProperLiveness
open P0ProperMachine P0ProperWords P0PairImages
variable {Q A H : Type*}

def Live (M : Machine Q A H) (w : List A) : Prop :=
  ∃ z : Nat → A, Good M z ∧ Spells z w

theorem live_good (M : Machine Q A H) (w : List A) (hl : Live M w) : GoodWord M w := by
  obtain ⟨z,hz,hw⟩ := hl
  exact (goodWord_iff_stream M w z hw).mpr (hz w.length)

variable [DecidableEq Q] [Fintype Q] [DecidableEq H]
variable (M : Machine Q A H) [DecidablePred M.valid]

theorem suffix_image_positive (w : List A) (hw : GoodWord M w) (a : Nat) :
    0 < (image M (w.drop a)).card := by
  obtain ⟨p,hp⟩ := good_nonempty M w hw
  have hs := suffix_subset M (w.take a) (w.drop a)
  rw [List.take_append_drop] at hs
  exact Finset.card_pos.mpr ⟨p,hs hp⟩

theorem nested_live (w : List A) (hw : GoodWord M w) (a b : Nat)
    (hab : a < b) (hbn : b ≤ w.length)
    (hq : state M w a = state M w b)
    (hp : (w.drop b).IsPrefix (w.drop a))
    (he : (image M (w.drop a)).card = (image M (w.drop b)).card) : Live M w := by
  let d := b-a
  let L := w.length-b
  have hd : 0 < d := by dsimp [d]; omega
  have had : a+d = b := by dsimp [d]; omega
  have hlen : w.length = a+d+L := by dsimp [d,L]; omega
  have hm : WordMatch w a (a+d) L := by
    rw [had]
    exact (P0SuffixConflict.match_iff_prefix w a b hab.le hbn).mpr hp
  have ht : (w.drop a).take (L+d) = w.drop a := by
    apply List.take_of_length_le
    simp only [List.length_drop]
    dsimp [L,d]
    omega
  have hr : (w.drop a).take L = w.drop b := by
    have hh := List.prefix_iff_eq_take.mp hp
    simpa only [List.length_drop] using hh.symm
  have hc : (image M ((w.drop a).take (L+d))).card =
      (image M ((w.drop a).take L)).card := by rwa [ht,hr]
  obtain ⟨z,hg,hz,_⟩ := P0WordMarker.exists_extension M w a d L hd hlen hw hm
    (by rwa [had]) hc
  exact ⟨z,hg,hz⟩

end NSSE.P0ProperLiveness
