import NSSE.P0SingleCut
import NSSE.P0DDeadColor
import Mathlib.Data.Finset.Max

/-! A module gives an actual interval shortening, not just a graph
retraction. The interval endpoints need equal reader states. Every other
retained position lies outside the module, so its external comparisons
provide the complete all-position entry certificate. -/
namespace NSSE.P0ModuleCut
open P0DDeadReader P0WordCuts P0CutComparison P0SingleCut P0DDeadColor
variable {Q A H : Type*}

theorem entry_of_external (w : List A) (left right : Nat → H) (a b : Nat)
    (hab : a < b) (hb : b ≤ w.length)
    (hext : ∀ z, z ≤ w.length → (z < a ∨ b < z) →
      (Compatible w left right a z ↔ Compatible w left right b z) ∧
      (Compatible w left right z a ↔ Compatible w left right z b)) :
    Entry (single w a b hab hb) left right := by
  let C := single w a b hab hb
  have hsource (k : Nat) (hk : k ≠ a) : C.source k = C.lift k := by
    simp only [C,source_single,if_neg hk]
  have hseam (k : Nat) (hk : Seam C k) : k = a := by
    by_contra h
    exact hk (hsource k h)
  have htarget : C.lift a = b := by
    simp only [C,single,lt_self_iff_false,if_false]
    omega
  have horigin : C.source a = a := by simp [C,source_single]
  have hout (k : Nat) (hk : k ≠ a) : C.lift k < a ∨ b < C.lift k := by
    dsimp [C,single]
    split_ifs <;> omega
  intro i hi j hj hij hs hcomp
  change Compatible w left right (C.lift i) (C.lift j)
  change Compatible w left right (C.source i) (C.source j) at hcomp
  rcases hs with hs | hs
  · have he := hseam i hs
    subst i
    have hja : j ≠ a := Ne.symm hij
    rw [horigin,hsource j hja] at hcomp
    rw [htarget]
    exact (hext (C.lift j) (C.lift_le j hj) (hout j hja)).1.mp hcomp
  · have he := hseam j hs
    subst j
    rw [horigin,hsource i hij] at hcomp
    rw [htarget]
    exact (hext (C.lift i) (C.lift_le i hi) (hout i hij)).2.mp hcomp

/-- The external-color rule on an actual bounded set of word positions. -/
def ColoredModule (J : Reader Q A H) (w : List A) (S : Finset Nat) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, color J w a = color J w b → ∀ z, z ≤ w.length → z ∉ S →
    (Compatible w (leftAt J w) (rightAt J w) a z ↔
      Compatible w (leftAt J w) (rightAt J w) b z) ∧
    (Compatible w (leftAt J w) (rightAt J w) z a ↔
      Compatible w (leftAt J w) (rightAt J w) z b)

theorem shorten_extremes (J : Reader Q A H) (w : List A) (S : Finset Nat)
    (hm : ColoredModule J w S) (a b : Nat) (ha : a ∈ S) (hb : b ∈ S)
    (hlo : ∀ z ∈ S, a ≤ z) (hhi : ∀ z ∈ S, z ≤ b)
    (hab : a < b) (hbn : b ≤ w.length)
    (hcol : color J w a = color J w b)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) :
    Accepted J (w.take a ++ w.drop b) ∧ (w.take a ++ w.drop b).length < w.length := by
  have hext : ∀ z, z ≤ w.length → (z < a ∨ b < z) →
      (Compatible w (leftAt J w) (rightAt J w) a z ↔
        Compatible w (leftAt J w) (rightAt J w) b z) ∧
      (Compatible w (leftAt J w) (rightAt J w) z a ↔
        Compatible w (leftAt J w) (rightAt J w) z b) := by
    intro z hz hout
    apply hm a ha b hb hcol z hz
    intro hzin
    have := hlo z hzin
    have := hhi z hzin
    omega
  have hloop : trace J w a = trace J w b := by
    rw [trace_color J w hw.1 a,trace_color J w hw.1 b,hcol]
  simpa only [word_single] using accepted_single J w a b hab hbn hends hw hloop
    (entry_of_external w (leftAt J w) (rightAt J w) a b hab hbn hext)

theorem one_color_shorten (J : Reader Q A H) (w : List A) (S : Finset Nat)
    (hm : ColoredModule J w S) (hbound : ∀ z ∈ S, z ≤ w.length)
    (hone : ∀ a ∈ S, ∀ b ∈ S, color J w a = color J w b)
    (hsize : 1 < S.card) (hends : J.endX ≠ J.endY) (hw : Accepted J w) :
    ∃ v, Accepted J v ∧ v.length < w.length := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  let a := S.min' hne
  let b := S.max' hne
  have ha : a ∈ S := S.min'_mem hne
  have hb : b ∈ S := S.max'_mem hne
  exact ⟨w.take a ++ w.drop b,shorten_extremes J w S hm a b ha hb
    (fun z hz => S.min'_le z hz) (fun z hz => S.le_max' z hz)
    (S.min'_lt_max'_of_card hsize) (hbound b hb) (hone a ha b hb) hends hw⟩

theorem shortest_one_color (J : Reader Q A H) (w : List A) (S : Finset Nat)
    (hm : ColoredModule J w S) (hbound : ∀ z ∈ S, z ≤ w.length)
    (hone : ∀ a ∈ S, ∀ b ∈ S, color J w a = color J w b)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hmin : ∀ v, Accepted J v → w.length ≤ v.length) : S.card ≤ 1 := by
  by_contra h
  obtain ⟨v,hv,hlen⟩ := one_color_shorten J w S hm hbound hone (by omega) hends hw
  have := hmin v hv
  omega

end NSSE.P0ModuleCut
