import NSSE.P0DZCutTrace
import NSSE.P0RelationalCut
import NSSE.P0FamilyWordCut

/-! Full four-rail Entry preserves actual D/Z safety. Literal cut words
retain the original final letter, final ID and all state-based births. -/
namespace NSSE.P0DZCutSafety
open P0DZBranch P0DZTrace P0DZCutTrace P0WordCuts
variable {Q Z A H : Type*} {w : List A} {n : Nat}

def FullEntry (C : Cut w n) (J : Branch Q Z A H) : Prop :=
  ∀ s t, P0RelationalCut.Entry Agree C (labelAt J w s) (labelAt J w t)

theorem compatible_transport (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hl : Loops C J) (he : FullEntry C J) (a b : Nat) (hne : a ≠ b) (s t : Bool)
    (hcomp : Compatible J w (C.lift a) s (C.lift b) t) : Compatible J C.word a s b t := by
  have hh := P0RelationalCut.pair_preservation Agree C (labelAt J w s) (labelAt J w t)
    (he s t) a b hne hcomp
  intro l hlen ha hb hm
  have hal : a+l ≤ n := by simpa using ha
  have hbl : b+l ≤ n := by simpa using hb
  rw [label_transport C J hc hl (a+l) hal s,label_transport C J hc hl (b+l) hbl t]
  exact hh l hlen ha hb hm

theorem accepted_cut (C : Cut w n) (J : Branch Q Z A H) (hends : J.endX ≠ J.endY)
    (hw : Accepted J w) (hl : Loops C J) (he : FullEntry C J) : Accepted J C.word := by
  refine ⟨complete_cut C J hw.1 hl,?_⟩
  intro a ha b hb s t hdistinct hborn
  have han : a ≤ n := by simpa using ha
  have hbn : b ≤ n := by simpa using hb
  have hborn' := (born_transport C J hw.1 hl a b han hbn s t).mp hborn
  by_cases hab : a = b
  · subst b
    have hst : s ≠ t := hdistinct.resolve_left (by simp)
    exact False.elim (no_diagonal_cross J w hends hw (C.lift a) (C.lift_le a han) s t hst hborn')
  · have hne : C.lift a ≠ C.lift b := fun hh => hab (C.lift_injective a b han hbn hh)
    exact compatible_transport C J hw.1 hl he a b hab s t
      (hw.2 (C.lift a) (C.lift_le a han) (C.lift b) (C.lift_le b hbn) s t (Or.inl hne) hborn')

theorem family_loops (J : Branch Q Z A H) (w : List A) (F : P0IntervalFamily.Family w.length)
    (hl : ∀ b ∈ F.intervals, stateAt J w b.1 = stateAt J w b.2) :
    Loops (P0FamilyWordCut.cut w F) J := by
  intro k hk
  by_cases hs : (P0FamilyWordCut.cut w F).source k = (P0FamilyWordCut.cut w F).lift k
  · rw [hs]
  · obtain ⟨b,hb,he,ht⟩ := (P0FamilyWordCut.seams_exact w F k hk).mp hs
    rw [he,ht]
    exact hl b hb

theorem accepted_family (J : Branch Q Z A H) (w : List A) (F : P0IntervalFamily.Family w.length)
    (hne : F.intervals ≠ []) (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hl : ∀ b ∈ F.intervals, stateAt J w b.1 = stateAt J w b.2)
    (he : FullEntry (P0FamilyWordCut.cut w F) J) :
    Accepted J (P0FamilyWordCut.cut w F).word ∧ (P0FamilyWordCut.cut w F).word.length < w.length :=
  ⟨accepted_cut _ J hends hw (family_loops J w F hl) he,P0FamilyWordCut.shorter w F hne⟩

end NSSE.P0DZCutSafety
