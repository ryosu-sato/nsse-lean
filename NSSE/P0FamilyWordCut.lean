import NSSE.P0IntervalMap
import NSSE.P0CutSafety

/-! The actual word produced by deleting a separated interval family.
The finite retained-position enumeration instantiates the previously
certified word construction and all-position comparison simulation. -/
namespace NSSE.P0FamilyWordCut
open P0IntervalFamily P0WordCuts P0DDeadReader P0CutComparison P0CutSafety
variable {Q A H : Type*}

def cut (w : List A) (F : Family w.length) : Cut w (P0IntervalMap.length F) where
  lift := P0IntervalMap.lift F
  increasing := P0IntervalMap.lift_increasing F
  terminal := P0IntervalMap.terminal F

theorem source_cut (w : List A) (F : Family w.length) (k : Nat) :
    (cut w F).source k = P0IntervalMap.source F k := by cases k <;> rfl

theorem retains_iff (w : List A) (F : Family w.length) (p : Nat) (hp : p < w.length) :
    (∃ k, k < P0IntervalMap.length F ∧ (cut w F).lift k = p) ↔ ¬ Removed F p := by
  constructor
  · rintro ⟨k,hk,hkp⟩
    have hh := (mem_kept F _).mp (P0IntervalMap.lift_mem F k (by omega))
    simpa only [← hkp] using hh.2
  · intro h
    obtain ⟨k,hk,hkp⟩ := P0IntervalMap.lift_surjective F p ((mem_kept F _).mpr ⟨by omega,h⟩)
    have hlt : k < P0IntervalMap.length F := by
      by_contra hn
      have he : k = P0IntervalMap.length F := by omega
      rw [he,P0IntervalMap.terminal] at hkp
      omega
    exact ⟨k,hlt,hkp⟩

theorem seams_exact (w : List A) (F : Family w.length) (k : Nat) (hk : k ≤ P0IntervalMap.length F) :
    Seam (cut w F) k ↔ ∃ b ∈ F.intervals, (cut w F).source k = b.1 ∧ (cut w F).lift k = b.2 := by
  simp only [Seam,source_cut]
  constructor
  · exact P0IntervalMap.seam_interval F k hk
  · rintro ⟨b,hb,hs,ht⟩ he
    have hv := F.valid b hb
    have he' : b.1 = b.2 := hs.symm.trans (he.trans ht)
    omega

theorem every_interval (w : List A) (F : Family w.length) (b : Nat × Nat) (hb : b ∈ F.intervals) :
    ∃ k, k ≤ P0IntervalMap.length F ∧ (cut w F).source k = b.1 ∧ (cut w F).lift k = b.2 := by
  simpa only [source_cut] using P0IntervalMap.interval_seam F b hb

theorem loops (J : Reader Q A H) (w : List A) (F : Family w.length)
    (hl : ∀ b ∈ F.intervals, trace J w b.1 = trace J w b.2) : (cut w F).Loops J := by
  intro k hk
  by_cases hs : (cut w F).source k = (cut w F).lift k
  · rw [hs]
  · obtain ⟨b,hb,he,ht⟩ := (seams_exact w F k hk).mp hs
    rw [he,ht]
    exact hl b hb

theorem shorter (w : List A) (F : Family w.length) (hne : F.intervals ≠ []) :
    (cut w F).word.length < w.length := by
  rw [Cut.word_length]
  have hh := kept_card_lt F hne
  have hp := kept_card_pos F
  unfold P0IntervalMap.length
  omega

theorem complete_word (J : Reader Q A H) (w : List A) (F : Family w.length) (hc : Complete J w)
    (hl : ∀ b ∈ F.intervals, trace J w b.1 = trace J w b.2) : Complete J (cut w F).word :=
  (cut w F).complete_word J (loops J w F hl) hc

theorem accepted_word (J : Reader Q A H) (w : List A) (F : Family w.length)
    (hne : F.intervals ≠ []) (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hl : ∀ b ∈ F.intervals, trace J w b.1 = trace J w b.2)
    (he : Entry (cut w F) (leftAt J w) (rightAt J w)) :
    Accepted J (cut w F).word ∧ (cut w F).word.length < w.length :=
  ⟨accepted_cut (cut w F) J hends hw (loops J w F hl) he,shorter w F hne⟩

end NSSE.P0FamilyWordCut
