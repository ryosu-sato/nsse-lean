import NSSE.P0UniformLiveness

/-! Uniform full-history liveness is equivalent to one explicit finite
extension level, and every live history has a bounded periodic continuation. -/
namespace NSSE.P0UniformContinuation
open P0ProperMachine P0ProperWords P0ProperLiveness P0LoopStreams P0UniformLiveness
variable {Q A H : Type*} [DecidableEq Q] [Fintype Q] [DecidableEq A] [Fintype A] [DecidableEq H]
variable (M : Machine Q A H) [DecidablePred M.valid]

theorem long_extension (u v : List A) (hw : GoodWord M (u++v))
    (hlen : liveBound Q A ≤ v.length) :
    ∃ a d z, u.length ≤ a ∧ a+d ≤ u.length+liveBound Q A ∧ 0 < d ∧ Good M z ∧
      Spells z u ∧ Function.Periodic (fun k => z (a+k)) d := by
  have h := bounded_word M (u++v) hw u.length (by simp only [List.length_append]; omega)
  simpa only [List.take_left] using h

omit [DecidableEq H] [DecidablePred M.valid] in
theorem live_has_level (u : List A) (hl : Live M u) :
    ∃ v : List A, v.length = liveBound Q A ∧ GoodWord M (u++v) := by
  obtain ⟨z,hg,hz⟩ := hl
  have hu : prefixWord z u.length = u := by
    have he := P0WordLoop.segment_of_spells u z hz 0 u.length (by omega)
    simpa only [P0LoopStreams.segment,Nat.zero_add,List.drop_zero,List.take_length] using he
  refine ⟨segment z u.length (liveBound Q A),segment_length ..,?_⟩
  have he : prefixWord z (u.length+liveBound Q A) =
      u ++ segment z u.length (liveBound Q A) := by
    have hs := segment_append z 0 u.length (liveBound Q A)
    simpa only [P0LoopStreams.segment,Nat.zero_add,hu] using hs
  rw [← he]
  exact (goodWord_prefix M z _).mpr (hg _)

theorem live_iff_level (u : List A) :
    Live M u ↔ ∃ v : List A, v.length = liveBound Q A ∧ GoodWord M (u++v) := by
  constructor
  · exact live_has_level M u
  · rintro ⟨v,hv,hw⟩
    obtain ⟨_,_,z,_,_,_,hg,hz,_⟩ := long_extension M u v hw hv.ge
    exact ⟨z,hg,hz⟩

theorem live_periodic (u : List A) (hl : Live M u) :
    ∃ a d z, u.length ≤ a ∧ a+d ≤ u.length+liveBound Q A ∧ 0 < d ∧ Good M z ∧
      Spells z u ∧ Function.Periodic (fun k => z (a+k)) d := by
  obtain ⟨v,hv,hw⟩ := live_has_level M u hl
  exact long_extension M u v hw hv.ge

theorem nonlive_height (u v : List A) (hn : ¬Live M u) (hw : GoodWord M (u++v)) :
    v.length < liveBound Q A := by
  by_contra h
  obtain ⟨_,_,z,_,_,_,hg,hz,_⟩ := long_extension M u v hw (by omega)
  exact hn ⟨z,hg,hz⟩

end NSSE.P0UniformContinuation
