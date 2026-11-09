import NSSE.MultiVarianceSelectedAcceptance
import NSSE.MultiVarianceWordOriginal
import NSSE.MultiVarianceBranchExtraction

/-! Every first nonempty original signed word is covered by the actual
finite reset/head/terminal family. Epsilon is kept as a separate case,
including empty and all-nullary signatures. This is an exact reduction;
it does not yet bound the existential word length. -/
namespace NSSE.MultiVarianceSelectorCoverage
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceWordReader
open MultiVarianceFirstPrefix MultiVarianceFirstTail MultiVarianceSelectorHead
open MultiVarianceSelectorTrace MultiVarianceSelectorReplay MultiVarianceSelectedTrace
open MultiVarianceSelectedAcceptance MultiVarianceBranch MultiVarianceBranchSoundness
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

theorem no_empty_covered (Q : Query arity n) (hD : ∀ h, arity h≤D) (w : List (Letter arity))
    (hw : w≠[]) (ha : Witness pol Q w)
    (hbefore : ∀ k, k<w.length → ¬Empty (frame pol Q w k)) :
    ∃ C : Parameters arity n, C.query=Q ∧ inspect pol C (indices hD w)=true := by
  obtain ⟨ex,ey,ha⟩ := ha
  have hn : 0<w.length := List.length_pos_iff.mpr hw
  let f : H := (w[w.length-1]'(by omega)).1
  let reset := MultiVarianceTokenExact.startFrame pol Q
  have hh := before_head pol Q w ex ey ha.2.2.1 w.length hn le_rfl hbefore
  let C : Parameters arity n := ⟨Q,reset,f,ex,ey⟩
  refine ⟨C,rfl,realized pol C hD w hw ha ?_ ?_⟩
  · intro k hk
    change choose Q.constraints (trace pol Q reset f w k) f=w[k].1
    rw [before_empty pol Q reset f w w.length le_rfl hbefore hh k hk]
    exact hh k hk
  · intro k hk
    change MultiVarianceSelectorHead.Ready Q.constraints (trace pol Q reset f w k) w[k].1
    rw [before_empty pol Q reset f w w.length le_rfl hbefore hh k hk]
    exact proper_ready pol Q w ex ey ha.2.2.1 k hk

theorem first_covered (Q : Query arity n) (hD : ∀ h, arity h≤D) (w : List (Letter arity))
    (hf : First pol Q w) (hw : w≠[]) :
    ∃ C : Parameters arity n, C.query=Q ∧ inspect pol C (indices hD w)=true := by
  classical
  obtain ⟨ex,ey,ha⟩ := hf.1
  by_cases hex : ∃ J, J<w.length ∧ Empty (frame pol Q w J)
  · let J := Nat.find hex
    have hJ : J<w.length := (Nat.find_spec hex).1
    have he : Empty (frame pol Q w J) := (Nat.find_spec hex).2
    have hbefore : ∀ k, k<J → ¬Empty (frame pol Q w k) := by
      intro k hk hek
      exact Nat.find_min hex hk ⟨by omega,hek⟩
    obtain ⟨d,hd,hdJ,hc⟩ := first_period pol Q w hf ex ey ha J hJ he
    let f : H := (w[J-1]'(by omega)).1
    have hh := before_head pol Q w ex ey ha.2.2.1 J (by omega) (by omega) hbefore
    let C : Parameters arity n := ⟨Q,frame pol Q w (J-d),f,ex,ey⟩
    refine ⟨C,rfl,realized pol C hD w hw ha ?_ ?_⟩
    · intro k hk
      exact replay_head pol Q w f J d hJ hd hdJ hbefore hh he hc k hk
    · intro k hk
      exact replay_ready pol Q w ex ey ha.2.2.1 f J d hJ hd hdJ hbefore hh he hc k hk
  · have hbefore : ∀ k, k<w.length → ¬Empty (frame pol Q w k) := by
      intro k hk he
      exact hex ⟨k,hk,he⟩
    exact no_empty_covered pol Q hD w hw ⟨ex,ey,ha⟩ hbefore

theorem not_entails_iff_parameters (Q : Query arity n) (hD : ∀ h, arity h≤D) :
    ¬MultiVarianceConstraints.Entails pol Q ↔ Witness pol Q [] ∨
      ∃ C : Parameters arity n, C.query=Q ∧ ∃ w : List (Fin D), inspect pol C w=true := by
  constructor
  · intro hn
    obtain ⟨w,hf⟩ := (MultiVarianceWordOriginal.not_entails_iff_first pol Q).mp hn
    by_cases hw : w=[]
    · exact Or.inl (hw ▸ hf.1)
    · obtain ⟨C,hq,hi⟩ := first_covered pol Q hD w hf hw
      exact Or.inr ⟨C,hq,indices hD w,hi⟩
  · rintro (he | ⟨C,hq,w,hi⟩)
    · exact (MultiVarianceWordOriginal.not_entails_iff_word pol Q).mpr ⟨[],he⟩
    · rw [← hq]
      exact not_entails_of_inspect pol C w hi

omit [DecidableEq H] in
theorem no_words_of_nullary (hz : ∀ h, arity h=0) (w : List (Letter arity)) : w=[] := by
  cases w with
  | nil => rfl
  | cons a w => have h := a.2.isLt; have hz' := hz a.1; omega

theorem nullary_not_entails_iff (Q : Query arity n) (hz : ∀ h, arity h=0) :
    ¬MultiVarianceConstraints.Entails pol Q ↔ Witness pol Q [] := by
  rw [MultiVarianceWordOriginal.not_entails_iff_word]
  constructor
  · rintro ⟨w,hw⟩
    simpa only [no_words_of_nullary hz w] using hw
  · intro hw
    exact ⟨[],hw⟩

variable [Fintype H]

theorem first_family (Q : Query arity n) (w : List (Letter arity)) (hf : First pol Q w) (hw : w≠[]) :
    MultiVarianceBranchExtraction.inspectAny pol Q
      (indices (MultiVarianceBranchFamily.arity_le_alphabet (arity:=arity)) w)=true :=
  (MultiVarianceBranchExtraction.inspectAny_correct pol Q _).mpr
    (first_covered pol Q MultiVarianceBranchFamily.arity_le_alphabet w hf hw)

theorem not_entails_iff_family (Q : Query arity n) :
    ¬MultiVarianceConstraints.Entails pol Q ↔ Witness pol Q [] ∨
      ∃ w : List (Fin (MultiVarianceBranchFamily.alphabetSize arity)),
        MultiVarianceBranchExtraction.inspectAny pol Q w=true := by
  rw [not_entails_iff_parameters pol Q MultiVarianceBranchFamily.arity_le_alphabet]
  constructor
  · rintro (he | ⟨C,hq,w,hi⟩)
    · exact Or.inl he
    · exact Or.inr ⟨w,(MultiVarianceBranchExtraction.inspectAny_correct pol Q w).mpr ⟨C,hq,hi⟩⟩
  · rintro (he | ⟨w,hi⟩)
    · exact Or.inl he
    · obtain ⟨C,hq,hc⟩ := (MultiVarianceBranchExtraction.inspectAny_correct pol Q w).mp hi
      exact Or.inr ⟨C,hq,w,hc⟩

end NSSE.MultiVarianceSelectorCoverage
