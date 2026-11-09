import NSSE.MultiVarianceSelectedTrace

/-! The finite branch realizes the supplied signed word literally. All
ray obligations and source consistency transfer through equality of the
actual original spine, without a new semantic realization assumption. -/
namespace NSSE.MultiVarianceSelectedAcceptance
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceWordReader
open MultiVarianceSelectorHead MultiVarianceSelectorTrace MultiVarianceSelectedTrace
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceBranchLetters
open MultiVarianceBranchFactors MultiVarianceBranchSoundness
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

theorem letters_eq (C : Parameters arity n) (hD : ∀ h, arity h≤D) (w : List (Letter arity))
    (hs : ∀ k, ∀ hk : k<w.length,
      choose C.query.constraints (trace pol C.query C.reset C.fallback w k) C.fallback=w[k].1)
    (hl : LocalRun pol C (branch pol C D).initial (indices hD w)) :
    letters pol C (branch pol C D).initial (indices hD w)=w := by
  have hr := local_arities pol C _ _ hl
  have hlen : (letters pol C (branch pol C D).initial (indices hD w)).length=w.length :=
    (letters_length pol C _ _ hr).trans (indices_length hD w)
  apply List.ext_getElem?
  intro k
  by_cases hk : k<w.length
  · apply option_letter_ext
    · rw [letters_current_head pol C _ _ hr k (by rw [indices_length]; exact hk),
        walk_eq pol C hD w hs k (Nat.le_of_lt hk),List.getElem?_eq_getElem hk]
      change some (choose C.query.constraints (trace pol C.query C.reset C.fallback w k) C.fallback)=some w[k].1
      rw [hs k hk]
    · have hi := congrArg (fun z : List Nat => z[k]?) (letters_indices pol C _ _ hr)
      have hm : (indices hD w).map Fin.val=w.map (fun a => a.2.val) := by simp only [indices,List.map_map]; rfl
      rw [hm] at hi
      simpa only [List.getElem?_map] using hi
  · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

theorem spine_eq (C : Parameters arity n) (hD : ∀ h, arity h≤D) (w : List (Letter arity))
    (hs : ∀ k, ∀ hk : k<w.length,
      choose C.query.constraints (trace pol C.query C.reset C.fallback w k) C.fallback=w[k].1)
    (hl : LocalRun pol C (branch pol C D).initial (indices hD w)) :
    MultiVarianceBranchSpine.spine pol C (indices hD w)=make pol C.query w C.endX C.endY := by
  have he := walk_eq pol C hD w hs w.length le_rfl
  have ht : (indices hD w).take w.length=indices hD w := by rw [← indices_length hD w,List.take_length]
  rw [ht] at he
  rw [MultiVarianceBranchSpine.spine,letters_eq pol C hD w hs hl,he]
  rfl

theorem realized (C : Parameters arity n) (hD : ∀ h, arity h≤D) (w : List (Letter arity))
    (hw : w≠[]) (ha : Accepted pol C.query w C.endX C.endY)
    (hs : ∀ k, ∀ hk : k<w.length,
      choose C.query.constraints (trace pol C.query C.reset C.fallback w k) C.fallback=w[k].1)
    (hr : ∀ k, ∀ hk : k<w.length,
      MultiVarianceSelectorHead.Ready C.query.constraints (trace pol C.query C.reset C.fallback w k) w[k].1) :
    inspect pol C (indices hD w)=true := by
  have hl := local_run pol C hD w hw ha hs hr
  rw [inspect_eq_spine_of_complete pol C _ ((complete_iff pol C _).mpr hl),spine_eq pol C hD w hs hl]
  exact (accepted_iff_inspect pol C.query w C.endX C.endY).mp ha

end NSSE.MultiVarianceSelectedAcceptance
