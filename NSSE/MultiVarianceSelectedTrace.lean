import NSSE.MultiVarianceSelectorReplay
import NSSE.MultiVarianceBranchSoundness

/-! Erase supplied heads to the actual finite child alphabet. When the
selector reproduces these heads, the actual branch walk has exactly the
original raw frame and the independent selector frame at every position. -/
namespace NSSE.MultiVarianceSelectedTrace
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceSelectorHead MultiVarianceSelectorStep MultiVarianceWordReader
open MultiVarianceWordEmptyTail MultiVarianceSelectorTrace
open MultiVarianceBranch MultiVarianceBranchLocal MultiVarianceBranchLetters
variable {H : Type*} {arity : H → Nat} {n D : Nat}

def indices (hD : ∀ h, arity h≤D) (w : List (Letter arity)) : List (Fin D) :=
  w.map (fun a => ⟨a.2.val,lt_of_lt_of_le a.2.isLt (hD a.1)⟩)

theorem indices_length (hD : ∀ h, arity h≤D) (w : List (Letter arity)) :
    (indices hD w).length=w.length := List.length_map _

theorem indices_take (hD : ∀ h, arity h≤D) (w : List (Letter arity)) (k : Nat) :
    (indices hD w).take k=indices hD (w.take k) := by simp only [indices,List.map_take]

theorem indices_get (hD : ∀ h, arity h≤D) (w : List (Letter arity))
    (k : Nat) (hk : k<w.length) :
    ((indices hD w)[k]'(by rw [indices_length]; exact hk)).val=w[k].2.val := by
  simp only [indices,List.getElem_map]

variable [DecidableEq H] (pol : Polarity arity)

theorem walk_eq (C : Parameters arity n) (hD : ∀ h, arity h≤D) (w : List (Letter arity))
    (hs : ∀ k, ∀ hk : k<w.length,
      choose C.query.constraints (trace pol C.query C.reset C.fallback w k) C.fallback=w[k].1)
    (k : Nat) (hk : k≤w.length) :
    walk pol C (branch pol C D).initial ((indices hD w).take k) =
      (frame pol C.query w k,trace pol C.query C.reset C.fallback w k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k<w.length := by omega
    have hki : k<(indices hD w).length := by rw [indices_length]; exact hkn
    rw [List.take_succ_eq_append_getElem hki]
    change (List.foldl (fun t (i : Fin D) => successor pol C t i.val) _ _)=_
    rw [List.foldl_append,List.foldl_cons,List.foldl_nil]
    change successor pol C (walk pol C (branch pol C D).initial ((indices hD w).take k))
      (indices hD w)[k].val=_
    rw [ih (by omega),indices_get]
    apply Prod.ext
    · change step pol C.query.constraints (frame pol C.query w k)
        (choose C.query.constraints (trace pol C.query C.reset C.fallback w k) C.fallback) w[k].2.val=_
      rw [hs k hkn,step_valid]
      exact (frame_succ pol C.query w k hkn).symm
    · exact (trace_succ pol C.query C.reset C.fallback w k hkn).symm

theorem local_run (C : Parameters arity n) (hD : ∀ h, arity h≤D) (w : List (Letter arity))
    (hw : w≠[]) (ha : Accepted pol C.query w C.endX C.endY)
    (hs : ∀ k, ∀ hk : k<w.length,
      choose C.query.constraints (trace pol C.query C.reset C.fallback w k) C.fallback=w[k].1)
    (hr : ∀ k, ∀ hk : k<w.length,
      MultiVarianceSelectorHead.Ready C.query.constraints (trace pol C.query C.reset C.fallback w k) w[k].1) :
    LocalRun pol C (branch pol C D).initial (indices hD w) := by
  apply (local_iff_pointwise pol C _ _).mpr
  refine ⟨?_,?_,?_⟩
  · intro he
    have hh := congrArg List.length he
    rw [indices_length] at hh
    exact hw (List.length_eq_zero_iff.mp hh)
  · intro k hk
    have hkn : k<w.length := by simpa only [indices_length] using hk
    rw [walk_eq pol C hD w hs k (Nat.le_of_lt hkn),indices_get]
    change (MultiVarianceSelectorHead.Ready C.query.constraints _ _ ∧
      MultiVarianceSelectorHead.Ready C.query.constraints _ _) ∧ _
    change (MultiVarianceSelectorHead.Ready C.query.constraints _
      (choose C.query.constraints (trace pol C.query C.reset C.fallback w k) C.fallback) ∧ _) ∧ _
    simp only [output,hs k hkn]
    exact ⟨⟨proper_ready pol C.query w C.endX C.endY ha.2.2.1 k hkn,hr k hkn⟩,w[k].2.isLt⟩
  · have he := walk_eq pol C hD w hs w.length le_rfl
    have ht : (indices hD w).take w.length=indices hD w := by rw [← indices_length hD w,List.take_length]
    rw [ht] at he
    rw [he]
    have hx := ha.2.2.1 w.length le_rfl false
    have hy := ha.2.2.1 w.length le_rfl true
    simp only [value,List.getElem?_length,roleOf,tokensOf,Bool.false_eq_true,if_false,if_true] at hx hy
    exact ⟨hx,hy,ha.1⟩

end NSSE.MultiVarianceSelectedTrace
