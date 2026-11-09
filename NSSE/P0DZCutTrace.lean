import NSSE.P0DZTrace
import NSSE.P0WordCuts
import Mathlib.Data.List.TakeDrop

/-! Literal cuts in full D/Z paths. Same-state loops force the final
letter to survive, and preserve its actual final state ID. -/
namespace NSSE.P0DZCutTrace
open P0DZBranch P0DZTrace P0WordCuts
variable {Q Z A H : Type*} {w : List A} {n : Nat}

def Loops (C : Cut w n) (J : Branch Q Z A H) : Prop :=
  ∀ k, k ≤ n → stateAt J w (C.source k) = stateAt J w (C.lift k)

theorem source_le_lift (C : Cut w n) (k : Nat) (hk : k ≤ n) : C.source k ≤ C.lift k := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k => exact Nat.succ_le_of_lt (C.increasing k (k+1) (by omega) hk)

theorem loops_proper (C : Cut w n) (J : Branch Q Z A H) (hl : Loops C J)
    (k : Nat) (hk : k < n) : properAt J w (C.source k) = properAt J w (C.lift k) := by
  have ht := C.lift_lt k hk
  have hs := source_le_lift C k (by omega)
  have he := hl k (by omega)
  rw [proper_state J w (C.source k) (by omega),proper_state J w (C.lift k) ht] at he
  exact Option.map_injective (fun a b h => Sum.inl.inj h) he

theorem terminal_source (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hl : Loops C J) : C.source n = w.length := by
  obtain ⟨z,hz⟩ := complete_terminal J w hc
  have he := hl n le_rfl
  rw [C.terminal,terminal_state,hz] at he
  exact terminal_unique J w (C.source n) (C.source_le n le_rfl) z he

theorem positive_length (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hl : Loops C J) : 0 < n := by
  have he := terminal_source C J hc hl
  have hp := List.length_pos_iff.mpr (complete_nonempty J w hc)
  cases n with
  | zero => change 0 = w.length at he; omega
  | succ n => omega

theorem last_lift (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hl : Loops C J) : C.lift (n-1) = w.length-1 := by
  have hn := positive_length C J hc hl
  have he := terminal_source C J hc hl
  cases n with
  | zero => omega
  | succ k => change C.lift k+1 = w.length at he; simpa using (Nat.sub_eq_of_eq_add he.symm).symm

theorem proper_transport (C : Cut w n) (J : Branch Q Z A H) (hl : Loops C J)
    (k : Nat) (hk : k < n) : properAt J C.word k = properAt J w (C.lift k) := by
  induction k with
  | zero => exact loops_proper C J hl 0 hk
  | succ k ih =>
    have hkn : k < n := by omega
    rw [proper_succ J C.word k (by simpa using hkn),ih hkn,C.word_get k hkn,
      ← proper_succ J w (C.lift k) (C.lift_lt k hkn)]
    exact loops_proper C J hl (k+1) hk

theorem terminal_last (J : Branch Q Z A H) (v : List A) (hv : 0 < v.length) :
    terminal J v = (properAt J v (v.length-1)).bind
      (fun q => J.final q (v[v.length-1]'(by omega))) := by
  have he : v.take (v.length-1) ++ [v[v.length-1]'(by omega)] = v := by
    have hh := List.take_concat_get' v (v.length-1) (by omega)
    simpa only [Nat.sub_add_cancel (show 1 ≤ v.length by omega),List.take_length] using hh
  change finishFrom J J.initial v = _
  conv_lhs => rw [← he]
  exact finish_append J J.initial (v.take (v.length-1)) _

theorem terminal_transport (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hl : Loops C J) : terminal J C.word = terminal J w := by
  have hn := positive_length C J hc hl
  have hw := List.length_pos_iff.mpr (complete_nonempty J w hc)
  rw [terminal_last J C.word (by simpa using hn),terminal_last J w hw]
  simp only [Cut.word_length]
  rw [proper_transport C J hl (n-1) (by omega),C.word_get (n-1) (by omega)]
  simp only [last_lift C J hc hl]

theorem complete_cut (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hl : Loops C J) : Complete J C.word := by
  unfold Complete
  rw [terminal_transport C J hc hl]
  exact hc

theorem state_transport (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hl : Loops C J) (k : Nat) (hk : k ≤ n) : stateAt J C.word k = stateAt J w (C.lift k) := by
  by_cases he : k = n
  · subst k
    have hend : stateAt J C.word n = (terminal J C.word).map Sum.inr := by
      simpa only [C.word_length] using terminal_state J C.word
    rw [hend,C.terminal,terminal_state,terminal_transport C J hc hl]
  · have hkn : k < n := by omega
    rw [proper_state J C.word k (by simpa using hkn),proper_state J w (C.lift k) (C.lift_lt k hkn)]
    exact congrArg (Option.map Sum.inl) (proper_transport C J hl k hkn)

theorem label_transport (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hl : Loops C J) (k : Nat) (hk : k ≤ n) (s : Bool) :
    labelAt J C.word s k = labelAt J w s (C.lift k) := by
  unfold labelAt
  rw [state_transport C J hc hl k hk]

theorem born_transport (C : Cut w n) (J : Branch Q Z A H) (hc : Complete J w)
    (hl : Loops C J) (a b : Nat) (ha : a ≤ n) (hb : b ≤ n) (s t : Bool) :
    bornAt J C.word a s b t ↔ bornAt J w (C.lift a) s (C.lift b) t := by
  simp only [bornAt,state_transport C J hc hl a ha,state_transport C J hc hl b hb]

end NSSE.P0DZCutTrace
