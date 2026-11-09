import NSSE.P0SuffixConflict

/-! The virtual all-D path includes a proper endpoint at length(w).
Nested equal-state suffixes copy its letters and states to earlier
positions, including that endpoint. No safety assumption is used. -/
namespace NSSE.P0DZVirtualTrace
open P0DZBranch P0DZTrace P0SuffixConflict P0SuffixRank P0ProperWords
variable {Q Z A H : Type*}

def DComplete (J : Branch Q Z A H) (w : List A) : Prop :=
  (properAt J w w.length).isSome = true

theorem d_prefix (J : Branch Q Z A H) (w : List A) (hc : DComplete J w)
    (k : Nat) : ∃ q, properAt J w k = some q := by
  have hs := proper_append J J.initial (w.take k) (w.drop k)
  rw [List.take_append_drop] at hs
  unfold DComplete properAt at hc
  rw [List.take_length,hs] at hc
  cases he : properFrom J J.initial (w.take k) with
  | none => simp [he] at hc
  | some q => exact ⟨q,he⟩

theorem d_succ (J : Branch Q Z A H) (w : List A) (hc : DComplete J w)
    (k : Nat) (hk : k < w.length) (q : Q) (hq : properAt J w k = some q) :
    ∃ r, J.next q w[k] = some r := by
  obtain ⟨r,hr⟩ := d_prefix J w hc (k+1)
  rw [proper_succ J w k hk,hq] at hr
  exact ⟨r,hr⟩

theorem linked_match (J : Branch Q Z A H) (w : List A) (a b : Nat)
    (hab : Linked J w a b) : WordMatch w a b (w.length-b) :=
  (match_iff_prefix w a b (Nat.le_of_lt hab.1) (Nat.le_of_lt hab.2.1)).mpr hab.2.2.2

theorem linked_states (J : Branch Q Z A H) (w : List A) (a b : Nat)
    (hab : Linked J w a b) (k : Nat) (hk : b ≤ k) (hkn : k ≤ w.length) :
    properAt J w (a+(k-b)) = properAt J w k := by
  have horder := hab.1
  have hm := linked_match J w a b hab
  have hh := proper_equal J w a b (k-b) (by omega) (by omega) hab.2.2.1
    (fun i hi => hm i (by omega))
  simpa only [Nat.add_sub_of_le hk] using hh

theorem linked_letters (J : Branch Q Z A H) (w : List A) (a b : Nat)
    (hab : Linked J w a b) (k : Nat) (hk : b ≤ k) (hkn : k < w.length) :
    w[a+(k-b)]? = w[k]? := by
  have hh := linked_match J w a b hab (k-b) (by omega)
  simpa only [Nat.add_sub_of_le hk] using hh

end NSSE.P0DZVirtualTrace
