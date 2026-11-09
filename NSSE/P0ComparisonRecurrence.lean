import NSSE.P0CutComparison

/-! Exact endpoint and one-letter recurrences for the finite comparison.
These are the local join/union rules used by the actual suffix trie. -/
namespace NSSE.P0ComparisonRecurrence
open P0CutComparison P0ProperWords
variable {A H : Type*}

theorem end_left (w : List A) (left right : Nat → H) (b : Nat) (hb : b ≤ w.length) :
    Compatible w left right w.length b ↔ left w.length = right b := by
  constructor
  · exact compatible_head w left right w.length b (by omega) hb
  · intro he l _ hal _ _
    have hl : l = 0 := by omega
    simpa only [hl,Nat.add_zero] using he

theorem end_right (w : List A) (left right : Nat → H) (a : Nat) (ha : a ≤ w.length) :
    Compatible w left right a w.length ↔ left a = right w.length := by
  constructor
  · exact compatible_head w left right a w.length ha (by omega)
  · intro he l _ _ hbl _
    have hl : l = 0 := by omega
    simpa only [hl,Nat.add_zero] using he

theorem step_iff (w : List A) (left right : Nat → H) (a b : Nat)
    (ha : a < w.length) (hb : b < w.length) :
    Compatible w left right a b ↔ left a = right b ∧
      (w[a]? = w[b]? → Compatible w left right (a+1) (b+1)) := by
  constructor
  · intro hc
    exact ⟨compatible_head w left right a b (by omega) (by omega) hc,
      fun he => compatible_tail w left right a b he hc⟩
  · rintro ⟨hhead,htail⟩ l hl hal hbl hm
    cases l with
    | zero => simpa using hhead
    | succ l =>
      have he : w[a]? = w[b]? := by simpa only [Nat.add_zero] using hm 0 (by omega)
      have hm' : WordMatch w (a+1) (b+1) l := by
        intro k hk
        simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hm (k+1) (by omega)
      have hh := htail he l (by omega) (by omega) (by omega) hm'
      simpa only [Nat.add_assoc,Nat.add_comm 1 l] using hh

end NSSE.P0ComparisonRecurrence
