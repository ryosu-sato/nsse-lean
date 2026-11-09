import NSSE.P0WordCuts

/-! All-position entry dominance gives exact forward comparison simulation.
The proof restarts at each consumed letter using the old suffix predicate;
it does not assume that one local seam test decides new-word safety. -/
namespace NSSE.P0CutComparison
open P0ProperWords P0WordCuts P0DDeadReader P0MarkerComparison
variable {Q A H : Type*}

def Compatible (w : List A) (left right : Nat → H) (a b : Nat) : Prop :=
  ∀ l, l ≤ w.length → a+l ≤ w.length → b+l ≤ w.length → WordMatch w a b l →
    left (a+l) = right (b+l)

theorem compatible_head (w : List A) (left right : Nat → H) (a b : Nat)
    (ha : a ≤ w.length) (hb : b ≤ w.length) (h : Compatible w left right a b) : left a = right b := by
  simpa only [Nat.add_zero] using h 0 (by omega) ha hb (fun k hk => by omega)

theorem compatible_tail (w : List A) (left right : Nat → H) (a b : Nat)
    (he : w[a]? = w[b]?) (h : Compatible w left right a b) :
    Compatible w left right (a+1) (b+1) := by
  intro l hl hal hbl hm
  have hm' : WordMatch w a b (l+1) := by
    intro k hk
    cases k with
    | zero => simpa only [Nat.add_zero] using he
    | succ k => simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hm k (by omega)
  have hh := h (l+1) (by omega) (by omega) (by omega) hm'
  simpa only [Nat.add_assoc,Nat.add_comm 1 l] using hh

def Seam {w : List A} {n : Nat} (C : Cut w n) (k : Nat) : Prop := C.source k ≠ C.lift k

def Entry {w : List A} {n : Nat} (C : Cut w n) (left right : Nat → H) : Prop :=
  ∀ a, a ≤ n → ∀ b, b ≤ n → a ≠ b → (Seam C a ∨ Seam C b) →
    Compatible w left right (C.source a) (C.source b) →
      Compatible w left right (C.lift a) (C.lift b)

theorem entry_apply {w : List A} {n : Nat} (C : Cut w n) (left right : Nat → H)
    (he : Entry C left right) (a b : Nat) (ha : a ≤ n) (hb : b ≤ n) (hne : a ≠ b)
    (hc : Compatible w left right (C.source a) (C.source b)) :
    Compatible w left right (C.lift a) (C.lift b) := by
  by_cases hs : Seam C a ∨ Seam C b
  · exact he a ha b hb hne hs hc
  · have hsa : C.source a = C.lift a := by by_contra h; exact hs (Or.inl h)
    have hsb : C.source b = C.lift b := by by_contra h; exact hs (Or.inr h)
    simpa only [hsa,hsb] using hc

/-- The all-position noncreation theorem, for every ordered off-diagonal
pair, independently of whether that pair is a birth. -/
theorem pair_preservation {w : List A} {n : Nat} (C : Cut w n) (left right : Nat → H)
    (he : Entry C left right) (a b : Nat) (hne : a ≠ b)
    (hc : Compatible w left right (C.lift a) (C.lift b)) :
    Compatible C.word (left ∘ C.lift) (right ∘ C.lift) a b := by
  intro l hl hal hbl hm
  have hal' : a+l ≤ n := by simpa using hal
  have hbl' : b+l ≤ n := by simpa using hbl
  clear hal hbl hl
  induction l generalizing a b with
  | zero =>
    exact compatible_head w left right (C.lift a) (C.lift b)
      (C.lift_le a (by omega)) (C.lift_le b (by omega)) hc
  | succ l ih =>
    have han : a < n := by omega
    have hbn : b < n := by omega
    have hletter : w[C.lift a]? = w[C.lift b]? := by
      have hh := hm 0 (by omega)
      simpa only [Nat.add_zero,C.word_getElem? a han,C.word_getElem? b hbn] using hh
    have hs := compatible_tail w left right (C.lift a) (C.lift b) hletter hc
    have ht := entry_apply C left right he (a+1) (b+1) (by omega) (by omega) (by omega) hs
    have hm' : WordMatch C.word (a+1) (b+1) l := by
      intro k hk
      simpa only [Nat.add_assoc,Nat.add_comm 1 k] using hm (k+1) (by omega)
    have hfinal := ih (a+1) (b+1) (by omega) ht hm' (by omega) (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm 1 l] using hfinal

end NSSE.P0CutComparison
