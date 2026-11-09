import NSSE.P0ProperWords

/-! Finite-word determinism and harmless birth erasure, with no extension
of a finite word to an arbitrarily chosen infinite stream. -/
namespace NSSE.P0ProperWordLemmas
open P0ProperMachine P0ProperWords
variable {Q A H : Type*}

theorem state_step (M : Machine Q A H) (w : List A) (k : Nat) (hk : k < w.length) :
    state M w (k+1) = M.step (state M w k) w[k] := by
  simp only [state,List.take_succ_eq_append_getElem hk,List.foldl_append,
    List.foldl_cons,List.foldl_nil]

theorem match_mono (w : List A) (a b l k : Nat) (hkl : k ≤ l)
    (hm : WordMatch w a b l) : WordMatch w a b k := fun i hi => hm i (by omega)

theorem state_equal (M : Machine Q A H) (w : List A) (a b l : Nat)
    (ha : a+l ≤ w.length) (hb : b+l ≤ w.length)
    (hs : state M w a = state M w b) (hm : WordMatch w a b l) :
    state M w (a+l) = state M w (b+l) := by
  induction l with
  | zero => simpa using hs
  | succ l ih =>
    have hal : a+l < w.length := by omega
    have hbl : b+l < w.length := by omega
    have he : w[a+l] = w[b+l] := by
      simpa only [List.getElem?_eq_getElem hal,List.getElem?_eq_getElem hbl,Option.some.injEq]
        using hm l (by omega)
    rw [Nat.add_succ,Nat.add_succ,state_step M w (a+l) hal,state_step M w (b+l) hbl,
      ih (by omega) (by omega) (match_mono w a b (l+1) l (by omega) hm),he]

@[simp] theorem state_eraseEqual (M : Machine Q A H) (w : List A) (k : Nat) :
    state (eraseEqual M) w k = state M w k := rfl

theorem goodWord_eraseEqual (M : Machine Q A H) (w : List A) :
    GoodWord (eraseEqual M) w ↔ GoodWord M w := by
  simp only [GoodWord,state_eraseEqual]
  simp only [eraseEqual]
  constructor
  · rintro ⟨hv,hr⟩
    refine ⟨hv,?_⟩
    intro a ha b hb l hl hal hbl hborn hm
    by_cases he : state M w a = state M w b
    · exact congrArg M.head (state_equal M w a b l hal hbl he hm)
    · exact hr a ha b hb l hl hal hbl ⟨hborn,he⟩ hm
  · rintro ⟨hv,hr⟩
    exact ⟨hv,fun a ha b hb l hl hal hbl hborn hm =>
      hr a ha b hb l hl hal hbl hborn.1 hm⟩

end NSSE.P0ProperWordLemmas
