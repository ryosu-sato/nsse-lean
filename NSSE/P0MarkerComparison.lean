import NSSE.P0ProperWordLemmas

/-! The literal fresh-marker argument, including every birth and comparison
offset. A marker at the end prevents distinct old origins from reaching a
terminal comparison. Equal old states must be erased before unequal terminal
heads are attached. No short-witness or recognition assumption is used here. -/
namespace NSSE.P0MarkerComparison
open P0ProperMachine P0ProperWords
variable {Q A H : Type*}

def Safe (w : List A) (left right : Nat → H) (born : Nat → Nat → Prop) : Prop :=
  ∀ a, a ≤ w.length → ∀ b, b ≤ w.length → ∀ l, l ≤ w.length →
    a+l ≤ w.length → b+l ≤ w.length → born a b → WordMatch w a b l →
    left (a+l) = right (b+l)

def marked (w : List A) : List (Option A) := w.map some ++ [none]

@[simp] theorem marked_length (w : List A) : (marked w).length = w.length+1 := by
  simp [marked]

theorem marked_get_old (w : List A) (k : Nat) (hk : k < w.length) :
    (marked w)[k]? = some (some w[k]) := by
  simp [marked,List.getElem?_append, hk, List.getElem?_eq_getElem]

theorem marked_get_end (w : List A) : (marked w)[w.length]? = some none := by
  simp [marked,List.getElem?_append]

theorem marked_none_iff (w : List A) (k : Nat) (hk : k < (marked w).length) :
    (marked w)[k]? = some none ↔ k = w.length := by
  by_cases hkn : k < w.length
  · rw [marked_get_old w k hkn]
    constructor
    · intro h
      cases h
    · intro h
      omega
  · have he : k = w.length := by rw [marked_length] at hk; omega
    subst k
    exact ⟨fun _ => rfl,fun _ => marked_get_end w⟩

theorem marked_match_iff (w : List A) (a b l : Nat)
    (ha : a+l ≤ w.length) (hb : b+l ≤ w.length) :
    WordMatch (marked w) a b l ↔ WordMatch w a b l := by
  constructor <;> intro hm k hk
  · have he := hm k hk
    rw [marked_get_old w (a+k) (by omega),marked_get_old w (b+k) (by omega)] at he
    simpa only [List.getElem?_eq_getElem (by omega : a+k < w.length),
      List.getElem?_eq_getElem (by omega : b+k < w.length),Option.some.injEq] using he
  · have he := hm k hk
    rw [marked_get_old w (a+k) (by omega),marked_get_old w (b+k) (by omega)]
    simpa only [List.getElem?_eq_getElem (by omega : a+k < w.length),
      List.getElem?_eq_getElem (by omega : b+k < w.length),Option.some.injEq] using he

/-- An old-origin comparison reaching the new endpoint must be diagonal. -/
theorem ending_match_diagonal (w : List A) (a b l : Nat)
    (ha : a ≤ w.length) (hb : b ≤ w.length)
    (hal : a+l ≤ w.length+1) (hbl : b+l ≤ w.length+1)
    (hend : a+l = w.length+1 ∨ b+l = w.length+1)
    (hm : WordMatch (marked w) a b l) : a = b := by
  have hl : 0 < l := by omega
  have he := hm (l-1) (by omega)
  rcases hend with h | h
  · have heq : a+(l-1) = w.length := by omega
    rw [heq,marked_get_end] at he
    have hbe := (marked_none_iff w (b+(l-1)) (by simp only [marked_length]; omega)).mp he.symm
    omega
  · have heq : b+(l-1) = w.length := by omega
    rw [heq,marked_get_end] at he
    have hae := (marked_none_iff w (a+(l-1)) (by simp only [marked_length]; omega)).mp he
    omega

def born (M : Machine Q A H) (w : List A) (a b : Nat) : Prop :=
  a ≤ w.length ∧ b ≤ w.length ∧ M.birth (state M w a) (state M w b) ∧
    state M w a ≠ state M w b

def endpoint (M : Machine Q A H) (w : List A) (side : Bool) (k : Nat) : H ⊕ Bool :=
  if k ≤ w.length then Sum.inl (M.head (state M w k)) else Sum.inr side

def MarkedSafe (M : Machine Q A H) (w : List A) : Prop :=
  Safe (marked w) (endpoint M w false) (endpoint M w true) (born M w)

theorem markedSafe_of_good (M : Machine Q A H) (w : List A) (hg : GoodWord M w) :
    MarkedSafe M w := by
  intro a ha b hb l hl hal hbl hborn hm
  obtain ⟨hao,hbo,hbirth,hne⟩ := hborn
  have hal' : a+l ≤ w.length+1 := by simpa using hal
  have hbl' : b+l ≤ w.length+1 := by simpa using hbl
  have hends : a+l ≤ w.length ∧ b+l ≤ w.length := by
    by_contra h
    have hd := ending_match_diagonal w a b l hao hbo hal' hbl' (by omega) hm
    exact hne (hd ▸ rfl)
  obtain ⟨haend,hbend⟩ := hends
  have he := hg.2 a hao b hbo l (by omega) haend hbend hbirth
    ((marked_match_iff w a b l haend hbend).mp hm)
  simpa only [endpoint,if_pos haend,if_pos hbend,Sum.inl.injEq] using he

theorem good_of_markedSafe (M : Machine Q A H) (w : List A)
    (hv : ∀ k, k ≤ w.length → M.valid (state M w k)) (hs : MarkedSafe M w) :
    GoodWord M w := by
  refine ⟨hv,?_⟩
  intro a ha b hb l hl hal hbl hbirth hm
  by_cases he : state M w a = state M w b
  · exact congrArg M.head (P0ProperWordLemmas.state_equal M w a b l hal hbl he hm)
  · have hsafe := hs a (by simp only [marked_length]; omega) b (by simp only [marked_length]; omega)
      l (by simp only [marked_length]; omega) (by simp only [marked_length]; omega)
      (by simp only [marked_length]; omega) ⟨ha,hb,hbirth,he⟩
      ((marked_match_iff w a b l hal hbl).mpr hm)
    simpa only [endpoint,if_pos hal,if_pos hbl,Sum.inl.injEq] using hsafe

theorem markedSafe_iff (M : Machine Q A H) (w : List A) :
    ((∀ k, k ≤ w.length → M.valid (state M w k)) ∧ MarkedSafe M w) ↔ GoodWord M w :=
  ⟨fun h => good_of_markedSafe M w h.1 h.2,fun h => ⟨h.1,markedSafe_of_good M w h⟩⟩

end NSSE.P0MarkerComparison
