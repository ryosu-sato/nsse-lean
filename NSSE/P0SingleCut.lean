import NSSE.P0CutSafety

/-! An actual nonempty interval deletion instantiates the retained-position
construction. Only the equal-state loop and the all-position dominance test
are required for preserving an accepted word; the test is not assumed for
arbitrary same-state intervals. -/
namespace NSSE.P0SingleCut
open P0DDeadReader P0WordCuts P0CutComparison P0CutSafety
variable {Q A H : Type*}

def single (w : List A) (a b : Nat) (hab : a < b) (hb : b ≤ w.length) :
    Cut w (w.length-(b-a)) where
  lift k := if k < a then k else k+(b-a)
  increasing i j hij _ := by split_ifs <;> omega
  terminal := by split_ifs <;> omega

theorem source_single (w : List A) (a b : Nat) (hab : a < b) (hb : b ≤ w.length) (k : Nat) :
    (single w a b hab hb).source k =
      if k = a then a else (single w a b hab hb).lift k := by
  cases k with
  | zero => dsimp [Cut.source,single]; split_ifs <;> omega
  | succ k => dsimp [Cut.source,single]; split_ifs <;> omega

theorem loops_single (J : Reader Q A H) (w : List A) (a b : Nat)
    (hab : a < b) (hb : b ≤ w.length) (he : trace J w a = trace J w b) :
    (single w a b hab hb).Loops J := by
  intro k _
  rw [source_single]
  by_cases hk : k = a
  · subst k
    simp only [if_pos rfl,single,lt_self_iff_false,if_false]
    simpa only [show a+(b-a) = b by omega] using he
  · rw [if_neg hk]

theorem shorter (w : List A) (a b : Nat) (hab : a < b) (hb : b ≤ w.length) :
    (single w a b hab hb).word.length < w.length := by
  rw [Cut.word_length]
  omega

theorem word_single (w : List A) (a b : Nat) (hab : a < b) (hb : b ≤ w.length) :
    (single w a b hab hb).word = w.take a ++ w.drop b := by
  have ha : a ≤ w.length := by omega
  have hlen : (w.take a).length = a := by simp [List.length_take,Nat.min_eq_left ha]
  apply List.ext_getElem
  · simp only [Cut.word_length,List.length_append,hlen,List.length_drop]
    omega
  · intro k hk hk'
    have hkn : k < w.length-(b-a) := by simpa using hk
    rw [Cut.word_get _ k hkn]
    by_cases hka : k < a
    · rw [List.getElem_append_left (by simpa [hlen] using hka)]
      simp only [single,if_pos hka,List.getElem_take]
    · rw [List.getElem_append_right (by rw [hlen]; omega),List.getElem_drop]
      simp only [single,if_neg hka,hlen]
      congr 1
      omega

theorem accepted_single (J : Reader Q A H) (w : List A) (a b : Nat)
    (hab : a < b) (hb : b ≤ w.length) (hends : J.endX ≠ J.endY) (hw : Accepted J w)
    (hloop : trace J w a = trace J w b)
    (he : Entry (single w a b hab hb) (leftAt J w) (rightAt J w)) :
    Accepted J (single w a b hab hb).word ∧ (single w a b hab hb).word.length < w.length :=
  ⟨accepted_cut _ J hends hw (loops_single J w a b hab hb hloop) he,shorter w a b hab hb⟩

end NSSE.P0SingleCut
