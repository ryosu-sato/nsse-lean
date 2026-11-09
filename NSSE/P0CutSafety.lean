import NSSE.P0CutComparison

/-! The actual reader-word consequence of all-position entry dominance.
Off-diagonal comparisons use forward simulation. Diagonal births cannot
occur in an accepted word with distinct terminal labels and are handled
explicitly, rather than deleted from the statement. -/
namespace NSSE.P0CutSafety
open P0DDeadReader P0ProperWords P0MarkerComparison P0WordCuts P0CutComparison
variable {Q A H : Type*}

theorem no_diagonal (J : Reader Q A H) (w : List A) (hends : J.endX ≠ J.endY)
    (hw : Accepted J w) (a : Nat) (ha : a ≤ w.length) : ¬ bornAt J w a a := by
  intro hb
  have he := hw.2 a ha a ha (w.length-a) (by omega) (by omega) (by omega) hb (fun _ _ => rfl)
  rw [show a+(w.length-a) = w.length by omega] at he
  unfold leftAt rightAt at he
  rw [complete_trace J w hw.1] at he
  exact hends he

theorem compatible_of_accepted (J : Reader Q A H) (w : List A) (hw : Accepted J w)
    (a b : Nat) (ha : a ≤ w.length) (hb : b ≤ w.length) (hborn : bornAt J w a b) :
    Compatible w (leftAt J w) (rightAt J w) a b :=
  fun l hl hal hbl hm => hw.2 a ha b hb l hl hal hbl hborn hm

theorem accepted_cut {w : List A} {n : Nat} (C : Cut w n) (J : Reader Q A H)
    (hends : J.endX ≠ J.endY) (hw : Accepted J w) (hloop : C.Loops J)
    (hentry : Entry C (leftAt J w) (rightAt J w)) : Accepted J C.word := by
  refine ⟨C.complete_word J hloop hw.1,?_⟩
  intro a ha b hb l hl hal hbl hborn hm
  have han : a ≤ n := by simpa using ha
  have hbn : b ≤ n := by simpa using hb
  have hborn' := (C.born_word J hloop a b han hbn).mp hborn
  have hne : a ≠ b := by
    intro he
    subst b
    exact no_diagonal J w hends hw (C.lift a) (C.lift_le a han) hborn'
  have hc := compatible_of_accepted J w hw (C.lift a) (C.lift b)
    (C.lift_le a han) (C.lift_le b hbn) hborn'
  have hn := pair_preservation C (leftAt J w) (rightAt J w) hentry a b hne hc
  have hh := hn l hl hal hbl hm
  rw [C.left_word J hloop (a+l) (by simpa using hal),
    C.right_word J hloop (b+l) (by simpa using hbl)]
  exact hh

end NSSE.P0CutSafety
