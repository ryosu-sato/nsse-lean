import NSSE.P0DDeadTrace
import NSSE.P0CutComparison
import Mathlib.Data.Fintype.Option

/-! Actual proper colouring of the ordered whole-suffix conflict graph.
The colour type has exactly |Q|+1 members, including the unique terminal.
D-deadness enters through the proved uniqueness of the terminal position.
-/
namespace NSSE.P0DDeadColor
open P0DDeadReader P0DDeadTrace P0CutComparison P0ProperWords
variable {Q A H : Type*}

theorem equal_state_compatible (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (hne : a ≠ b) (hs : trace J w a = trace J w b) :
    Compatible w (leftAt J w) (rightAt J w) a b := by
  intro l hl hal hbl hm
  have he := trace_equal J w a b l hal hbl hs hm
  have haend : a+l < w.length := by
    by_contra h
    have hae : a+l = w.length := by omega
    have ht : trace J w (b+l) = some none := by rw [← he,hae,complete_trace J w hc]
    have hbe := (terminal_iff J w hc (b+l) hbl).mp ht
    exact hne (by omega)
  obtain ⟨q,hq⟩ := trace_proper J w hc (a+l) haend
  unfold leftAt rightAt
  rw [← he,hq]

def color (J : Reader Q A H) (w : List A) (k : Nat) : Option Q :=
  match trace J w k with
  | some q => q
  | none => none

theorem trace_color (J : Reader Q A H) (w : List A) (hc : Complete J w) (k : Nat) :
    trace J w k = some (color J w k) := by
  cases he : trace J w k with
  | none => exact False.elim (trace_ne_failure J w hc k he)
  | some q => simp only [color,he]

theorem terminal_color_iff (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (k : Nat) (hk : k ≤ w.length) : color J w k = none ↔ k = w.length := by
  rw [← terminal_iff J w hc k hk,trace_color J w hc k,Option.some.injEq]

def Adjacent (J : Reader Q A H) (w : List A) (a b : Nat) : Prop :=
  ¬ Compatible w (leftAt J w) (rightAt J w) a b ∨
    ¬ Compatible w (leftAt J w) (rightAt J w) b a

theorem proper_coloring (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (a b : Nat) (hne : a ≠ b) (he : color J w a = color J w b) : ¬ Adjacent J w a b := by
  have hs : trace J w a = trace J w b := by rw [trace_color J w hc a,trace_color J w hc b,he]
  rintro (h | h)
  · exact h (equal_state_compatible J w hc a b hne hs)
  · exact h (equal_state_compatible J w hc b a hne.symm hs.symm)

theorem color_count [Fintype Q] [DecidableEq Q] (J : Reader Q A H) (w : List A) :
    (Finset.univ.image (fun k : Fin (w.length+1) => color J w k)).card ≤ Fintype.card Q+1 := by
  simpa using (Finset.card_le_univ
    (Finset.univ.image (fun k : Fin (w.length+1) => color J w k)))

end NSSE.P0DDeadColor
