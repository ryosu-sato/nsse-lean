import NSSE.P0StableMarker
import NSSE.P0WordLoop

/-! Constructive stable-marker pumping from an actual finite Good word.
The produced infinite stream begins with the entire original word. -/
namespace NSSE.P0WordMarker
open P0ProperMachine P0ProperWords P0PairImages P0LoopStreams
variable {Q A H : Type*} [DecidableEq Q] [Fintype Q] [DecidableEq H]
variable (M : Machine Q A H) [DecidablePred M.valid]

theorem pump (w : List A) (a d L : Nat) (hd : 0 < d)
    (hlen : w.length = a+d+L) (hw : GoodWord M w)
    (hm : WordMatch w a (a+d) L)
    (hq : state M w a = state M w (a+d))
    (hcard : (image M ((w.drop a).take (L+d))).card =
      (image M ((w.drop a).take L)).card) :
    Good M (P0WordLoop.stream w a d hd (by omega)) ∧
      Spells (P0WordLoop.stream w a d hd (by omega)) w := by
  let z := P0WordLoop.stream w a d hd (show a+d ≤ w.length by omega)
  have hz : Spells z w := P0WordLoop.spells w a d L hd hlen hm
  refine ⟨?_,hz⟩
  apply P0StableMarker.good M z a d L hd (P0WordLoop.periodic w a d hd (by omega))
  · rwa [← state_eq_run M w z hz a (by omega),
      ← state_eq_run M w z hz (a+d) (by omega)]
  · have hg := (goodWord_iff_stream M w z hz).mp hw
    rwa [hlen] at hg
  · rwa [P0WordLoop.segment_of_spells w z hz a (L+d) (by omega),
      P0WordLoop.segment_of_spells w z hz a L (by omega)]

theorem exists_extension (w : List A) (a d L : Nat) (hd : 0 < d)
    (hlen : w.length = a+d+L) (hw : GoodWord M w)
    (hm : WordMatch w a (a+d) L)
    (hq : state M w a = state M w (a+d))
    (hcard : (image M ((w.drop a).take (L+d))).card =
      (image M ((w.drop a).take L)).card) :
    ∃ z : Nat → A, Good M z ∧ Spells z w ∧
      Function.Periodic (fun k => z (a+k)) d := by
  obtain ⟨hg,hz⟩ := pump M w a d L hd hlen hw hm hq hcard
  exact ⟨P0WordLoop.stream w a d hd (by omega),hg,hz,
    P0WordLoop.periodic w a d hd (by omega)⟩

end NSSE.P0WordMarker
