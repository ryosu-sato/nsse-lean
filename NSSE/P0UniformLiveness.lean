import NSSE.P0AnnotatedMarkers
import NSSE.P0NestedWords

/-! A uniform bounded period bank preserves every supplied Good history.
The numerical bound depends only on the finite state and letter types. -/
namespace NSSE.P0UniformLiveness
open P0ProperMachine P0ProperWords P0ProperLiveness P0AnnotatedMarkers P0LoopStreams
variable {Q A H : Type*} [DecidableEq Q] [Fintype Q] [DecidableEq A] [Fintype A] [DecidableEq H]

def liveBound (Q A : Type*) [DecidableEq Q] [Fintype Q] [DecidableEq A] [Fintype A] : Nat :=
  P0NestedRepeats.bound (Finset.univ : Finset (Q × A)) (Fintype.card Q^2)

theorem liveBound_positive : 0 < liveBound Q A := P0NestedRepeats.bound_positive _ _

variable (M : Machine Q A H) [DecidablePred M.valid]

theorem bounded_stream (z : Nat → A) (n m : Nat) (hg : GoodUpTo M z n)
    (hlen : m+liveBound Q A ≤ n) : Pumped M z m (m+liveBound Q A) := by
  obtain ⟨a,L,ha,he,hn⟩ := P0NestedSelection.exists_nested Finset.univ (annotated M z)
    (fun _ => Finset.mem_univ _) (Fintype.card Q^2) m
  exact nested_pumps M z n hg m (m+liveBound Q A) a L ha he hlen hn

theorem bounded_word (w : List A) (hw : GoodWord M w) (m : Nat)
    (hlen : m+liveBound Q A ≤ w.length) :
    ∃ a d z, m ≤ a ∧ a+d ≤ m+liveBound Q A ∧ 0 < d ∧ Good M z ∧
      Spells z (w.take m) ∧ Function.Periodic (fun k => z (a+k)) d := by
  have hpos : 0 < w.length := by have := liveBound_positive (Q := Q) (A := A); omega
  let z := P0NestedWords.pad w hpos
  have hz : Spells z w := P0NestedWords.pad_spells w hpos
  have hg : GoodUpTo M z w.length := (goodWord_iff_stream M w z hz).mp hw
  obtain ⟨a,d,z',ha,hd,hdpos,hg',hsp,hper⟩ := bounded_stream M z w.length m hg hlen
  have he : prefixWord z m = w.take m := by
    simpa only [P0LoopStreams.segment,Nat.zero_add,List.drop_zero] using
      P0WordLoop.segment_of_spells w z hz 0 m (by omega)
  exact ⟨a,d,z',ha,hd,hdpos,hg',by rwa [← he],hper⟩

end NSSE.P0UniformLiveness
