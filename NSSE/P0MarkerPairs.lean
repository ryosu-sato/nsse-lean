import NSSE.P0LoopStreams

/-! The pair image at a marker is obtained from actual old origins,
including origins arbitrarily far before the periodic part. -/
namespace NSSE.P0MarkerPairs
open P0ProperMachine P0ProperWords P0SafePairs P0PairImages P0PairStreams P0LoopStreams
variable {Q A H : Type*}

theorem segment_safe (M : Machine Q A H) (z : Nat → A) (a b L : Nat)
    (hm : Match z a b L)
    (hv : ∀ k, k ≤ L → ValidPair M (run M z (a+k),run M z (b+k))) :
    Safe M (segment z b L) (run M z a,run M z b) := by
  apply (safe_iff M _ _).mpr
  intro k hk
  have hkL : k ≤ L := by simpa using hk
  rw [finish_spells M (fun t => z (b+t)) _ (segment_spells z b L) _ k hk,
    matched_pair M z a b k (match_mono z a b L k hkL hm)]
  exact hv k hkL

variable [DecidableEq Q] [Fintype Q] [DecidableEq H]
variable (M : Machine Q A H) [DecidablePred M.valid]

theorem segment_image (z : Nat → A) (a b L : Nat)
    (hm : Match z a b L)
    (hv : ∀ k, k ≤ L → ValidPair M (run M z (a+k),run M z (b+k))) :
    (run M z (a+L),run M z (b+L)) ∈ image M (segment z b L) := by
  apply (mem_image M _ _).mpr
  refine ⟨(run M z a,run M z b),segment_safe M z a b L hm hv,?_⟩
  have he := finish_spells M (fun t => z (b+t)) _ (segment_spells z b L)
    (run M z a,run M z b) L (by simp)
  have ht : (segment z b L).take L = segment z b L := by
    simpa only [segment_length] using (List.take_length (l := segment z b L))
  simpa only [ht,matched_pair M z a b L hm] using he

theorem good_segment_image (z : Nat → A) (n : Nat) (hg : GoodUpTo M z n)
    (i j t L : Nat) (hi : i+t+L ≤ n) (hj : j+t+L ≤ n)
    (hb : M.birth (run M z i) (run M z j) ∨ M.birth (run M z j) (run M z i))
    (hm : Match z i j (t+L)) :
    (run M z (i+t+L),run M z (j+t+L)) ∈ image M (segment z (j+t) L) := by
  apply segment_image M z (i+t) (j+t) L
  · intro k hk
    simpa only [Nat.add_assoc] using hm (t+k) (by omega)
  · intro k hk
    refine ⟨hg.1 _ (by omega),hg.1 _ (by omega),?_⟩
    have hm' := match_mono z i j (t+L) (t+k) (by omega) hm
    rcases hb with hb | hb
    · simpa only [Nat.add_assoc] using hg.2 i (by omega) j (by omega)
        (t+k) (by omega) (by omega) (by omega) hb hm'
    · simpa only [Nat.add_assoc] using (hg.2 j (by omega) i (by omega)
        (t+k) (by omega) (by omega) (by omega) hb (match_symm z i j (t+k) hm')).symm

end NSSE.P0MarkerPairs
