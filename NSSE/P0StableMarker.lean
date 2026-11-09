import NSSE.P0MarkerPairs

/-! Stable-marker pumping on an actual periodic stream. All original
history is retained: origins before the loop are never restarted. -/
namespace NSSE.P0StableMarker
open P0ProperMachine P0ProperWords P0SafePairs P0PairImages P0PairStreams P0LoopStreams
open P0MarkerPairs
variable {Q A H : Type*} [DecidableEq Q] [Fintype Q] [DecidableEq H]
variable (M : Machine Q A H) [DecidablePred M.valid]

theorem small_origins (z : Nat → A) (a d L : Nat) (hd : 0 < d)
    (hp : Function.Periodic (fun k => z (a+k)) d)
    (hg : GoodUpTo M z (a+d+L))
    (hcard : (image M (segment z a (L+d))).card = (image M (segment z a L)).card)
    (i j l : Nat) (hij : i ≤ j) (hj : j < a+d)
    (hb : M.birth (run M z i) (run M z j) ∨ M.birth (run M z j) (run M z i))
    (hm : Match z i j l) : M.head (run M z (i+l)) = M.head (run M z (j+l)) := by
  let n := a+d+L
  by_cases hl : j+l ≤ n
  · rcases hb with hb | hb
    · exact hg.2 i (by dsimp [n] at hl; omega) j (by omega) l
        (by dsimp [n] at hl; omega) (by dsimp [n] at hl; omega) hl hb hm
    · exact (hg.2 j (by omega) i (by dsimp [n] at hl; omega) l
        (by dsimp [n] at hl; omega) hl (by dsimp [n] at hl; omega)
        hb (match_symm z i j l hm)).symm
  · let t := a+d-j
    have ht : j+t = a+d := by dsimp [t]; omega
    have htL : t+L = n-j := by dsimp [t,n]; omega
    have hin : i+t+L ≤ n := by omega
    have hjn : j+t+L = n := by dsimp [n]; omega
    have hiend : i+t+L = i+(n-j) := by omega
    have himg := good_segment_image M z n hg i j t L hin hjn.le hb
      (match_mono z i j l (t+L) (by omega) hm)
    have hr : segment z (a+d) L = segment z a L := by
      apply segment_eq
      intro k _
      simpa only [Nat.add_assoc,Nat.add_comm d k] using hp k
    rw [ht,hr,hiend] at himg
    have hc : 0 < (segment z (a+L) d).length := by simpa using hd
    have hret : ∃ u, segment z a L ++ segment z (a+L) d = u ++ segment z a L :=
      ⟨segment z a d,rotated_suffix z a d L hp⟩
    have hcard' : (image M (segment z a L ++ segment z (a+L) d)).card =
        (image M (segment z a L)).card := by rwa [← segment_append]
    have hcopies : Copies (fun k => z (n+k)) (segment z (a+L) d) :=
      rotation_copies z a d L hp
    have hs := stable_stream M (segment z a L) (segment z (a+L) d) hc hret hcard'
      (fun k => z (n+k)) hcopies (run M z (i+(n-j)),run M z n) himg (l-(n-j))
    have hm' : Match z (i+(n-j)) n (l-(n-j)) := by
      intro k hk
      have he := hm (n-j+k) (by omega)
      simpa only [show j+(n-j+k) = n+k by dsimp [n] at *; omega,
        ← Nat.add_assoc] using he
    rw [matched_pair M z (i+(n-j)) n (l-(n-j)) hm'] at hs
    have he1 : i+(n-j)+(l-(n-j)) = i+l := by omega
    have he2 : n+(l-(n-j)) = j+l := by dsimp [n] at *; omega
    rw [he1,he2] at hs
    exact hs.2.2

theorem good (z : Nat → A) (a d L : Nat) (hd : 0 < d)
    (hp : Function.Periodic (fun k => z (a+k)) d)
    (hq : run M z a = run M z (a+d))
    (hg : GoodUpTo M z (a+d+L))
    (hcard : (image M (segment z a (L+d))).card = (image M (segment z a L)).card) :
    Good M z := by
  apply (good_iff M z).mpr
  constructor
  · intro x
    obtain ⟨i,hi,_,hf⟩ := P0LoopStreams.origin_representative M z a d hd hp hq x
    have he : run M z i = run M z x := by simpa using (hf 0).1
    rw [← he]
    exact hg.1 i (by omega)
  · intro x y l hb hm
    obtain ⟨i,hi,_,hfi⟩ := P0LoopStreams.origin_representative M z a d hd hp hq x
    obtain ⟨j,hj,_,hfj⟩ := P0LoopStreams.origin_representative M z a d hd hp hq y
    have hqi : run M z i = run M z x := by simpa using (hfi 0).1
    have hqj : run M z j = run M z y := by simpa using (hfj 0).1
    have hb' : M.birth (run M z i) (run M z j) := by rwa [hqi,hqj]
    have hm' : Match z i j l := by
      intro k hk
      rw [(hfi k).2,(hfj k).2]
      exact hm k hk
    have he : M.head (run M z (i+l)) = M.head (run M z (j+l)) := by
      by_cases hij : i ≤ j
      · exact small_origins M z a d L hd hp hg hcard i j l hij hj (Or.inl hb') hm'
      · exact (small_origins M z a d L hd hp hg hcard j i l (by omega) hi
          (Or.inr hb') (match_symm z i j l hm')).symm
    rwa [(hfi l).1,(hfj l).1] at he

end NSSE.P0StableMarker
