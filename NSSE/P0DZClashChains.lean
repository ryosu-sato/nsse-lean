import NSSE.P0DZFirstClash

/-! The global first-clash argument on actual suffix chains: at most
one chain origin precedes the later birth, and later origins have
distinct aligned states, all different from the chain's own state. -/
namespace NSSE.P0DZClashChains
open P0DZBranch P0DZTrace P0DZVirtualTrace P0DZFirstClash P0ProperWords P0SuffixRank
variable {Q Z A H : Type*}

theorem no_two_early (J : Branch Q Z A H) (w : List A) (hf : FirstUnsafe J w)
    (a b l : Nat) (hab : a < b) (hend : b+l = w.length) (h : Clash J w a b l)
    (u v : Nat) (huv : Linked J w u v) (hvb : v ≤ b) : False := by
  have huvlt := huv.1
  let b' := u+(b-v)
  have hcopy := states_of_proper J w (u+(b-v)) b (linked_states J w u v huv b hvb (by omega))
  have hendcopy := states_of_proper J w (u+(w.length-v)) w.length
    (linked_states J w u v huv w.length (by omega) (by omega))
  have hidx : u+(w.length-v) = b'+l := by dsimp [b']; omega
  rw [hidx] at hendcopy
  have hnew : Clash J w a b' l := by
    refine ⟨h.left_bound,by dsimp [b']; omega,?_,?_,?_⟩
    · change Born J (dState J w a) (dState J w (u+(b-v)))
      rw [hcopy]
      exact h.born
    · intro k hk
      have hh := linked_letters J w u v huv (b+k) (by omega) (by omega)
      have hkidx : u+(b+k-v) = b'+k := by dsimp [b']; omega
      rw [hkidx] at hh
      exact (h.letters k hk).trans hh.symm
    · rw [hendcopy]
      simpa only [hend] using h.bad
  exact no_earlier J w hf a b' l (by omega) (by dsimp [b']; omega) hnew

def aligned (J : Branch Q Z A H) (w : List A) (a b c : Nat) : Q := dState J w (a+(c-b))

theorem aligned_ne_self (J : Branch Q Z A H) (w : List A) (hc : DComplete J w)
    (a b l : Nat) (hab : a < b) (hend : b+l = w.length) (h : Clash J w a b l)
    (c : Nat) (hbc : b ≤ c) (hcn : c ≤ w.length) : aligned J w a b c ≠ dState J w c := by
  intro he
  have hm : WordMatch w (a+(c-b)) c (w.length-c) := by
    intro k hk
    have hh := h.letters (c-b+k) (by omega)
    simpa only [Nat.add_assoc,show b+(c-b+k) = c+k by omega] using hh
  have hh := matched_states J w hc (a+(c-b)) c (w.length-c) (by omega) (by omega) he hm
  have hleft : a+(c-b)+(w.length-c) = a+l := by omega
  have hright : c+(w.length-c) = b+l := by omega
  rw [hleft,hright] at hh
  exact h.bad (congrArg J.head hh)

theorem aligned_distinct (J : Branch Q Z A H) (w : List A) (hf : FirstUnsafe J w)
    (a b l : Nat) (hab : a < b) (hend : b+l = w.length) (h : Clash J w a b l)
    (c d : Nat) (hbc : b ≤ c) (hcd : Linked J w c d) : aligned J w a b c ≠ aligned J w a b d := by
  intro he
  have horder := hcd.1
  have hdn := hcd.2.1
  let k := c-b+(w.length-d)
  have hm : WordMatch w (a+(c-b)) (a+(d-b)) (w.length-d) := by
    intro i hi
    have hc := h.letters (c-b+i) (by omega)
    have hd := h.letters (d-b+i) (by omega)
    have hh := linked_match J w c d hcd i hi
    have hci : b+(c-b+i) = c+i := by omega
    have hdi : b+(d-b+i) = d+i := by omega
    rw [hci] at hc
    rw [hdi] at hd
    simpa only [Nat.add_assoc] using hc.trans (hh.trans hd.symm)
  have hleft := matched_states J w hf.complete (a+(c-b)) (a+(d-b)) (w.length-d)
    (by omega) (by omega) he hm
  have hright := states_of_proper J w (c+(w.length-d)) w.length
    (linked_states J w c d hcd w.length (by omega) (by omega))
  have hli : a+(c-b)+(w.length-d) = a+k := by dsimp [k]; omega
  have hlj : a+(d-b)+(w.length-d) = a+l := by omega
  have hri : c+(w.length-d) = b+k := by dsimp [k]; omega
  rw [hli,hlj] at hleft
  rw [hri,← hend] at hright
  have hnew : Clash J w a b k := by
    refine ⟨by dsimp [k]; omega,by dsimp [k]; omega,h.born,?_,?_⟩
    · exact fun i hi => h.letters i (by dsimp [k] at hi; omega)
    · rw [hleft,hright]
      exact h.bad
  exact no_earlier J w hf a b k (by dsimp [k]; omega) (by dsimp [k]; omega) hnew

end NSSE.P0DZClashChains
