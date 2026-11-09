import NSSE.P0LayoutCuts
import NSSE.P0DDeadColor

/-! The selected layout intervals lie strictly before the actual terminal
and are equal-state loops when the four position lists have one common
state profile. This prepares the literal multi-interval word operation. -/
namespace NSSE.P0LayoutReader
open P0HomogeneousOrder P0SignedLayout P0LayoutCuts P0DDeadReader P0DDeadColor
variable {Q A H : Type*} {m : Nat}

def UniformStates (J : Reader Q A H) (w : List A) (G : Grid m) : Prop :=
  ∀ r s i, i < m → color J w (G.pos r i) = color J w (G.pos s i)

theorem positions_proper (J : Reader Q A H) (w : List A) (hc : Complete J w) (G : Grid m)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length) (hu : UniformStates J w G)
    (r : Fin 4) (i : Nat) (hi : i < m) : G.pos r i < w.length := by
  have hr := hb r i hi
  by_contra h
  have he : G.pos r i = w.length := by omega
  let s : Fin 4 := if r = 0 then 1 else 0
  have hrs : r ≠ s := by
    dsimp [s]
    split_ifs with h0
    · subst r; decide
    · exact h0
  have ht : color J w (G.pos r i) = none := (terminal_color_iff J w hc _ hr).mpr he
  have hts : color J w (G.pos s i) = none := by rw [← hu r s i hi]; exact ht
  have hes := (terminal_color_iff J w hc _ (hb s i hi)).mp hts
  exact G.apart r s hrs i i hi hi (he.trans hes.symm)

theorem interval_loop (J : Reader Q A H) (w : List A) (hc : Complete J w) (G : Grid m)
    (hu : UniformStates J w G) (b : Nat × Bool) (hb : b.1-1 < m) :
    trace J w (source G b) = trace J w (target G b) := by
  rw [trace_color J w hc,trace_color J w hc]
  congr 1
  exact hu (sourceGroup b.2) (targetGroup b.2) (b.1-1) hb

theorem prepared_intervals (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (G : Grid m) (hm : 0 < m) (hb : ∀ r i, i < m → G.pos r i ≤ w.length)
    (hu : UniformStates J w G) :
    ∃ L, Layout G 0 m L ∧ L ≠ [] ∧
      L.Pairwise (fun b d => target G b < source G d) ∧
      (∀ b ∈ L, source G b < target G b ∧ target G b < w.length ∧
        trace J w (source G b) = trace J w (target G b)) ∧
      ∀ r k, (r = 1 ∨ r = 2) → k < m →
        Removed G L (G.pos r k) ∨ TargetCoordinate L r k := by
  obtain ⟨L,hL,hlen,hempty⟩ := whole_layout G
  refine ⟨L,hL,fun h => (Nat.ne_of_gt hm) (hempty.mp h),intervals_separated G hL,?_,?_⟩
  · intro b hmem
    have hcoord := boundary_bounds G hL b hmem
    have hk : b.1-1 < m := by omega
    exact ⟨intervals_ordered G hL b hmem,
      positions_proper J w hc G hb hu (targetGroup b.2) (b.1-1) hk,
      interval_loop J w hc G hu b hk⟩
  · intro r k hr hk
    exact middle_covered G hL le_rfl r k hr (Nat.zero_le _) hk

end NSSE.P0LayoutReader
