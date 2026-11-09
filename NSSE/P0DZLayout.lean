import NSSE.P0DZSingleCut
import NSSE.P0LayoutSeams

/-! Homogeneous position rows with equal refined D/Z colors supply the
actual state loops for the signed multi-interval layout. -/
namespace NSSE.P0DZLayout
open P0DZBranch P0DZRankColor P0DZSingleCut P0HomogeneousOrder P0SignedLayout P0LayoutCuts
open P0LayoutWordCut
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A] {m : Nat}

def UniformColors (J : Branch Q Z A H) (w : List A) (G : Grid m) : Prop :=
  ∀ r s i, i < m → color J w (G.pos r i) = color J w (G.pos s i)

theorem positions_proper (J : Branch Q Z A H) (w : List A) (hc : Complete J w) (G : Grid m)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length) (hu : UniformColors J w G)
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

theorem family_states (J : Branch Q Z A H) (w : List A) (hc : Complete J w) (G : Grid m)
    {lo hi : Nat} {L : List (Nat × Bool)} (h : Layout G lo hi L) (hhi : hi ≤ m)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length) (hu : UniformColors J w G) :
    ∀ d ∈ (family G h hhi w.length hb).intervals, stateAt J w d.1 = stateAt J w d.2 := by
  intro d hd
  obtain ⟨b,hbL,rfl⟩ := List.mem_map.mp hd
  have hh := boundary_bounds G h b hbL
  have hk : b.1-1 < m := by omega
  exact state_of_color J w hc (source G b) (target G b)
    (hb (sourceGroup b.2) _ hk) (hb (targetGroup b.2) _ hk)
    (hu (sourceGroup b.2) (targetGroup b.2) _ hk)

end NSSE.P0DZLayout
