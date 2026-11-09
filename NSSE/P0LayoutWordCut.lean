import NSSE.P0FamilyWordCut
import NSSE.P0LayoutReader

/-! The intervals selected by a signed layout now produce an actual
strictly shorter complete reader word. The all-position Entry proof for
four union children is a separate condition, not inferred from loops. -/
namespace NSSE.P0LayoutWordCut
open P0HomogeneousOrder P0SignedLayout P0LayoutCuts P0LayoutReader
open P0IntervalFamily P0FamilyWordCut P0DDeadReader
variable {Q A H : Type*} {m : Nat}

def family (G : Grid m) {lo hi : Nat} {L : List (Nat × Bool)} (h : Layout G lo hi L)
    (hhi : hi ≤ m) (n : Nat) (hb : ∀ r i, i < m → G.pos r i ≤ n) : Family n where
  intervals := L.map (fun b => (source G b,target G b))
  valid := by
    intro d hd
    obtain ⟨b,hbL,rfl⟩ := List.mem_map.mp hd
    have hh := boundary_bounds G h b hbL
    exact ⟨intervals_ordered G h b hbL,hb (targetGroup b.2) (b.1-1) (by omega)⟩
  separated := by
    rw [List.pairwise_map]
    exact intervals_separated G h

theorem family_nonempty (G : Grid m) {lo hi : Nat} {L : List (Nat × Bool)} (h : Layout G lo hi L)
    (hhi : hi ≤ m) (n : Nat) (hb : ∀ r i, i < m → G.pos r i ≤ n) (hne : lo < hi) :
    (family G h hhi n hb).intervals ≠ [] := by
  have hh : L ≠ [] := fun he => Nat.ne_of_lt hne ((layout_empty_iff G h).mp he)
  intro he
  exact hh (List.map_eq_nil_iff.mp he)

theorem family_loops (J : Reader Q A H) (w : List A) (hc : Complete J w) (G : Grid m)
    {lo hi : Nat} {L : List (Nat × Bool)} (h : Layout G lo hi L) (hhi : hi ≤ m)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length) (hu : UniformStates J w G) :
    ∀ d ∈ (family G h hhi w.length hb).intervals, trace J w d.1 = trace J w d.2 := by
  intro d hd
  obtain ⟨b,hbL,rfl⟩ := List.mem_map.mp hd
  have hh := boundary_bounds G h b hbL
  exact interval_loop J w hc G hu b (by omega)

theorem shorter_complete (J : Reader Q A H) (w : List A) (hc : Complete J w) (G : Grid m)
    {lo hi : Nat} {L : List (Nat × Bool)} (h : Layout G lo hi L) (hhi : hi ≤ m)
    (hb : ∀ r i, i < m → G.pos r i ≤ w.length) (hu : UniformStates J w G) (hne : lo < hi) :
    Complete J (cut w (family G h hhi w.length hb)).word ∧
      (cut w (family G h hhi w.length hb)).word.length < w.length :=
  ⟨complete_word J w _ hc (family_loops J w hc G h hhi hb hu),
    shorter w _ (family_nonempty G h hhi _ hb hne)⟩

end NSSE.P0LayoutWordCut
