import NSSE.P0SignedLayout

/-! Literal position intervals selected from a homogeneous four-list
layout. Their endpoints are strictly ordered and separated; every middle
list position is removed or is one of the prescribed target entries. -/
namespace NSSE.P0LayoutCuts
open P0HomogeneousOrder P0SignedLayout
variable {m : Nat}

def sourceGroup (s : Bool) : Fin 4 := if s then 0 else 3
def targetGroup (s : Bool) : Fin 4 := if s then 2 else 1
def source (G : Grid m) (b : Nat × Bool) : Nat := G.pos (sourceGroup b.2) (b.1-1)
def target (G : Grid m) (b : Nat × Bool) : Nat := G.pos (targetGroup b.2) (b.1-1)

def Removed (G : Grid m) (L : List (Nat × Bool)) (p : Nat) : Prop :=
  ∃ b ∈ L, source G b ≤ p ∧ p < target G b

def TargetCoordinate (L : List (Nat × Bool)) (r : Fin 4) (k : Nat) : Prop :=
  ∃ b ∈ L, k = b.1-1 ∧ r = targetGroup b.2

theorem block_ordered (G : Grid m) (lo mid : Nat) (s : Bool) (hlo : lo < mid)
    (hb : Block G lo mid s) : source G (mid,s) < target G (mid,s) := by
  cases s with
  | false => exact hb 1 3 (by decide) (mid-1) (mid-1) (by omega) (by omega) (by omega) (by omega)
  | true => exact hb 0 2 (by decide) (mid-1) (mid-1) (by omega) (by omega) (by omega) (by omega)

theorem boundary_bounds (G : Grid m) {lo hi : Nat} {L : List (Nat × Bool)} (h : Layout G lo hi L)
    (b : Nat × Bool) (hb : b ∈ L) : lo < b.1 ∧ b.1 ≤ hi := by
  induction h with
  | nil => simp at hb
  | @cons lo mid hi s L hlo hhi hblock hbefore hrest ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hlo,hhi⟩
    · have hh := ih hb
      omega

theorem intervals_ordered (G : Grid m) {lo hi : Nat} {L : List (Nat × Bool)}
    (h : Layout G lo hi L) : ∀ b ∈ L, source G b < target G b := by
  induction h with
  | nil => simp
  | cons hlo hhi hb hbefore hrest ih =>
    intro b hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact block_ordered G _ _ _ hlo hb
    · exact ih b hmem

theorem intervals_separated (G : Grid m) {lo hi : Nat} {L : List (Nat × Bool)}
    (h : Layout G lo hi L) : L.Pairwise (fun b d => target G b < source G d) := by
  induction h with
  | nil => simp
  | @cons lo mid hi s L hlo hhi hb hbefore hrest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih⟩
    intro b hmem
    have hh := boundary_bounds G hrest b hmem
    exact hbefore (mid-1) (b.1-1) (by omega) (by omega) (by omega) (by omega)
      (targetGroup s) (sourceGroup b.2)

theorem block_middle (G : Grid m) (lo mid : Nat) (s : Bool) (hlo : lo < mid) (hmid : mid ≤ m)
    (hb : Block G lo mid s) (r : Fin 4) (k : Nat) (hr : r = 1 ∨ r = 2)
    (hlok : lo ≤ k) (hk : k < mid) :
    (source G (mid,s) ≤ G.pos r k ∧ G.pos r k < target G (mid,s)) ∨
      (k = mid-1 ∧ r = targetGroup s) := by
  rcases hr with rfl | rfl
  · cases s with
    | false =>
      by_cases he : k = mid-1
      · exact Or.inr ⟨he,rfl⟩
      · have hl := hb 1 3 (by decide) (mid-1) k (by omega) (by omega) hlok hk
        have hr := G.row 1 k (mid-1) (by omega) (by omega)
        exact Or.inl ⟨Nat.le_of_lt hl,hr⟩
    | true =>
      have hl := hb 0 1 (by decide) (mid-1) k (by omega) (by omega) hlok hk
      have hr := hb 1 2 (by decide) k (mid-1) hlok hk (by omega) (by omega)
      exact Or.inl ⟨Nat.le_of_lt hl,hr⟩
  · cases s with
    | false =>
      have hl := hb 2 3 (by decide) (mid-1) k (by omega) (by omega) hlok hk
      have hr := hb 1 2 (by decide) k (mid-1) hlok hk (by omega) (by omega)
      exact Or.inl ⟨Nat.le_of_lt hl,hr⟩
    | true =>
      by_cases he : k = mid-1
      · exact Or.inr ⟨he,rfl⟩
      · have hl := hb 0 2 (by decide) (mid-1) k (by omega) (by omega) hlok hk
        have hr := G.row 2 k (mid-1) (by omega) (by omega)
        exact Or.inl ⟨Nat.le_of_lt hl,hr⟩

theorem middle_covered (G : Grid m) {lo hi : Nat} {L : List (Nat × Bool)}
    (h : Layout G lo hi L) (hhi : hi ≤ m) (r : Fin 4) (k : Nat)
    (hr : r = 1 ∨ r = 2) (hklo : lo ≤ k) (hkhi : k < hi) :
    Removed G L (G.pos r k) ∨ TargetCoordinate L r k := by
  induction h with
  | nil => omega
  | @cons lo mid hi s L hlo hmid hb hbefore hrest ih =>
    by_cases hk : k < mid
    · rcases block_middle G lo mid s hlo (by omega) hb r k hr hklo hk with hh | hh
      · exact Or.inl ⟨(mid,s),List.mem_cons_self ..,hh⟩
      · exact Or.inr ⟨(mid,s),List.mem_cons_self ..,hh⟩
    · rcases ih hhi (by omega) hkhi with ⟨b,hb,hrem⟩ | ⟨b,hb,ht⟩
      · exact Or.inl ⟨b,List.mem_cons_of_mem _ hb,hrem⟩
      · exact Or.inr ⟨b,List.mem_cons_of_mem _ hb,ht⟩

theorem target_identity (G : Grid m) (L : List (Nat × Bool)) (r : Fin 4) (k : Nat)
    (h : TargetCoordinate L r k) :
    ∃ b ∈ L, G.pos r k = target G b ∧
      (r = 2 → source G b = G.pos 0 k) ∧ (r = 1 → source G b = G.pos 3 k) := by
  obtain ⟨⟨mid,s⟩,hb,hk,hr⟩ := h
  refine ⟨(mid,s),hb,?_,?_,?_⟩
  · simp only [target,hk,hr]
  · intro h2
    cases s <;> simp_all [source,targetGroup,sourceGroup]
  · intro h1
    cases s <;> simp_all [source,targetGroup,sourceGroup]

end NSSE.P0LayoutCuts
