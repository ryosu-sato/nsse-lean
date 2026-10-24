import NSSE.GeneralCopyGrid

/-! Long primitive periodic tails cannot match arbitrarily long factors of
fixed-word bounded languages. Raw index matching needs head coherence before
this result can be applied to constructor/index tokens. -/
namespace NSSE.BoundedPrefixPeriodicOverlap
open PeriodicCopyHeadNormalization
variable {α V H I : Type*}

def PrimitivePeriod (q : Nat → α) (p : Nat) : Prop :=
  0 < p ∧ PhasePeriodic q 0 p ∧
    ∀ l, 0 < l → l < p → ¬ PhasePeriodic q 0 l

/-- Elementary overlap bound, avoiding a Fine-Wilf theorem dependency.
Agreement for p+l positions would make l a global period of q. -/
theorem overlap_bound (q s : Nat → α) (p l a b r : Nat)
    (hq : PrimitivePeriod q p) (hl : 0 < l) (hlp : l < p)
    (hs : PhasePeriodic s 0 l)
    (hm : ∀ d, d < r → s (a+d) = q (b+d)) : r < p+l := by
  by_contra h
  have hr : p+l ≤ r := by omega
  have localShift : ∀ d, d < p → q (b+d+l) = q (b+d) := by
    intro d hd
    have h₁ := hm d (by omega)
    have h₂ := hm (d+l) (by omega)
    have hmod : Nat.ModEq l (a+d+l) (a+d) := by
      change (a+d+l)%l = (a+d)%l
      simp
    have he := hs (a+d+l) (a+d) (by omega) (by omega) hmod
    rw [← Nat.add_assoc] at h₂
    simpa [Nat.add_assoc] using h₂.symm.trans (he.trans h₁)
  have shift : ∀ n, q (n+l) = q n := by
    intro n
    obtain ⟨z,hbz,hzp,hmod⟩ := residue_in_interval b n p hq.1
    have he : b+(z-b) = z := by omega
    have hz := localShift (z-b) (by omega)
    rw [he] at hz
    calc
      q (n+l) = q (z+l) :=
        (hq.2.1 (z+l) (n+l) (by omega) (by omega) (hmod.add_right l)).symm
      _ = q z := hz
      _ = q n := hq.2.1 z n (by omega) (by omega) hmod
  exact hq.2.2 l hl hlp (phase_of_shift q 0 l (fun n _ => shift n))

/-- A segment of a periodic block. Its length is unrestricted and can be
zero; phase changes are absorbed into seq. -/
structure Block (α : Type*) where
  seq : Nat → α
  period : Nat
  length : Nat
  positive : 0 < period
  periodic : PhasePeriodic seq 0 period

def MatchesBlocks (q : Nat → α) (b : Nat) : List (Block α) → Prop
  | [] => True
  | w :: ws => (∀ d, d < w.length → w.seq d = q (b+d)) ∧
      MatchesBlocks q (b+w.length) ws

/-- The bound is independent of all block exponents/lengths. -/
theorem blocks_bound (q : Nat → α) (p b : Nat) (ws : List (Block α))
    (hq : PrimitivePeriod q p)
    (hs : ∀ w ∈ ws, w.period < p) (hm : MatchesBlocks q b ws) :
    (ws.map Block.length).sum ≤ (ws.map (fun w => p+w.period-1)).sum := by
  induction ws generalizing b with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨hw,ht⟩ := hm
    have bound := overlap_bound q w.seq p w.period 0 b w.length hq
      w.positive (hs w (by simp)) w.periodic (by simpa using hw)
    have rest := ih (b+w.length) (fun v hv => hs v (by simp [hv])) ht
    simp only [List.map_cons,List.sum_cons]
    omega

def token (q : Nat → Annotation V H I) (j : Nat) : H × I :=
  ((q j).head,(q j).index)

/-- A coherent ray matches constructor/index tokens, not merely indices. -/
theorem ray_tokens (q : Nat → Annotation V H I) (a b r : Nat)
    (hr : Ray q a b r)
    (hc : ∀ d, d < r → (q (a+d)).head = (q (b+d)).head) :
    ∀ d, d < r → token q (a+d) = token q (b+d) := by
  intro d hd
  exact Prod.ext (hc d hd) (hr.2 d hd)

/-- Before the first incoherent comparison row, every ray really matches
full tokens. Its endpoint head is deliberately excluded: it may be the
first mismatch. This avoids assuming coherence at the disputed endpoint. -/
theorem ray_tokens_before_first_bad (q : Nat → Annotation V H I)
    (N bad a b r : Nat) (hr : Ray q a b r)
    (hs : a+r ≤ N) (ht : b+r ≤ bad)
    (hc : ∀ k, k < bad → ∀ j, GeneralCopyGrid.Active q N k j →
      (q j).head = (q k).head) :
    ∀ d, d < r → token q (a+d) = token q (b+d) := by
  apply ray_tokens q a b r hr
  intro d hd
  have prefixRay : Ray q a b d :=
    ⟨hr.1,fun e he => hr.2 e (by omega)⟩
  have active : GeneralCopyGrid.Active q N (b+d) (a+d) :=
    (GeneralCopyGrid.active_iff_ray q N (b+d) (a+d)).mpr
      ⟨by omega,a,b,d,rfl,rfl,prefixRay⟩
  exact hc (b+d) (by omega) (a+d) active

/-- Every full-token match from the prefix into the proper tail is short.
The N bound excludes the possibly changed endpoint token. -/
def CrossBound (q : Nat → Annotation V H I) (F N K : Nat) : Prop :=
  ∀ s t len, s < F → F ≤ t → s+len ≤ F → t+len ≤ N →
    (∀ d, d < len → token q (s+d) = token q (t+d)) → len ≤ K

/-- A coherent forward ray whose source has gone K steps beyond the free
frontier must have distance at most K. The original frontier depth F is
absent from this late distance bound. -/
theorem forward_tail_distance (q : Nat → Annotation V H I)
    (F N K a b r : Nat) (hb : b < a) (ha : a ≤ F)
    (hn : a+r ≤ N) (hr : Ray q a b r)
    (hc : ∀ d, d < r → (q (a+d)).head = (q (b+d)).head)
    (hcross : CrossBound q F N K) :
    a+r ≤ F+K ∨ a ≤ b+K := by
  by_contra h
  have far : F+K < a+r := by omega
  have dist : b+K < a := by omega
  let start := b+(F-a)
  let len := min (a-b) (a+r-F)
  have hstart : start < F := by dsimp [start]; omega
  have hend : start+len ≤ F := by dsimp [start,len]; omega
  have htail : F+len ≤ N := by dsimp [len]; omega
  have hlen : K < len := by dsimp [len]; omega
  have hmatches := ray_tokens q a b r hr hc
  have bound := hcross start F len hstart (by omega) hend htail (by
    intro d hd
    have hm := hmatches (F-a+d) (by dsimp [len] at hd; omega)
    have he : a+(F-a+d) = F+d := by omega
    have ht : b+(F-a+d) = start+d := by dsimp [start]; omega
    rw [he,ht] at hm
    exact hm.symm)
  omega

end NSSE.BoundedPrefixPeriodicOverlap
