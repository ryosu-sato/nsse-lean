import NSSE.GeneralCopyGrid

/-! Simultaneous deletion uses one increasing retained-position map.
No intermediate singly-deleted word is required to be safe. -/
namespace NSSE.JointSeamFaults
open GeneralCopyGrid PeriodicCopyHeadNormalization
variable {V H I : Type*}

def Fault (q : Nat → Annotation V H I) (N n : Nat) (e : Nat → Nat) (p k : Nat) : Prop :=
  p<n ∧ k<n ∧ p≠k ∧ (e (p+1)≠e p+1 ∨ e (k+1)≠e k+1) ∧
  Active q N (e k) (e p) ∧ (q (e p)).index=(q (e k)).index ∧
  ¬ Active q N (e (k+1)) (e (p+1))

def Tail (q : Nat → Annotation V H I) (N n : Nat) (e : Nat → Nat) (t j : Nat) : Prop :=
  ∃ p k r, Fault q N n e p k ∧ p+1+r=j ∧ k+1+r=t ∧
    ∀ s, s<r → (q (e (p+1+s))).index=(q (e (k+1+s))).index

theorem tail_zero (q : Nat → Annotation V H I) (N n : Nat) (e : Nat → Nat) (p k : Nat)
    (hf : Fault q N n e p k) : Tail q N n e (k+1) (p+1) :=
  ⟨p,k,0,hf,by omega,by omega,by intros; omega⟩

theorem tail_step (q : Nat → Annotation V H I) (N n : Nat) (e : Nat → Nat) (k j : Nat)
    (ht : Tail q N n e k j) (hi : (q (e j)).index=(q (e k)).index) :
    Tail q N n e (k+1) (j+1) := by
  obtain ⟨p,t,r,hf,hj,hk,hm⟩ := ht
  refine ⟨p,t,r+1,hf,by omega,by omega,?_⟩
  intro s hs
  by_cases h : s<r
  · exact hm s h
  · have : s=r := by omega
    subst s
    simpa [hj,hk] using hi

/-- Global monotonicity is stronger than necessary; bounded one-step
monotonicity and range suffice, including initial or terminal cuts. -/
theorem active_or_tail (q : Nat → Annotation V H I) (N n : Nat) (e : Nat → Nat)
    (hbound : ∀ j, j≤n → e j≤N) (hmono : ∀ k, k<n → e k≤e (k+1))
    (k j : Nat) (hk : k≤n) (ha : Active (fun t => q (e t)) n k j) :
    Active q N (e k) (e j) ∨ Tail q N n e k j := by
  induction k generalizing j with
  | zero =>
    obtain ⟨hj,hb⟩ := ha
    exact Or.inl ((active_iff_ray q N _ _).mpr
      ⟨hbound j hj,e j,e 0,0,by omega,by omega,(ray_zero q _ _).mpr hb⟩)
  | succ k ih =>
    obtain ⟨hj,hb | ⟨p,hp,hpn,hjp,hi⟩⟩ := ha
    · exact Or.inl ((active_iff_ray q N _ _).mpr
        ⟨hbound j hj,e j,e (k+1),0,by omega,by omega,(ray_zero q _ _).mpr hb⟩)
    · subst j
      rcases ih p (by omega) hp with ho | ht
      · by_cases hn : Active q N (e (k+1)) (e (p+1))
        · exact Or.inl hn
        · have hne : p≠k := by
            intro he; subst p
            exact hn (diagonal_persists q N (e k) (e (k+1)) ho
              (hmono k (by omega)) (hbound (k+1) hk))
          have hjump : e (p+1)≠e p+1 ∨ e (k+1)≠e k+1 := by
            by_cases hpstep : e (p+1)=e p+1
            · by_cases hkstep : e (k+1)=e k+1
              · apply False.elim
                apply hn
                rw [hkstep,hpstep]
                have hb := hbound (p+1) hj
                rw [hpstep] at hb
                exact ⟨hb,Or.inr ⟨e p,ho,by omega,rfl,hi⟩⟩
              · exact Or.inr hkstep
            · exact Or.inl hpstep
          exact Or.inr (tail_zero q N n e p k ⟨hpn,by omega,hne,hjump,ho,hi,hn⟩)
      · exact Or.inr (tail_step q N n e k p ht hi)

/-- Fault-free joint maps reflect ALL copies, even if their component
single cuts would each introduce harmful copies. -/
theorem fault_free_reflect (q : Nat → Annotation V H I) (N n : Nat) (e : Nat → Nat)
    (hbound : ∀ j, j≤n → e j≤N) (hmono : ∀ k, k<n → e k≤e (k+1))
    (hf : ∀ p k, ¬ Fault q N n e p k)
    (k j : Nat) (hk : k≤n) (ha : Active (fun t => q (e t)) n k j) :
    Active q N (e k) (e j) := by
  rcases active_or_tail q N n e hbound hmono k j hk ha with ho | ht
  · exact ho
  · obtain ⟨p,t,r,hf',_⟩ := ht
    exact False.elim (hf p t hf')

/-- Closed-form source positions for the balanced reciprocal-ray input.
The connection to the original constraint reader is recorded separately. -/
def Triangle (n k j : Nat) : Prop :=
  (k≤n ∧ n+1≤j ∧ j≤n+k) ∨ (j+n+2≤k ∧ k≤2*n+1)

/-- Keep m zeros in each run and remove r zeros from the end of each.
The original run length is m+r. -/
def pairedMap (m r j : Nat) : Nat :=
  if j<m then j else if j<2*m+1 then j+r else j+2*r

/-- Joint deletion preserves the exact triangular copy relation for every
run length and every removal length, not just the finite test instances. -/
theorem triangle_reflect (m r k j : Nat) (ht : Triangle m k j) :
    Triangle (m+r) (pairedMap m r k) (pairedMap m r j) := by
  by_cases hk : k<m <;> by_cases hk' : k<2*m+1 <;>
    by_cases hj : j<m <;> by_cases hj' : j<2*m+1 <;>
    simp only [pairedMap,hk,hk',hj,hj',ite_true,ite_false] <;>
    unfold Triangle at * <;> omega

theorem paired_bound (m r j : Nat) (hj : j≤2*m+2) :
    pairedMap m r j≤2*(m+r)+2 := by
  unfold pairedMap
  split
  · omega
  · split <;> omega

theorem paired_step (m r k : Nat) : pairedMap m r k≤pairedMap m r (k+1) := by
  by_cases hk : k<m <;> by_cases hk' : k<2*m+1 <;>
    by_cases hs : k+1<m <;> by_cases hs' : k+1<2*m+1 <;>
    simp only [pairedMap,hk,hk',hs,hs',ite_true,ite_false] <;> omega

end NSSE.JointSeamFaults
