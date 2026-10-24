import NSSE.CopySeamDeletion

/-! Every copy created by a deletion descends from a one-sided boundary
fault. Harmless fault tails may be retained rather than forbidden. -/
namespace NSSE.SeamFaultPropagation
open GeneralCopyGrid PeriodicCopyHeadNormalization CopySeamDeletion
variable {V H I : Type*}

def Fault (q : Nat → Annotation V H I) (n L d p k : Nat) : Prop :=
  p<n ∧ k<n ∧ ((p+1=L ∧ k+1≠L) ∨ (k+1=L ∧ p+1≠L)) ∧
  Active q (n+d) (cutMap L d k) (cutMap L d p) ∧
  (q (cutMap L d p)).index=(q (cutMap L d k)).index ∧
  ¬ Active q (n+d) (cutMap L d (k+1)) (cutMap L d (p+1))

/-- The propagated tail does not require a new birth. Its initial edge
comes from a mapped old predecessor and a missing mapped successor. -/
def Tail (q : Nat → Annotation V H I) (n L d t j : Nat) : Prop :=
  ∃ p k r, Fault q n L d p k ∧ p+1+r=j ∧ k+1+r=t ∧
    ∀ s, s<r → (q (cutMap L d (p+1+s))).index=(q (cutMap L d (k+1+s))).index

theorem tail_zero (q : Nat → Annotation V H I) (n L d p k : Nat)
    (hf : Fault q n L d p k) : Tail q n L d (k+1) (p+1) := by
  exact ⟨p,k,0,hf,by omega,by omega,by intros; omega⟩

theorem tail_step (q : Nat → Annotation V H I) (n L d t j : Nat)
    (ht : Tail q n L d t j)
    (hi : (q (cutMap L d j)).index=(q (cutMap L d t)).index) :
    Tail q n L d (t+1) (j+1) := by
  obtain ⟨p,k,r,hf,hj,hk,hm⟩ := ht
  refine ⟨p,k,r+1,hf,by omega,by omega,?_⟩
  intro s hs
  by_cases h : s<r
  · exact hm s h
  · have : s=r := by omega
    subst s
    simpa [hj,hk] using hi

private theorem bound (L d n j : Nat) (hj : j≤n) : cutMap L d j≤n+d := by
  unfold cutMap; split <;> omega

private theorem next (L d k : Nat) (hk : k+1≠L) :
    cutMap L d (k+1)=cutMap L d k+1 := by
  unfold cutMap; split <;> split <;> omega

/-- No seam hypothesis is needed for this decomposition. All new copies
are in the finite union of tails originating at boundary faults. -/
theorem active_or_tail (q : Nat → Annotation V H I) (n L d k j : Nat)
    (hk : k≤n) (ha : Active (fun t => q (cutMap L d t)) n k j) :
    Active q (n+d) (cutMap L d k) (cutMap L d j) ∨ Tail q n L d k j := by
  induction k generalizing j with
  | zero =>
    obtain ⟨hj,hb⟩ := ha
    apply Or.inl
    exact (active_iff_ray q (n+d) _ _).mpr
      ⟨bound L d n j hj,cutMap L d j,cutMap L d 0,0,
        by omega,by omega,(ray_zero q _ _).mpr hb⟩
  | succ k ih =>
    obtain ⟨hj,hb | ⟨p,hp,hpn,hjp,hi⟩⟩ := ha
    · apply Or.inl
      exact (active_iff_ray q (n+d) _ _).mpr
        ⟨bound L d n j hj,cutMap L d j,cutMap L d (k+1),0,
          by omega,by omega,(ray_zero q _ _).mpr hb⟩
    · subst j
      rcases ih p (by omega) hp with hold | ht
      · by_cases hn : Active q (n+d) (cutMap L d (k+1)) (cutMap L d (p+1))
        · exact Or.inl hn
        · have hcross : (p+1=L ∧ k+1≠L) ∨ (k+1=L ∧ p+1≠L) := by
            by_cases hps : p+1=L
            · by_cases hks : k+1=L
              · have hpk : p=k := by omega
                subst p
                apply False.elim
                apply hn
                exact diagonal_persists q (n+d) (cutMap L d k) (cutMap L d (k+1)) hold
                  (by unfold cutMap; split <;> split <;> omega) (bound L d n (k+1) hk)
              · exact Or.inl ⟨hps,hks⟩
            · by_cases hks : k+1=L
              · exact Or.inr ⟨hks,hps⟩
              · apply False.elim
                apply hn
                rw [next L d k hks,next L d p hps]
                have hb := bound L d n (p+1) hj
                rw [next L d p hps] at hb
                exact ⟨hb,Or.inr ⟨cutMap L d p,hold,by omega,rfl,hi⟩⟩
          exact Or.inr (tail_zero q n L d p k ⟨hpn,by omega,hcross,hold,hi,hn⟩)
      · exact Or.inr (tail_step q n L d k p ht hi)

/-- A guard need only cover mapped old copies and the finite fault tails.
In the application it permits already-present constructor heads and
separately checks terminal Top. It need not preserve source identities. -/
theorem guarded_active (q : Nat → Annotation V H I) (n L d : Nat)
    (guard : Nat → Nat → Prop)
    (hold : ∀ k j, k≤n → j≤n →
      Active q (n+d) (cutMap L d k) (cutMap L d j) → guard k j)
    (htail : ∀ k j, k≤n → j≤n → Tail q n L d k j → guard k j)
    (k j : Nat) (hk : k≤n)
    (ha : Active (fun t => q (cutMap L d t)) n k j) : guard k j := by
  have hj := ((active_iff_ray _ n k j).mp ha).1
  rcases active_or_tail q n L d k j hk ha with ho | ht
  · exact hold k j hk hj ho
  · exact htail k j hk hj ht

end NSSE.SeamFaultPropagation
