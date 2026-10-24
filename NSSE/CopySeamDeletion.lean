import NSSE.GeneralCopyGrid

/-! A sufficient, finite seam certificate for copy reflection after deletion.
Existence of a certified short deletion is not claimed. -/
namespace NSSE.CopySeamDeletion
open GeneralCopyGrid PeriodicCopyHeadNormalization
variable {V H I : Type*}

def cutMap (L d k : Nat) : Nat := if k<L then k else k+d

private theorem cut_bound (L d n j : Nat) (hj : j≤n) : cutMap L d j≤n+d := by
  unfold cutMap
  split <;> omega

private theorem cut_mono_step (L d k : Nat) : cutMap L d k≤cutMap L d (k+1) := by
  unfold cutMap
  split <;> split <;> omega

private theorem cut_step (L d k : Nat) (hk : k+1≠L) :
    cutMap L d (k+1)=cutMap L d k+1 := by
  unfold cutMap
  split <;> split <;> omega

/-- Only one boundary row and one boundary column need checking. The
intersection is diagonal and propagates automatically across the cut. -/
def Seam (q : Nat → Annotation V H I) (n L d : Nat) : Prop :=
  ∀ p k, p<n → k<n →
    ((p+1=L ∧ k+1≠L) ∨ (k+1=L ∧ p+1≠L)) →
    Active q (n+d) (cutMap L d k) (cutMap L d p) →
    (q (cutMap L d p)).index=(q (cutMap L d k)).index →
    Active q (n+d) (cutMap L d (k+1)) (cutMap L d (p+1))

/-- Under the finite seam certificate, every shortened-grid copy already
exists at the mapped positions of the old grid. Births are preserved
because the shortened annotation is the pullback along the cut map. -/
theorem active_reflect (q : Nat → Annotation V H I) (n L d : Nat)
    (hs : Seam q n L d) (k j : Nat) (hk : k≤n)
    (ha : Active (fun t => q (cutMap L d t)) n k j) :
    Active q (n+d) (cutMap L d k) (cutMap L d j) := by
  induction k generalizing j with
  | zero =>
    obtain ⟨hj,hb⟩ := ha
    apply (active_iff_ray q (n+d) (cutMap L d 0) (cutMap L d j)).mpr
    exact ⟨cut_bound L d n j hj,cutMap L d j,cutMap L d 0,0,
      by omega,by omega,(ray_zero q _ _).mpr hb⟩
  | succ k ih =>
    obtain ⟨hj,hb | ⟨p,hp,hpn,hjp,hi⟩⟩ := ha
    · apply (active_iff_ray q (n+d) (cutMap L d (k+1)) (cutMap L d j)).mpr
      exact ⟨cut_bound L d n j hj,cutMap L d j,cutMap L d (k+1),0,
        by omega,by omega,(ray_zero q _ _).mpr hb⟩
    · subst j
      have hold := ih p (by omega) hp
      by_cases hps : p+1=L
      · by_cases hks : k+1=L
        · have hpk : p=k := by omega
          subst p
          exact diagonal_persists q (n+d) (cutMap L d k) (cutMap L d (k+1))
            hold (cut_mono_step L d k) (cut_bound L d n (k+1) hk)
        · exact hs p k hpn (by omega) (Or.inl ⟨hps,hks⟩) hold hi
      · by_cases hks : k+1=L
        · exact hs p k hpn (by omega) (Or.inr ⟨hks,hps⟩) hold hi
        · rw [cut_step L d k hks,cut_step L d p hps]
          have hbound := cut_bound L d n (p+1) hj
          rw [cut_step L d p hps] at hbound
          exact ⟨hbound,Or.inr ⟨cutMap L d p,hold,by omega,rfl,hi⟩⟩

/-- Deleting an initial segment needs no seam checks at all. This yields
unconditional suffix-grid reflection, given annotation pullback. -/
theorem root_seam (q : Nat → Annotation V H I) (n d : Nat) : Seam q n 0 d := by
  intro p k hp hk hcross
  rcases hcross with ⟨h,_⟩ | ⟨h,_⟩ <;> omega

theorem suffix_reflect (q : Nat → Annotation V H I) (n d k j : Nat)
    (hk : k≤n) (ha : Active (fun t => q (t+d)) n k j) :
    Active q (n+d) (k+d) (j+d) := by
  simpa [cutMap] using active_reflect q n 0 d (root_seam q n d) k j hk
    (by simpa [cutMap] using ha)

/-- Copied head sets can only shrink at corresponding rows. -/
theorem head_reflect (q : Nat → Annotation V H I) (n L d : Nat)
    (hs : Seam q n L d) (k : Nat) (hk : k≤n) (h : H)
    (ha : HasHead (fun t => q (cutMap L d t)) n k h) :
    HasHead q (n+d) (cutMap L d k) h := by
  obtain ⟨j,hj,hh⟩ := (head_iff_active _ n k h).mp ha
  exact (head_iff_active q (n+d) (cutMap L d k) h).mpr
    ⟨cutMap L d j,active_reflect q n L d hs k j hk hj,hh⟩

/-- A copied terminal Top cannot be newly introduced by certified deletion. -/
theorem terminal_reflect (q : Nat → Annotation V H I) (n L d : Nat)
    (hL : L≤n) (hs : Seam q n L d) (k : Nat) (hk : k≤n)
    (ha : Active (fun t => q (cutMap L d t)) n k n) :
    Active q (n+d) (cutMap L d k) (n+d) := by
  have hh := active_reflect q n L d hs k n hk ha
  simpa only [cutMap,if_neg (show ¬ n<L by omega)] using hh

end NSSE.CopySeamDeletion
