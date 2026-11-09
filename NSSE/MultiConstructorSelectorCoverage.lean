import NSSE.MultiConstructorSelectedAcceptance

/-! Every first nonempty original unified word is accepted by one of the
finite reset/head/terminal parameter choices of the actual compiler. -/
namespace NSSE.MultiConstructorSelectorCoverage
open MultiConstructorConstraints MultiConstructorTrees MultiConstructorRawTrace MultiConstructorRawValidity
open MultiConstructorUnifiedWords MultiConstructorIsolatedPrefix MultiConstructorEmptyTail
open MultiConstructorTailPeriod MultiConstructorSelectorTrace MultiConstructorSelectorHeads
open MultiConstructorSelectedAcceptance MultiConstructorBranch
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

theorem first_covered (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (hf : First phi x y w) (hw : w ≠ []) :
    ∃ reset : Row n, ∃ fallback : H, ∃ ex ey : Label H,
      P0DZBranch.Accepted (branch (config phi x y reset fallback ex ey) D) w := by
  classical
  obtain ⟨heads,ex,ey,ha⟩ := hf.1
  have hn : 0 < w.length := List.length_pos_iff.mpr hw
  by_cases hex : ∃ J, J < w.length ∧ row phi x y w J = (∅,∅)
  · let J := Nat.find hex
    have hJ : J < w.length := (Nat.find_spec hex).1
    have he : row phi x y w J = (∅,∅) := (Nat.find_spec hex).2
    have hbefore : ∀ k, k < J → row phi x y w k ≠ (∅,∅) := by
      intro k hk hek
      exact Nat.find_min hex hk ⟨by omega,hek⟩
    obtain ⟨d,hd,hdJ,hc⟩ := first_period phi x y w hf heads ex ey ha J hJ he
    refine ⟨row phi x y w (J-d),heads ⟨J-1,by omega⟩,ex,ey,?_⟩
    apply realized phi x y w hw heads ex ey ha
    · intro k
      exact replay_head phi x y w heads ha.1 J d hJ hd hdJ hbefore he hc k.val k.isLt
    · intro k
      exact replay_proper phi x y w heads ha.1 J d hJ hd hdJ hbefore he hc k.val k.isLt
  · have hbefore : ∀ k, k < w.length → row phi x y w k ≠ (∅,∅) := by
      intro k hk he
      exact hex ⟨k,hk,he⟩
    refine ⟨(∅,∅),heads ⟨w.length-1,by omega⟩,ex,ey,?_⟩
    apply realized phi x y w hw heads ex ey ha
    · intro k
      rw [before_empty phi x y _ w w.length le_rfl hbefore k.val k.isLt]
      exact before_head phi x y w heads ha.1 w.length hn le_rfl hbefore k.val k.isLt
    · intro k
      rw [before_empty phi x y _ w w.length le_rfl hbefore k.val k.isLt]
      exact proper_row phi x y w heads ha.1 k.val k.isLt

def Family (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) : Prop :=
  ∃ reset : Row n, ∃ fallback : H, ∃ ex ey : Label H,
    P0DZBranch.Accepted (branch (config phi x y reset fallback ex ey) D) w

def familyDecision [Fintype H] (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) :
    Decidable (Family phi x y w) := by
  letI : ∀ (reset : Row n) (fallback : H) (ex ey : Label H),
      Decidable (P0DZBranch.Accepted (branch (config phi x y reset fallback ex ey) D) w) :=
    fun reset fallback ex ey => P0DZDecision.acceptedDecision
      (branch (config phi x y reset fallback ex ey) D) (birthDecision _ _) w
  unfold Family
  infer_instance

def inspect [Fintype H] (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) : Bool :=
  @decide (Family phi x y w) (familyDecision phi x y w)

theorem inspect_correct [Fintype H] (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) :
    inspect phi x y w = true ↔ Family phi x y w := by
  unfold inspect
  exact @decide_eq_true_iff _ (familyDecision phi x y w)

theorem family_sound (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (hw : Family phi x y w) : Witness phi x y w := by
  obtain ⟨reset,fallback,ex,ey,ha⟩ := hw
  exact MultiConstructorUnifiedBranch.accepted_witness (config phi x y reset fallback ex ey) w ha

theorem prefix_iff (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) :
    (∃ m, m ≤ w.length ∧ Witness phi x y (w.take m)) ↔
      Witness phi x y ([] : List (Fin D)) ∨ ∃ m, m ≤ w.length ∧ Family phi x y (w.take m) := by
  constructor
  · rintro ⟨m,hm,hw⟩
    obtain ⟨k,hk,hf⟩ := MultiConstructorFirstRay.first_prefix phi x y (w.take m) hw
    have hkm : k ≤ m := by simp only [List.length_take] at hk; omega
    have hkn : k ≤ w.length := by omega
    have hf' : First phi x y (w.take k) := by
      simpa only [List.take_take,Nat.min_eq_left hkm] using hf
    by_cases he : w.take k = []
    · exact Or.inl (he ▸ hf'.1)
    · exact Or.inr ⟨k,hkn,first_covered phi x y (w.take k) hf' he⟩
  · rintro (he | ⟨m,hm,hf⟩)
    · exact ⟨0,Nat.zero_le _,by simpa only [List.take_zero] using he⟩
    · exact ⟨m,hm,family_sound phi x y _ hf⟩

theorem exists_iff (phi : Constraints arity n) (x y : Fin n) :
    (∃ w : List (Fin D), Witness phi x y w) ↔
      Witness phi x y ([] : List (Fin D)) ∨ ∃ w : List (Fin D), Family phi x y w := by
  constructor
  · rintro ⟨w,hw⟩
    have hp : ∃ m, m ≤ w.length ∧ Witness phi x y (w.take m) :=
      ⟨w.length,le_rfl,by simpa only [List.take_length] using hw⟩
    rcases (prefix_iff phi x y w).mp hp with he | ⟨m,_,hf⟩
    · exact Or.inl he
    · exact Or.inr ⟨w.take m,hf⟩
  · rintro (he | ⟨w,hf⟩)
    · exact ⟨[],he⟩
    · exact ⟨w,family_sound phi x y w hf⟩

end NSSE.MultiConstructorSelectorCoverage
