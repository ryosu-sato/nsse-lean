import NSSE.BoundedPrefixPeriodicOverlap

/-! Past-copy localization and payload-preserving shortening after a free
frontier. This is not an end-to-end input decision theorem. -/
namespace NSSE.LatePastCopyNormalization
open PeriodicCopyHeadNormalization BoundedPrefixPeriodicOverlap
variable {V H I A : Type*}

/-- A late coherent past copy is close, short, or born near the frontier
on its source side. The target birth need not precede the frontier. -/
theorem past_birth_localization (q : Nat → Annotation V H I)
    (F N K a b r : Nat) (hab : a < b) (ha : a ≤ F)
    (ht : b+r ≤ N) (hlate : F+K < b+r) (hr : Ray q a b r)
    (hc : ∀ d, d < r → (q (a+d)).head = (q (b+d)).head)
    (hcross : CrossBound q F N K) :
    b ≤ a+K ∨ r ≤ K ∨ F ≤ a+K := by
  have hm := ray_tokens q a b r hr hc
  by_contra h
  have hdist : a+K < b := by omega
  have hlong : K < r := by omega
  have hfar : a+K < F := by omega
  by_cases hb : b ≤ F
  · let start := a+(F-b)
    let len := min (b-a) (b+r-F)
    have hstart : start < F := by dsimp [start]; omega
    have hend : start+len ≤ F := by dsimp [start,len]; omega
    have htail : F+len ≤ N := by dsimp [len]; omega
    have hlen : K < len := by dsimp [len]; omega
    have bound := hcross start F len hstart (by omega) hend htail (by
      intro d hd
      have he := hm (F-b+d) (by dsimp [len] at hd; omega)
      have h₁ : a+(F-b+d) = start+d := by dsimp [start]; omega
      have h₂ : b+(F-b+d) = F+d := by omega
      simpa only [h₁,h₂] using he)
    omega
  · have bound := hcross a b (K+1) (by omega) (by omega)
      (by omega) (by omega) (fun d hd => hm d (by omega))
    omega

/-- Replace a long far-past ray by a short ray with the SAME source birth
and target endpoint. Any eventually periodic payload is preserved, including
(source index, next head), as needed before a changed final exit. -/
theorem normalize_past (q : Nat → Annotation V H I) (payload : Nat → A)
    (F T P N K a b r : Nat) (hFT : F ≤ T) (hp : 0 < P)
    (hq : PhasePeriodic q T P) (hpayload : PhasePeriodic payload T P)
    (hab : a < b) (ha : a ≤ F) (ht : b+r ≤ N)
    (hlate : F+K < b+r) (hr : Ray q a b r)
    (hc : ∀ d, d < r → (q (a+d)).head = (q (b+d)).head)
    (hcross : CrossBound q F N K) :
    ∃ b' r', r' ≤ r ∧ a+r' ≤ N ∧ b'+r' = b+r ∧
      Ray q a b' r' ∧ payload (a+r') = payload (a+r) ∧
      (Near (K+(T-F)+P) a b' ∨ r' ≤ K+(T-F)+P) := by
  let B := K+(T-F)+P
  by_cases hshort : r ≤ B
  · exact ⟨b,r,by omega,by omega,rfl,hr,rfl,Or.inr hshort⟩
  by_cases hnear : Near B a b
  · exact ⟨b,r,by omega,by omega,rfl,hr,rfl,Or.inl hnear⟩
  have hB : K ≤ B := by dsimp [B]; omega
  have hdist : a+B < b := by unfold Near at hnear; omega
  have hlocal := past_birth_localization q F N K a b r hab ha ht hlate hr hc hcross
  have haK : F ≤ a+K := by omega
  have hbT : T ≤ b := by dsimp [B] at hdist; omega
  have hbase : T-a ≤ r := by dsimp [B] at hshort; omega
  obtain ⟨r',hrlow,hrhigh,hrr,hmod⟩ := first_residue (T-a) r P hp hbase
  let b' := b+r-r'
  have hsum : b'+r' = b+r := by dsimp [b']; omega
  have hbb : b ≤ b' := by dsimp [b']; omega
  have hmodsum : Nat.ModEq P (b'+r') (b+r) := by rw [hsum]
  have hbmod : Nat.ModEq P b' b := Nat.ModEq.add_right_cancel hmod hmodsum
  have heq : q b' = q b := hq b' b (by omega) hbT hbmod
  have newray : Ray q a b' r' := by
    constructor
    · rw [heq]
      exact hr.1
    · intro d hd
      have he := hq (b'+d) (b+d) (by omega) (by omega) (hbmod.add_right d)
      rw [he]
      exact hr.2 d (by omega)
  refine ⟨b',r',hrr,by omega,hsum,newray,?_,Or.inr ?_⟩
  · exact hpayload (a+r') (a+r) (by omega) (by omega) (hmod.add_left a)
  · dsimp [B] at *
    omega

end NSSE.LatePastCopyNormalization
