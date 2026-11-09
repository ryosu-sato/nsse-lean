import NSSE.MultiConstructorLiveResidual
import NSSE.MultiConstructorSelectorCoverage
import NSSE.P0DZEndpointRank
import NSSE.P0DZFirstClashRank
import NSSE.P0DZNonliveRank

/-! An input-only bound for every original unified witness. All four
proper-path cases are covered; no rank, liveness or residual premise remains. -/
namespace NSSE.MultiConstructorUnifiedBound
open MultiConstructorConstraints MultiConstructorBranch MultiConstructorUnifiedWords
open MultiConstructorLiveResidual MultiConstructorResidualWitness
open P0DZBranch P0DZTrace P0DZVirtualTrace P0DZFirstClash P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def liveWordBound (n D : Nat) : Nat :=
  (Finset.range (periodBound n D+1)).sup (witnessBound n)

def combinedBound (N L : Nat) : Nat :=
  max (max (P0DZNormalization.lengthBound N 1) (P0DZNormalization.lengthBound N N))
    (max (P0DZNormalization.lengthBound N ((N+1)^2)) L)

def bound (n D : Nat) : Nat := combinedBound ((2^n)^4) (liveWordBound n D)

theorem absent_le (N L : Nat) : P0DZNormalization.lengthBound N 1 ≤ combinedBound N L :=
  (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)

theorem unsafe_le (N L : Nat) : P0DZNormalization.lengthBound N N ≤ combinedBound N L :=
  (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)

theorem nonlive_le (N L : Nat) : P0DZNormalization.lengthBound N ((N+1)^2) ≤ combinedBound N L :=
  (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem live_le (n D r : Nat) (hr : r ≤ periodBound n D) : witnessBound n r ≤ bound n D := by
  have h : witnessBound n r ≤ liveWordBound n D := Finset.le_sup (Finset.mem_range.mpr (by omega))
  exact h.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

theorem branch_short (C : Parameters arity n) (w : List (Fin D)) (ha : Accepted (branch C D) w) :
    ∃ v : List (Fin D), Witness C.input C.left C.right v ∧ v.length ≤ bound n D := by
  classical
  have he : (branch C D).endX ≠ (branch C D).endY := MultiConstructorBranchLocal.ends_distinct C w ha.1
  by_cases hc : DComplete (branch C D) w
  · by_cases hg : GoodWord (P0DZProperMachine.machine (branch C D)) w
    · by_cases hl : P0ProperLiveness.Live (P0DZProperMachine.machine (branch C D)) w
      · obtain ⟨r,_,hr,v,hv,hlen⟩ := live_short C w ha hl
        exact ⟨v,hv,hlen.trans (live_le n D r hr)⟩
      · obtain ⟨v,hv,_,_,hlen⟩ := P0DZNonliveRank.nonlive_short (branch C D) w he ha hg hl
        rw [card_state] at hlen
        exact ⟨v,MultiConstructorUnifiedBranch.accepted_witness C v hv,
          hlen.trans (nonlive_le ((2^n)^4) (liveWordBound n D))⟩
    · have hcl : ∃ a b l, Clash (branch C D) w a b l := by
        by_contra! h
        exact hg ((P0DZProperMachine.good_iff (branch C D) w).mpr ⟨hc,h⟩)
      obtain ⟨v,hv,_,_,hlen⟩ := P0DZFirstClashRank.virtual_unsafe_short (branch C D) w he ha hc hcl
      rw [card_state] at hlen
      exact ⟨v,MultiConstructorUnifiedBranch.accepted_witness C v hv,
        hlen.trans (unsafe_le ((2^n)^4) (liveWordBound n D))⟩
  · have hend : properAt (branch C D) w w.length = none := by
      cases h : properAt (branch C D) w w.length with
      | none => rfl
      | some q => exact False.elim (hc (by unfold DComplete; rw [h]; rfl))
    obtain ⟨v,hv,_,_,hlen⟩ := P0DZEndpointRank.absent_short (branch C D) w he ha hend
    rw [card_state] at hlen
    exact ⟨v,MultiConstructorUnifiedBranch.accepted_witness C v hv,
      hlen.trans (absent_le ((2^n)^4) (liveWordBound n D))⟩

theorem exists_short (phi : Constraints arity n) (x y : Fin n)
    (hex : ∃ w : List (Fin D), Witness phi x y w) :
    ∃ v : List (Fin D), Witness phi x y v ∧ v.length ≤ bound n D := by
  rcases (MultiConstructorSelectorCoverage.exists_iff phi x y).mp hex with he | ⟨w,reset,fallback,ex,ey,ha⟩
  · exact ⟨[],he,Nat.zero_le _⟩
  · exact branch_short (MultiConstructorSelectedAcceptance.config phi x y reset fallback ex ey) w ha

theorem bounded_iff (phi : Constraints arity n) (x y : Fin n) :
    (∃ w : List (Fin D), Witness phi x y w) ↔
      ∃ w : List (Fin D), Witness phi x y w ∧ w.length ≤ bound n D :=
  ⟨exists_short phi x y,fun ⟨w,hw,_⟩ => ⟨w,hw⟩⟩

end NSSE.MultiConstructorUnifiedBound
