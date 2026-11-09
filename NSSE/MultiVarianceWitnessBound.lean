import NSSE.MultiVarianceLiveResidual
import NSSE.MultiVarianceSelectorCoverage
import NSSE.P0DZEndpointRank
import NSSE.P0DZFirstClashRank
import NSSE.P0DZNonliveRank

/-! An actual input-only signed witness bound. Every virtual proper-path
case is discharged; no rank, liveness, selected residue, model or SAB
premise remains. The live case may change the physical terminal labels. -/
namespace NSSE.MultiVarianceWitnessBound
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceBranch MultiVarianceBranchSoundness
open MultiVarianceLiveResidual MultiVarianceResidualWitness
open P0DZTrace P0DZVirtualTrace P0DZFirstClash P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def liveWordBound (n D : Nat) : Nat := (Finset.range (periodBound n D+1)).sup (witnessBound n)

def combinedBound (N L : Nat) : Nat :=
  max (max (P0DZNormalization.lengthBound N 1) (P0DZNormalization.lengthBound N N))
    (max (P0DZNormalization.lengthBound N ((N+1)^2)) L)

def bound (n D : Nat) : Nat := combinedBound (2^(4*n+2)) (liveWordBound n D)

def wordBound (n D : Nat) : Nat := if D=0 then 0 else bound n D

theorem absent_le (N L : Nat) : P0DZNormalization.lengthBound N 1≤combinedBound N L :=
  (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
theorem unsafe_le (N L : Nat) : P0DZNormalization.lengthBound N N≤combinedBound N L :=
  (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
theorem nonlive_le (N L : Nat) : P0DZNormalization.lengthBound N ((N+1)^2)≤combinedBound N L :=
  (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)

theorem live_le (n D r : Nat) (hr : r≤periodBound n D) : witnessBound n r≤bound n D := by
  have h : witnessBound n r≤liveWordBound n D := Finset.le_sup (Finset.mem_range.mpr (by omega))
  exact h.trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

theorem branch_short (C : Parameters arity n) (w : List (Fin D)) (hi : inspect pol C w=true) :
    ∃ C' : Parameters arity n, C'.query=C.query ∧ ∃ v : List (Fin D),
      inspect pol C' v=true ∧ v.length≤bound n D := by
  classical
  obtain ⟨ho,ha⟩ := (inspect_correct pol C w).mp hi
  have he : (branch pol C D).endX≠(branch pol C D).endY :=
    ends_distinct C _ (MultiVarianceTerminalIsolation.accepted_end pol C w ha)
  by_cases hc : DComplete (branch pol C D) w
  · by_cases hg : GoodWord (P0DZProperMachine.machine (branch pol C D)) w
    · by_cases hl : P0ProperLiveness.Live (P0DZProperMachine.machine (branch pol C D)) w
      · obtain ⟨r,_,hr,C',hq,v,hv,hlen⟩ := live_short pol C w ha hl ho
        exact ⟨C',hq,v,hv,hlen.trans (live_le n D r hr)⟩
      · obtain ⟨v,hv,_,_,hlen⟩ := P0DZNonliveRank.nonlive_short (branch pol C D) w he ha hg hl
        rw [card_state] at hlen
        exact ⟨C,rfl,v,(inspect_correct pol C v).mpr ⟨ho,hv⟩,
          hlen.trans (nonlive_le (2^(4*n+2)) (liveWordBound n D))⟩
    · have hcl : ∃ a b l, Clash (branch pol C D) w a b l := by
        by_contra! h
        exact hg ((P0DZProperMachine.good_iff (branch pol C D) w).mpr ⟨hc,h⟩)
      obtain ⟨v,hv,_,_,hlen⟩ := P0DZFirstClashRank.virtual_unsafe_short (branch pol C D) w he ha hc hcl
      rw [card_state] at hlen
      exact ⟨C,rfl,v,(inspect_correct pol C v).mpr ⟨ho,hv⟩,
        hlen.trans (unsafe_le (2^(4*n+2)) (liveWordBound n D))⟩
  · have hend : properAt (branch pol C D) w w.length=none := by
      cases h : properAt (branch pol C D) w w.length with
      | none => rfl
      | some q => exact False.elim (hc (by unfold DComplete; rw [h]; rfl))
    obtain ⟨v,hv,_,_,hlen⟩ := P0DZEndpointRank.absent_short (branch pol C D) w he ha hend
    rw [card_state] at hlen
    exact ⟨C,rfl,v,(inspect_correct pol C v).mpr ⟨ho,hv⟩,
      hlen.trans (absent_le (2^(4*n+2)) (liveWordBound n D))⟩

theorem branch_wordBound (C : Parameters arity n) (w : List (Fin D)) (hi : inspect pol C w=true) :
    ∃ C' : Parameters arity n, C'.query=C.query ∧ ∃ v : List (Fin D),
      inspect pol C' v=true ∧ v.length≤wordBound n D := by
  by_cases hd : D=0
  · subst D
    have hw : w=[] := List.eq_nil_iff_forall_not_mem.mpr (fun a _ => Fin.elim0 a)
    exact ((P0DZBranch.complete_nonempty _ _ ((inspect_correct pol C w).mp hi).2.1) hw).elim
  · simpa only [wordBound,if_neg hd] using branch_short pol C w hi

variable [Fintype H]

theorem not_entails_iff_bounded (Q : Query arity n) :
    ¬MultiVarianceConstraints.Entails pol Q ↔ MultiVarianceWordReader.Witness pol Q [] ∨
      ∃ w : List (Fin (MultiVarianceBranchFamily.alphabetSize arity)),
        w.length≤wordBound n (MultiVarianceBranchFamily.alphabetSize arity) ∧
        MultiVarianceBranchExtraction.inspectAny pol Q w=true := by
  rw [MultiVarianceSelectorCoverage.not_entails_iff_family]
  constructor
  · rintro (he | ⟨w,hw⟩)
    · exact Or.inl he
    · obtain ⟨C,hq,hi⟩ := (MultiVarianceBranchExtraction.inspectAny_correct pol Q w).mp hw
      obtain ⟨C',hq',v,hv,hlen⟩ := branch_wordBound pol C w hi
      exact Or.inr ⟨v,hlen,(MultiVarianceBranchExtraction.inspectAny_correct pol Q v).mpr ⟨C',hq'.trans hq,hv⟩⟩
  · rintro (he | ⟨w,_,hw⟩)
    · exact Or.inl he
    · exact Or.inr ⟨w,hw⟩

end NSSE.MultiVarianceWitnessBound
