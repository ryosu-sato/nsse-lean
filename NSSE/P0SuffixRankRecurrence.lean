import NSSE.P0SuffixRank
import Mathlib.Data.Finset.Max

/-! The finite maximum-chain definition satisfies exactly the backward
recurrence of x741. Maximal chains attain both local and whole-word ranks. -/
namespace NSSE.P0SuffixRankRecurrence
open P0DZBranch P0SuffixRank
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A]

def successors (J : Branch Q Z A H) (w : List A) (a : Nat) : Finset Nat :=
  (Finset.range w.length).filter (fun b => Linked J w a b)

theorem recurrence (J : Branch Q Z A H) (w : List A) (a : Nat) (ha : a < w.length) :
    rank J w a = 1 + (successors J w a).sup (rank J w) := by
  apply le_antisymm
  · obtain ⟨S,hS,hcard⟩ := rank_attained J w a ha
    by_cases hsmall : S.card ≤ 1
    · omega
    have hsum := Finset.card_erase_add_one hS.2.1
    have hne : (S.erase a).Nonempty := Finset.card_pos.mp (by omega)
    let b := (S.erase a).min' hne
    have hb : b ∈ S.erase a := (S.erase a).min'_mem hne
    have hbS := Finset.mem_erase.mp hb
    have hab : a < b := by have hh := hS.2.2.1 b hbS.2; omega
    have hlink := hS.2.2.2 a hS.2.1 b hbS.2 hab
    have hE : ChainAt J w b (S.erase a) := by
      refine ⟨Finset.Subset.trans (Finset.erase_subset _ _) hS.1,hb,?_,?_⟩
      · intro c hc; exact (S.erase a).min'_le c hc
      · intro p hp q hq hpq
        exact hS.2.2.2 p (Finset.mem_of_mem_erase hp) q (Finset.mem_of_mem_erase hq) hpq
    have hlow := chain_le_rank J w b (S.erase a) hE
    have hupper : rank J w b ≤ (successors J w a).sup (rank J w) :=
      Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlink.2.1,hlink⟩)
    omega
  · have hp := rank_positive J w a ha
    have hh : (successors J w a).sup (rank J w) ≤ rank J w a-1 := by
      apply Finset.sup_le
      intro b hb
      have hs := rank_strict J w a b (Finset.mem_filter.mp hb).2
      omega
    omega

theorem unique (J : Branch Q Z A H) (w : List A) (r : Nat → Nat)
    (hz : ∀ a, w.length ≤ a → r a = 0)
    (hr : ∀ a, a < w.length → r a = 1+(successors J w a).sup r) :
    ∀ a, r a = rank J w a := by
  have hmain : ∀ d a, w.length-a = d → r a = rank J w a := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro a hd
      by_cases ha : a < w.length
      · rw [hr a ha,recurrence J w a ha]
        congr 1
        apply Finset.sup_congr rfl
        intro b hb
        have hab := (Finset.mem_filter.mp hb).2
        exact ih (w.length-b) (by have := hab.1; have := hab.2.1; omega) b rfl
      · rw [hz a (by omega),rank_zero J w a (by omega)]
  exact fun a => hmain (w.length-a) a rfl

theorem max_attained (J : Branch Q Z A H) (w : List A) (hw : 0 < w.length) :
    ∃ a S, ChainAt J w a S ∧ S.card = maxRank J w := by
  have hn : (Finset.range w.length).Nonempty := ⟨0,Finset.mem_range.mpr hw⟩
  obtain ⟨a,ha,hm⟩ := Finset.exists_mem_eq_sup (Finset.range w.length) hn (rank J w)
  obtain ⟨S,hS,hcard⟩ := rank_attained J w a (Finset.mem_range.mp ha)
  exact ⟨a,S,hS,hcard.trans hm.symm⟩

theorem max_le_of_chains (J : Branch Q Z A H) (w : List A) (B : Nat)
    (h : ∀ a S, ChainAt J w a S → S.card ≤ B) : maxRank J w ≤ B := by
  apply Finset.sup_le
  intro a ha
  obtain ⟨S,hS,hcard⟩ := rank_attained J w a (Finset.mem_range.mp ha)
  rw [← hcard]
  exact h a S hS

end NSSE.P0SuffixRankRecurrence
