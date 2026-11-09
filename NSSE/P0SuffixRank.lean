import NSSE.P0DZTrace
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold

/-! Effective same-state suffix ranks of actual D/Z words, defined by the
maximum length of a nested chain. Finite powerset enumeration keeps the
definition executable and makes maximal chains explicit proof objects. -/
namespace NSSE.P0SuffixRank
open P0DZBranch P0DZTrace
variable {Q Z A H : Type*} [DecidableEq Q] [DecidableEq A]

def Linked (J : Branch Q Z A H) (w : List A) (a b : Nat) : Prop :=
  a < b ∧ b < w.length ∧ properAt J w a = properAt J w b ∧ (w.drop b).IsPrefix (w.drop a)

instance linkedDecision (J : Branch Q Z A H) (w : List A) (a b : Nat) : Decidable (Linked J w a b) := by
  unfold Linked
  infer_instance

omit [DecidableEq Q] [DecidableEq A] in
theorem linked_trans (J : Branch Q Z A H) (w : List A) (a b c : Nat)
    (hab : Linked J w a b) (hbc : Linked J w b c) : Linked J w a c :=
  ⟨hab.1.trans hbc.1,hbc.2.1,hab.2.2.1.trans hbc.2.2.1,hbc.2.2.2.trans hab.2.2.2⟩

def Chain (J : Branch Q Z A H) (w : List A) (S : Finset Nat) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a < b → Linked J w a b

instance chainDecision (J : Branch Q Z A H) (w : List A) (S : Finset Nat) : Decidable (Chain J w S) := by
  unfold Chain
  infer_instance

def ChainAt (J : Branch Q Z A H) (w : List A) (a : Nat) (S : Finset Nat) : Prop :=
  S ⊆ Finset.range w.length ∧ a ∈ S ∧ (∀ b ∈ S, a ≤ b) ∧ Chain J w S

def chains (J : Branch Q Z A H) (w : List A) (a : Nat) : Finset (Finset Nat) :=
  (Finset.range w.length).powerset.filter (fun S => a ∈ S ∧ (∀ b ∈ S, a ≤ b) ∧ Chain J w S)

theorem mem_chains (J : Branch Q Z A H) (w : List A) (a : Nat) (S : Finset Nat) :
    S ∈ chains J w a ↔ ChainAt J w a S := by
  simp only [chains,Finset.mem_filter,Finset.mem_powerset,ChainAt]

def rank (J : Branch Q Z A H) (w : List A) (a : Nat) : Nat := (chains J w a).sup Finset.card
def maxRank (J : Branch Q Z A H) (w : List A) : Nat := (Finset.range w.length).sup (rank J w)

omit [DecidableEq Q] [DecidableEq A] in
theorem singleton_chain (J : Branch Q Z A H) (w : List A) (a : Nat) (ha : a < w.length) :
    ChainAt J w a {a} := by
  simpa [ChainAt,Chain] using ha

theorem chain_le_rank (J : Branch Q Z A H) (w : List A) (a : Nat) (S : Finset Nat)
    (h : ChainAt J w a S) : S.card ≤ rank J w a :=
  Finset.le_sup ((mem_chains J w a S).mpr h)

theorem rank_positive (J : Branch Q Z A H) (w : List A) (a : Nat) (ha : a < w.length) :
    0 < rank J w a := by
  have hh := chain_le_rank J w a {a} (singleton_chain J w a ha)
  simpa only [Finset.card_singleton] using hh

theorem rank_attained (J : Branch Q Z A H) (w : List A) (a : Nat) (ha : a < w.length) :
    ∃ S, ChainAt J w a S ∧ S.card = rank J w a := by
  have hne : (chains J w a).Nonempty := ⟨{a},(mem_chains J w a {a}).mpr (singleton_chain J w a ha)⟩
  obtain ⟨S,hS,hcard⟩ := Finset.exists_mem_eq_sup (chains J w a) hne Finset.card
  exact ⟨S,(mem_chains J w a S).mp hS,hcard.symm⟩

theorem rank_zero (J : Branch Q Z A H) (w : List A) (a : Nat) (ha : w.length ≤ a) : rank J w a = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro S hS
  have hh := (mem_chains J w a S).mp hS
  have hp := Finset.mem_range.mp (hh.1 hh.2.1)
  omega

theorem rank_le_length (J : Branch Q Z A H) (w : List A) (a : Nat) : rank J w a ≤ w.length := by
  apply Finset.sup_le
  intro S hS
  have hh := Finset.card_le_card ((mem_chains J w a S).mp hS).1
  simpa only [Finset.card_range] using hh

omit [DecidableEq Q] [DecidableEq A] in
theorem prepend (J : Branch Q Z A H) (w : List A) (a b : Nat) (hab : Linked J w a b)
    (S : Finset Nat) (hS : ChainAt J w b S) : ChainAt J w a (insert a S) := by
  refine ⟨?_,Finset.mem_insert_self ..,?_,?_⟩
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_range.mpr (hab.1.trans hab.2.1)
    · exact hS.1 hp
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact le_rfl
    · exact Nat.le_trans (Nat.le_of_lt hab.1) (hS.2.2.1 p hp)
  · intro p hp q hq hpq
    rcases Finset.mem_insert.mp hp with hpa | hpS
    · subst p
      rcases Finset.mem_insert.mp hq with hqa | hqS
      · subst q; omega
      · by_cases he : q = b
        · simpa only [he] using hab
        · have hbq := hS.2.2.1 q hqS
          exact linked_trans J w a b q hab (hS.2.2.2 b hS.2.1 q hqS (by omega))
    · rcases Finset.mem_insert.mp hq with hqa | hqS
      · subst q
        have hbp := hS.2.2.1 p hpS
        have hab' := hab.1
        omega
      · exact hS.2.2.2 p hpS q hqS hpq

theorem rank_strict (J : Branch Q Z A H) (w : List A) (a b : Nat) (hab : Linked J w a b) :
    rank J w b < rank J w a := by
  obtain ⟨S,hS,hcard⟩ := rank_attained J w b hab.2.1
  have hnot : a ∉ S := by intro ha; have hh := hS.2.2.1 a ha; have := hab.1; omega
  have hh := chain_le_rank J w a (insert a S) (prepend J w a b hab S hS)
  rw [Finset.card_insert_of_not_mem hnot,hcard] at hh
  omega

theorem rank_le_max (J : Branch Q Z A H) (w : List A) (a : Nat) (ha : a < w.length) :
    rank J w a ≤ maxRank J w := Finset.le_sup (Finset.mem_range.mpr ha)

end NSSE.P0SuffixRank
