import Mathlib.Data.Finset.Sort

/-! A finite separated family of nonempty literal deletion intervals.
The retained positions include the terminal and every interval's target. -/
namespace NSSE.P0IntervalFamily

structure Family (n : Nat) where
  intervals : List (Nat × Nat)
  valid : ∀ b ∈ intervals, b.1 < b.2 ∧ b.2 ≤ n
  separated : intervals.Pairwise (fun b d => b.2 < d.1)

variable {n : Nat}

def Removed (F : Family n) (p : Nat) : Prop :=
  ∃ b ∈ F.intervals, b.1 ≤ p ∧ p < b.2

def removedDecision (F : Family n) (p : Nat) : Decidable (Removed F p) := by
  unfold Removed
  infer_instance

attribute [local instance] removedDecision

def kept (F : Family n) : Finset Nat := (Finset.range (n+1)).filter (fun p => ¬ Removed F p)

theorem mem_kept (F : Family n) (p : Nat) : p ∈ kept F ↔ p ≤ n ∧ ¬ Removed F p := by
  simp only [kept,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]

theorem pair_cases {V : Type*} (R : V → V → Prop) (L : List V) (h : L.Pairwise R)
    (a b : V) (ha : a ∈ L) (hb : b ∈ L) : a = b ∨ R a b ∨ R b a := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
    obtain ⟨hx,hL⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with hax | haL
    · subst a
      rcases List.mem_cons.mp hb with hbx | hbL
      · exact Or.inl hbx.symm
      · exact Or.inr (Or.inl (hx b hbL))
    · rcases List.mem_cons.mp hb with hbx | hbL
      · subst b
        exact Or.inr (Or.inr (hx a haL))
      · exact ih hL haL hbL

theorem target_not_removed (F : Family n) (b : Nat × Nat) (hb : b ∈ F.intervals) :
    ¬ Removed F b.2 := by
  rintro ⟨d,hd,hlo,hhi⟩
  have hvb := F.valid b hb
  have hvd := F.valid d hd
  rcases pair_cases _ _ F.separated b d hb hd with he | hbd | hdb
  · subst d; omega
  · omega
  · omega

theorem target_kept (F : Family n) (b : Nat × Nat) (hb : b ∈ F.intervals) : b.2 ∈ kept F :=
  (mem_kept F _).mpr ⟨(F.valid b hb).2,target_not_removed F b hb⟩

theorem terminal_kept (F : Family n) : n ∈ kept F := by
  apply (mem_kept F n).mpr
  refine ⟨le_rfl,?_⟩
  rintro ⟨b,hb,hlo,hhi⟩
  have := F.valid b hb
  omega

theorem kept_nonempty (F : Family n) : (kept F).Nonempty := ⟨n,terminal_kept F⟩
theorem kept_card_pos (F : Family n) : 0 < (kept F).card := Finset.card_pos.mpr (kept_nonempty F)

theorem kept_max (F : Family n) : (kept F).max' (kept_nonempty F) = n := by
  apply le_antisymm
  · exact (kept F).max'_le (kept_nonempty F) n (fun p hp => ((mem_kept F p).mp hp).1)
  · exact (kept F).le_max' n (terminal_kept F)

theorem source_removed (F : Family n) (b : Nat × Nat) (hb : b ∈ F.intervals) : Removed F b.1 :=
  ⟨b,hb,le_rfl,(F.valid b hb).1⟩

theorem target_injective (F : Family n) (b d : Nat × Nat) (hb : b ∈ F.intervals)
    (hd : d ∈ F.intervals) (he : b.2 = d.2) : b = d := by
  have hvb := F.valid b hb
  have hvd := F.valid d hd
  rcases pair_cases _ _ F.separated b d hb hd with h | h | h
  · exact h
  · omega
  · omega

theorem kept_card_lt (F : Family n) (hne : F.intervals ≠ []) : (kept F).card < n+1 := by
  have hnon : F.intervals ≠ [] := hne
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil _ hnon
  have hv := F.valid b hb
  have hsub : kept F ⊂ Finset.range (n+1) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun p hp => Finset.mem_range.mpr (by have := ((mem_kept F p).mp hp).1; omega),?_⟩
    intro he
    have hm : b.1 ∈ kept F := by rw [he]; exact Finset.mem_range.mpr (by omega)
    exact ((mem_kept F b.1).mp hm).2 (source_removed F b hb)
  simpa only [Finset.card_range] using Finset.card_lt_card hsub

end NSSE.P0IntervalFamily
