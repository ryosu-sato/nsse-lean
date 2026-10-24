import NSSE.DirectedPrefixDeletion

/-! Reciprocal offset rays enforce equality of two positive block lengths.
The concrete original-input bridge is paper plus independently checked models. -/
namespace NSSE.ReciprocalRayEquality

/-- Match 0^a1 against the suffix of 0^c1 starting at offset b. -/
def Match (a c b : Nat) : Prop :=
  ∀ s, s≤a → (if s<a then false else true)=(if b+s<c then false else true)

theorem match_iff (a c b : Nat) (hb : b≤c) : Match a c b ↔ a+b=c := by
  constructor
  · intro hm
    have hlast := hm a (by omega)
    have hge : c≤b+a := by
      by_contra h
      simp [show b+a<c by omega] at hlast
    by_contra he
    have hs : c-b<a := by omega
    have hh := hm (c-b) (by omega)
    have heq : b+(c-b)=c := by omega
    simp [hs,heq] at hh
  · intro he
    intro s hs
    by_cases h : s<a
    · simp [h,show b+s<c by omega]
    · simp [h,show ¬ b+s<c by omega]

/-- Target births omit offset zero: only positions after its first child
are marked. This makes the inequality strict. -/
def Gate (a c : Nat) : Prop := ∃ b, 1≤b ∧ b≤c ∧ Match a c b

theorem gate_iff (a c : Nat) : Gate a c ↔ a<c := by
  constructor
  · rintro ⟨b,hb,hbc,hm⟩
    have := (match_iff a c b hbc).mp hm
    omega
  · intro h
    refine ⟨c-a,by omega,by omega,(match_iff a c (c-a) (by omega)).mpr ?_⟩
    omega

/-- Absence of both the past f-copy and the future terminal-Top copy. -/
def CounterGate (a c : Nat) : Prop := ¬ Gate a c ∧ ¬ Gate c a

theorem counter_iff (a c : Nat) : CounterGate a c ↔ a=c := by
  unfold CounterGate
  rw [gate_iff,gate_iff]
  omega

/-- Every nonempty shortening of just one positive block destroys this
counter. The statement is universal in the size, not a finite grid test. -/
theorem single_deletion_fails (n r : Nat) (hr : 0<r) (hn : r≤n) :
    CounterGate n n ∧ ¬ CounterGate (n-r) n ∧ ¬ CounterGate n (n-r) := by
  have hlt : n-r<n := Nat.sub_lt (by omega) hr
  simp only [counter_iff]
  exact ⟨trivial,ne_of_lt hlt,(ne_of_lt hlt).symm⟩

/-- Shortening both blocks together works even though either individual
shortening fails. This is a joint rewrite, not a safe sequence of singles. -/
theorem joint_deletion_succeeds (n r : Nat) (hr : 0<r) (hn : r<n) :
    ¬ CounterGate (n-r) n ∧ ¬ CounterGate n (n-r) ∧ CounterGate (n-r) (n-r) := by
  have hlt : n-r<n := Nat.sub_lt (by omega) hr
  simp only [counter_iff]
  exact ⟨ne_of_lt hlt,(ne_of_lt hlt).symm,trivial⟩

/-- There are arbitrarily large equal-length arithmetic instances that
have no safe single-block deletion, while admitting a joint deletion. -/
theorem unbounded_single_minima (bound : Nat) :
    ∃ n, bound<n ∧ 1<n ∧ CounterGate n n ∧
      (∀ r, 0<r → r<n → ¬ CounterGate (n-r) n ∧ ¬ CounterGate n (n-r)) ∧
      CounterGate (n-1) (n-1) := by
  refine ⟨bound+2,by omega,by omega,(counter_iff _ _).mpr rfl,?_,(counter_iff _ _).mpr rfl⟩
  intro r hr hn
  exact (single_deletion_fails (bound+2) r hr (by omega)).2

end NSSE.ReciprocalRayEquality
