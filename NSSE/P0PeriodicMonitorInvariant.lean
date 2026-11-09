import NSSE.P0PeriodicFutures

/-! Semantic invariants and one-letter recurrences for the permanent-ray
monitor. Origins are inclusive at the current cut; diagonal births are
recorded separately, since they need no pure-suffix hypothesis. -/
namespace NSSE.P0PeriodicMonitorInvariant
open P0ProperMachine P0PeriodicDriver P0PeriodicFutures
variable {Q A H : Type*} {r : Nat}

theorem pure_succ (hr : 0 < r) (cycle : Fin r → A) (z : Nat → A)
    (a n : Nat) (ha : a ≤ n) (p : Fin r) :
    PureUntil hr cycle z a (n+1) p ↔
      PureUntil hr cycle z a n p ∧ z n = cycle (advance hr p (n-a)) := by
  constructor
  · intro h
    refine ⟨fun k hk => h k (by omega),?_⟩
    simpa only [show a+(n-a) = n by omega] using h (n-a) (by omega)
  · rintro ⟨h,hl⟩ k hk
    by_cases hkn : k < n-a
    · exact h k hkn
    · have he : k = n-a := by omega
      subst k
      simpa only [show a+(n-a) = n by omega] using hl

def Origin (M : Machine Q A H) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) (q : Q) (p c : Fin r) : Prop :=
  ∃ a, a ≤ n ∧ run M z a = q ∧ PureUntil hr cycle z a n p ∧ advance hr p (n-a) = c

def Hit (M : Machine Q A H) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) (c : Fin r) : Prop :=
  ∃ a b, ∃ p : Fin r, a ≤ b ∧ b ≤ n ∧ M.birth (run M z a) (run M z b) ∧
    PureUntil hr cycle z a n p ∧ RotationEq hr cycle p (advance hr p (b-a)) ∧
    advance hr p (n-a) = c

def Diagonal (M : Machine Q A H) (z : Nat → A) (n : Nat) : Prop :=
  ∃ a, a ≤ n ∧ M.birth (run M z a) (run M z a)

def Permanent (M : Machine Q A H) (z : Nat → A) (n : Nat) : Prop :=
  ∃ a b, a ≤ b ∧ b ≤ n ∧ M.birth (run M z a) (run M z b) ∧
    ∀ k, z (a+k) = z (b+k)

theorem origin_zero (M : Machine Q A H) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (q : Q) (p c : Fin r) :
    Origin M hr cycle z 0 q p c ↔ M.initial = q ∧ p = c := by
  constructor
  · rintro ⟨a,ha,hq,_,hc⟩
    have he : a = 0 := by omega
    subst a
    simpa using And.intro hq hc
  · rintro ⟨hq,hpc⟩
    exact ⟨0,by omega,hq,fun k hk => by omega,by simpa using hpc⟩

theorem origin_succ (M : Machine Q A H) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) (q : Q) (p c : Fin r) :
    Origin M hr cycle z (n+1) q p c ↔
      (run M z (n+1) = q ∧ p = c) ∨
      ∃ d : Fin r, Origin M hr cycle z n q p d ∧ cycle d = z n ∧ advance hr d 1 = c := by
  constructor
  · rintro ⟨a,ha,hq,hpure,hc⟩
    by_cases he : a = n+1
    · subst a
      exact Or.inl ⟨hq,by simpa using hc⟩
    · have han : a ≤ n := by omega
      obtain ⟨hp,hl⟩ := (pure_succ hr cycle z a n han p).mp hpure
      refine Or.inr ⟨advance hr p (n-a),⟨a,han,hq,hp,rfl⟩,hl.symm,?_⟩
      rw [advance_add,show n-a+1 = n+1-a by omega]
      exact hc
  · rintro (⟨hq,hpc⟩ | ⟨d,⟨a,ha,hq,hp,hd⟩,hl,hc⟩)
    · exact ⟨n+1,by omega,hq,fun k hk => by omega,by simpa using hpc⟩
    · refine ⟨a,by omega,hq,(pure_succ hr cycle z a n ha p).mpr ⟨hp,?_⟩,?_⟩
      · rw [hd]
        exact hl.symm
      · rw [show n+1-a = (n-a)+1 by omega,← advance_add,hd]
        exact hc

theorem hit_zero (M : Machine Q A H) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (c : Fin r) :
    Hit M hr cycle z 0 c ↔ M.birth M.initial M.initial := by
  constructor
  · rintro ⟨a,b,p,hab,hb,hborn,_⟩
    have ha : a = 0 := by omega
    have he : b = 0 := by omega
    simpa [ha,he] using hborn
  · intro h
    refine ⟨0,0,c,by omega,by omega,h,fun k hk => by omega,?_,?_⟩
    · simp only [Nat.sub_self,advance_zero]
      exact fun _ => rfl
    · simp

theorem hit_succ (M : Machine Q A H) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) (c : Fin r) :
    Hit M hr cycle z (n+1) c ↔
      (∃ d : Fin r, Hit M hr cycle z n d ∧ cycle d = z n ∧ advance hr d 1 = c) ∨
      ∃ q p, Origin M hr cycle z (n+1) q p c ∧
        M.birth q (run M z (n+1)) ∧ RotationEq hr cycle p c := by
  constructor
  · rintro ⟨a,b,p,hab,hbn,hborn,hpure,hrot,hc⟩
    by_cases hb : b = n+1
    · subst b
      refine Or.inr ⟨run M z a,p,⟨a,hab,rfl,hpure,hc⟩,hborn,?_⟩
      rwa [hc] at hrot
    · have hbn' : b ≤ n := by omega
      have han : a ≤ n := by omega
      obtain ⟨hp,hl⟩ := (pure_succ hr cycle z a n han p).mp hpure
      refine Or.inl ⟨advance hr p (n-a),⟨a,b,p,hab,hbn',hborn,hp,hrot,rfl⟩,hl.symm,?_⟩
      rw [advance_add,show n-a+1 = n+1-a by omega]
      exact hc
  · rintro (⟨d,⟨a,b,p,hab,hbn,hborn,hpure,hrot,hd⟩,hl,hc⟩ |
      ⟨q,p,⟨a,han,hq,hpure,hc⟩,hborn,hrot⟩)
    · refine ⟨a,b,p,hab,by omega,hborn,?_,hrot,?_⟩
      · apply (pure_succ hr cycle z a n (by omega) p).mpr
        exact ⟨hpure,by rw [hd]; exact hl.symm⟩
      · rw [show n+1-a = n-a+1 by omega,← advance_add,hd]
        exact hc
    · refine ⟨a,n+1,p,han,by omega,?_,hpure,?_,hc⟩
      · rwa [hq]
      · rwa [hc]

theorem diagonal_zero (M : Machine Q A H) (z : Nat → A) :
    Diagonal M z 0 ↔ M.birth M.initial M.initial := by
  simp [Diagonal]

theorem diagonal_succ (M : Machine Q A H) (z : Nat → A) (n : Nat) :
    Diagonal M z (n+1) ↔ Diagonal M z n ∨ M.birth (run M z (n+1)) (run M z (n+1)) := by
  constructor
  · rintro ⟨a,ha,h⟩
    by_cases he : a = n+1
    · exact Or.inr (he ▸ h)
    · exact Or.inl ⟨a,by omega,h⟩
  · rintro (⟨a,ha,h⟩ | h)
    · exact ⟨a,by omega,h⟩
    · exact ⟨n+1,by omega,h⟩

theorem permanent_iff (M : Machine Q A H) (z : Nat → A) (n : Nat)
    (hr : 0 < r) (cycle : Fin r → A) (hp : PeriodicFrom z n r hr cycle) :
    Permanent M z n ↔ Diagonal M z n ∨ Hit M hr cycle z n (phase r hr 0) := by
  constructor
  · rintro ⟨a,b,hab,hbn,hborn,he⟩
    by_cases heq : a = b
    · subst b
      exact Or.inl ⟨a,hbn,hborn⟩
    · obtain ⟨p,hpure,halign,hrot⟩ :=
        (equal_futures_iff z n r hr cycle hp a b (by omega) hbn).mp he
      exact Or.inr ⟨a,b,p,hab,hbn,hborn,hpure,hrot,halign⟩
  · rintro (⟨a,ha,hborn⟩ | ⟨a,b,p,hab,hbn,hborn,hpure,hrot,halign⟩)
    · exact ⟨a,a,by omega,ha,hborn,fun _ => rfl⟩
    · refine ⟨a,b,hab,hbn,hborn,?_⟩
      by_cases heq : a = b
      · subst b
        exact fun _ => rfl
      · exact (equal_futures_iff z n r hr cycle hp a b (by omega) hbn).mpr
          ⟨p,hpure,halign,hrot⟩

end NSSE.P0PeriodicMonitorInvariant
