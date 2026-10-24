import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega

/-! Periodic copied-head normalization, v1698 §1–2.
This is not a decision theorem for arbitrary multi-constructor inputs.
-/
namespace NSSE.PeriodicCopyHeadNormalization

structure Annotation (V H I : Type*) where
  upper : Set V
  lower : Set V
  head : H
  index : I

def PhasePeriodic (q : Nat → α) (T P : Nat) : Prop :=
  ∀ a b, T ≤ a → T ≤ b → Nat.ModEq P a b → q a = q b

/-- The phase formulation follows from the usual eventual shift equation. -/
theorem phase_of_shift (q : Nat → α) (T P : Nat)
    (hstep : ∀ a, T ≤ a → q (a+P) = q a) : PhasePeriodic q T P := by
  have iter : ∀ a, T ≤ a → ∀ m, q (a+P*m) = q a := by
    intro a ha m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hstep (a+P*m) (by omega), ih]
  intro a b ha hb hm
  by_cases hab : a ≤ b
  · obtain ⟨m,hmm⟩ := (Nat.modEq_iff_dvd' hab).mp hm
    have he : b = a+P*m := by omega
    rw [he,iter a ha m]
  · have hba : b ≤ a := by omega
    obtain ⟨m,hmm⟩ := (Nat.modEq_iff_dvd' hba).mp hm.symm
    have he : a = b+P*m := by omega
    rw [he,iter b hb m]

def Near (B a b : Nat) : Prop := a ≤ b + B ∧ b ≤ a + B

def Ray (q : Nat → Annotation V H I) (ell t r : Nat) : Prop :=
  (∃ v, v ∈ (q ell).upper ∧ v ∈ (q t).lower) ∧
  ∀ d, d < r → (q (ell + d)).index = (q (t + d)).index

/-- Any interval of P consecutive positions contains every residue. -/
theorem residue_in_interval (base a P : Nat) (hp : 0 < P) :
    ∃ b, base ≤ b ∧ b < base + P ∧ Nat.ModEq P b a := by
  let e := a + P - base % P
  let b := base + e % P
  have hmod := Nat.mod_lt e hp
  have hbase := Nat.mod_lt base hp
  refine ⟨b, by omega, by omega, ?_⟩
  change (base + e % P) % P = a % P
  have he : base % P + e = a + P := by dsimp [e]; omega
  calc
    (base + e % P) % P = (base % P + e) % P := by simp [Nat.add_mod]
    _ = (a + P) % P := by rw [he]
    _ = a % P := by simp

/-- The first representative in the periodic region never exceeds a
position already in that region. -/
theorem first_residue (T a P : Nat) (hp : 0 < P) (ha : T ≤ a) :
    ∃ b, T ≤ b ∧ b < T + P ∧ b ≤ a ∧ Nat.ModEq P b a := by
  obtain ⟨b,hb,hbp,hm⟩ := residue_in_interval T a P hp
  refine ⟨b,hb,hbp,?_,hm⟩
  exact hm.le_of_lt_add (by omega)

/-- Matching one transient plus one whole period forces infinite agreement. -/
theorem match_forever (q : Nat → Annotation V H I) (T P ell t r : Nat)
    (hp : 0 < P) (hq : PhasePeriodic q T P) (hr : T + P < r)
    (hm : ∀ d, d < r → (q (ell+d)).index = (q (t+d)).index) :
    ∀ d, (q (ell+d)).index = (q (t+d)).index := by
  intro d
  by_cases hd : d < T + P
  · exact hm d (by omega)
  · obtain ⟨b,hb,hbp,hmod⟩ := residue_in_interval T d P hp
    have he := hq (ell+b) (ell+d) (by omega) (by omega) (hmod.add_left ell)
    have ht := hq (t+b) (t+d) (by omega) (by omega) (hmod.add_left t)
    rw [← he, ← ht]
    exact hm b (by omega)

/-- Head-preserving ray normalization. The target is fixed, but the source
position may move. Bounds hold uniformly for every prefix length N. -/
theorem normalize (q : Nat → Annotation V H I) (T P N ell t r : Nat)
    (hp : 0 < P) (hq : PhasePeriodic q T P)
    (hs : ell+r ≤ N) (ht : t+r ≤ N) (hray : Ray q ell t r) :
    ∃ ell' t' r', ell'+r' ≤ N ∧ t'+r' = t+r ∧ Ray q ell' t' r' ∧
      (q (ell'+r')).head = (q (ell+r)).head ∧
      (Near (T+P) ell' t' ∨ r' ≤ T+P) := by
  by_cases short : r ≤ T+P
  · exact ⟨ell,t,r,hs,rfl,hray,rfl,Or.inr short⟩
  by_cases close : Near (T+P) ell t
  · exact ⟨ell,t,r,hs,rfl,hray,rfl,Or.inl close⟩
  have long : T+P < r := by omega
  have forever := match_forever q T P ell t r hp hq long hray.2
  by_cases he : T ≤ ell
  · have choice : ∃ b, T ≤ b ∧ b+r ≤ N ∧ Nat.ModEq P b ell ∧ Near (T+P) b t := by
      by_cases hlarge : T+P ≤ t
      · obtain ⟨b,hb,hbp,hmod⟩ := residue_in_interval (t+1-P) ell P hp
        refine ⟨b,by omega,by omega,hmod,?_⟩
        unfold Near
        omega
      · obtain ⟨b,hb,hbp,hba,hmod⟩ := first_residue T ell P hp he
        refine ⟨b,hb,by omega,hmod,?_⟩
        unfold Near
        omega
    obtain ⟨b,hb,hbn,hmod,hnear⟩ := choice
    have hbe : q b = q ell := hq b ell hb he hmod
    have ray : Ray q b t r := by
      constructor
      · rw [hbe]
        exact hray.1
      · intro d hd
        have hshift := hq (b+d) (ell+d) (by omega) (by omega) (hmod.add_right d)
        rw [hshift]
        exact hray.2 d hd
    have heads : (q (b+r)).head = (q (ell+r)).head :=
      congrArg Annotation.head (hq (b+r) (ell+r) (by omega) (by omega) (hmod.add_right r))
    exact ⟨b,t,r,hbn,rfl,ray,heads,Or.inl hnear⟩
  · have htt : T ≤ t := by
      unfold Near at close
      omega
    obtain ⟨b,hb,hbp,hbt,hmod⟩ := first_residue T t P hp htt
    let r' := t+r-b
    have eqsum : b+r' = t+r := by dsimp [r']; omega
    have hr' : r ≤ r' := by dsimp [r']; omega
    have hsource : ell+r' ≤ N := by omega
    have hbtq : q b = q t := hq b t hb htt hmod
    have ray : Ray q ell b r' := by
      constructor
      · rw [hbtq]
        exact hray.1
      · intro d _
        have hshift := hq (b+d) (t+d) (by omega) (by omega) (hmod.add_right d)
        rw [hshift]
        exact forever d
    have hsumMod : Nat.ModEq P (r'+b) (r+t) := by
      have : r'+b = r+t := by omega
      rw [this]
    have hrmod : Nat.ModEq P r' r := Nat.ModEq.add_right_cancel hmod hsumMod
    have heads : (q (ell+r')).head = (q (ell+r)).head :=
      congrArg Annotation.head (hq (ell+r') (ell+r) (by omega) (by omega) (hrmod.add_left ell))
    refine ⟨ell,b,r',hsource,eqsum,ray,heads,Or.inl ?_⟩
    unfold Near
    omega

/-- Concrete annotations constructed by a transient table and an absolute
residue table satisfy the periodicity hypothesis without any oracle. -/
def lasso (preTable cycle : Nat → α) (T P : Nat) (k : Nat) : α :=
  if k < T then preTable k else cycle (k % P)

theorem lasso_phase (preTable cycle : Nat → α) (T P : Nat) :
    PhasePeriodic (lasso preTable cycle T P) T P := by
  intro a b ha hb hm
  simp only [lasso, if_neg (by omega : ¬ a < T), if_neg (by omega : ¬ b < T)]
  exact congrArg cycle hm

/-- Actual finite tables, rather than an assumed infinite periodic oracle. -/
def finiteLasso (preTable : Fin T → α) (cycle : Fin P → α) (hp : 0 < P)
    (k : Nat) : α :=
  if h : k < T then preTable ⟨k,h⟩ else cycle ⟨k % P,Nat.mod_lt k hp⟩

theorem finiteLasso_phase (preTable : Fin T → α) (cycle : Fin P → α) (hp : 0 < P) :
    PhasePeriodic (finiteLasso preTable cycle hp) T P := by
  intro a b ha hb hm
  simp only [finiteLasso, dif_neg (by omega : ¬ a < T), dif_neg (by omega : ¬ b < T)]
  apply congrArg cycle
  exact Fin.ext hm

def HasHead (q : Nat → Annotation V H I) (N k : Nat) (h : H) : Prop :=
  ∃ ell t r, ell+r ≤ N ∧ t+r = k ∧ Ray q ell t r ∧ (q (ell+r)).head = h

def HasBoundedHead (q : Nat → Annotation V H I) (N k B : Nat) (h : H) : Prop :=
  ∃ ell t r, ell+r ≤ N ∧ t+r = k ∧ Ray q ell t r ∧ (q (ell+r)).head = h ∧
    (Near B ell t ∨ r ≤ B)

/-- Equality of the full copied-head predicate and its bounded approximation.
The theorem does not claim equality of individual active source positions. -/
theorem hasHead_iff_bounded (q : Nat → Annotation V H I) (T P N k : Nat) (h : H)
    (hp : 0 < P) (hq : PhasePeriodic q T P) (hk : k ≤ N) :
    HasHead q N k h ↔ HasBoundedHead q N k (T+P) h := by
  constructor
  · rintro ⟨ell,t,r,hs,ht,hray,hh⟩
    obtain ⟨ell',t',r',hs',ht',hray',hh',hb⟩ :=
      normalize q T P N ell t r hp hq hs (by omega) hray
    exact ⟨ell',t',r',hs',by omega,hray',hh'.trans hh,hb⟩
  · rintro ⟨ell,t,r,hs,ht,hray,hh,_⟩
    exact ⟨ell,t,r,hs,ht,hray,hh⟩

/-- The complete copied-head theorem for a concrete finite lasso input. -/
theorem finiteLasso_heads (preTable : Fin T → Annotation V H I)
    (cycle : Fin P → Annotation V H I) (hp : 0 < P) (N k : Nat) (h : H)
    (hk : k ≤ N) :
    HasHead (finiteLasso preTable cycle hp) N k h ↔
      HasBoundedHead (finiteLasso preTable cycle hp) N k (T+P) h :=
  hasHead_iff_bounded _ T P N k h hp (finiteLasso_phase preTable cycle hp) hk

end NSSE.PeriodicCopyHeadNormalization
