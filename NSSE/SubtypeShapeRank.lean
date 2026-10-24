import NSSE.SubtypePairRank
import NSSE.FiniteSubtypeSmallModel

/-! # A quadratic proof rank for the ACTUAL two-set shape grammar

Coherence is syntactic support of every lower/upper pair. No satisfying
valuation is used to obtain the uniform finite unfolding equation.
-/

namespace NSSE.SubtypeShapeRank

open SubtypeConstraints SubtypeShapeGrammar SubtypePairRank SubtypeCycleClashes
open FiniteTreeGrammar FiniteSubtypeTrees

variable {n d : Nat}

def Coherent (φ : Constraints n d) (s : State n) : Prop :=
  ∀ a ∈ s.1, ∀ b ∈ s.2, Support φ a b

theorem initial_coherent (φ : Constraints n d) (x : Fin n) : Coherent φ (initial φ x) := by
  intro a ha b hb
  exact ((mem_down φ x a).mp ha).trans ((mem_up φ x b).mp hb)

theorem next_coherent (φ : Constraints n d) {s : State n} (hs : Coherent φ s) (i : Fin d) :
    Coherent φ ((grammar φ).next s i) := by
  intro a ha b hb
  obtain ⟨l,hl,hlL,hal⟩ := (mem_lowStep φ s.1 i a).mp ha
  obtain ⟨u,hu,huU,hub⟩ := (mem_highStep φ s.2 i b).mp hb
  exact hal.trans ((Support.decomp hl hu (hs l.1 hlL u.1 huU) i).trans hub)

def measure (μ : (Fin n × Fin n) → Nat) (s : State n) : Nat :=
  (Finset.product s.1 s.2).sup (fun p => 1 + μ p)

theorem measure_bound (μ : (Fin n × Fin n) → Nat) (hμ : ∀ p, μ p < n * n) (s : State n) :
    measure μ s ≤ n * n := by
  apply Finset.sup_le
  intro p _
  have := hμ p
  omega

theorem measure_pos (φ : Constraints n d) (μ : (Fin n × Fin n) → Nat)
    (s : State n) (hn : (grammar φ).label s = .node) : 0 < measure μ s := by
  obtain ⟨⟨l,_,hl⟩,⟨u,_,hu⟩⟩ := (FiniteSubtypeSmallModel.label_node_iff φ s).mp hn
  have hh : 1 + μ (l.1,u.1) ≤ measure μ s :=
    Finset.le_sup (f := fun p => 1 + μ p) (Finset.mem_product.mpr ⟨hl,hu⟩)
  omega

theorem measure_decreases (φ : Constraints n d) (μ : (Fin n × Fin n) → Nat)
    (hμ : ∀ p q, Reach φ p q → μ q < μ p)
    {s : State n} (hs : Coherent φ s) (hn : (grammar φ).label s = .node) (i : Fin d) :
    measure μ ((grammar φ).next s i) < measure μ s := by
  apply (Finset.sup_lt_iff (measure_pos φ μ s hn)).mpr
  rintro ⟨c,e⟩ hp
  obtain ⟨hc,he⟩ := Finset.mem_product.mp hp
  obtain ⟨l,hl,hlL,hcl⟩ := (mem_lowStep φ s.1 i c).mp hc
  obtain ⟨u,hu,huU,hue⟩ := (mem_highStep φ s.2 i e).mp he
  have hr := one_reach φ (hs l.1 hlL u.1 huU)
    (i := i) ⟨l,hl,hcl,.refl _⟩ ⟨u,hu,.refl _,hue⟩
  have hh := hμ (l.1,u.1) (c,e) hr
  have hb : 1 + μ (l.1,u.1) ≤ measure μ s :=
    Finset.le_sup (f := fun p => 1 + μ p) (Finset.mem_product.mpr ⟨hlL,huU⟩)
  omega

theorem stable_of_rank (φ : Constraints n d) (μ : State n → Nat)
    (hdec : ∀ s, Coherent φ s → (grammar φ).label s = .node →
      ∀ i, μ ((grammar φ).next s i) < μ s)
    (k : Nat) : ∀ s, Coherent φ s → μ s < k →
      unfold (grammar φ) k s = unfold (grammar φ) (k + 1) s := by
  induction k with
  | zero => intro s _ hk; omega
  | succ k ih =>
      intro s hs hk
      cases he : (grammar φ).label s with
      | bot => simp [unfold, he]
      | top => simp [unfold, he]
      | node =>
          simp only [unfold, he]
          congr 1
          funext i
          apply ih _ (next_coherent φ hs i)
          have := hdec s hs he i
          omega

/-- A SAME-fuel equation at an input-only quadratic cutoff. -/
theorem bounded_equation (φ : Constraints n d) (hc : ¬ CycleClash φ)
    (s : State n) (hs : Coherent φ s) :
    unfold (grammar φ) (n * n + 1) s = match (grammar φ).label s with
      | .bot => .bot
      | .top => .top
      | .node => .node (fun i => unfold (grammar φ) (n * n + 1) ((grammar φ).next s i)) := by
  obtain ⟨μ,hbound,hdec⟩ := exists_rank φ hc
  have hd : ∀ s, Coherent φ s → (grammar φ).label s = .node →
      ∀ i, measure μ ((grammar φ).next s i) < measure μ s := by
    intro s hs hn i
    exact measure_decreases φ μ hdec hs hn i
  have hh : measure μ s < n * n + 1 := by
    have := measure_bound μ hbound s
    omega
  rw [stable_of_rank φ (measure μ) hd (n * n + 1) s hs hh]
  rfl

theorem height_le_rank (φ : Constraints n d) (μ : State n → Nat)
    (hpos : ∀ s, (grammar φ).label s = .node → 0 < μ s)
    (hdec : ∀ s, Coherent φ s → (grammar φ).label s = .node →
      ∀ i, μ ((grammar φ).next s i) < μ s)
    (k : Nat) : ∀ s, Coherent φ s → height (unfold (grammar φ) k s) ≤ μ s := by
  induction k with
  | zero => intro s _; exact Nat.zero_le _
  | succ k ih =>
      intro s hs
      cases he : (grammar φ).label s with
      | bot => simp [unfold, he, height]
      | top => simp [unfold, he, height]
      | node =>
          simp only [unfold, he, height]
          apply Nat.succ_le_iff.mpr
          apply (Finset.sup_lt_iff (hpos s he)).mpr
          intro i _
          exact (ih _ (next_coherent φ hs i)).trans_lt (hdec s hs he i)

theorem bounded_height (φ : Constraints n d) (hc : ¬ CycleClash φ)
    (k : Nat) (s : State n) (hs : Coherent φ s) :
    height (unfold (grammar φ) k s) ≤ n * n := by
  obtain ⟨μ,hbound,hdec⟩ := exists_rank φ hc
  apply le_trans (height_le_rank φ (measure μ) (measure_pos φ μ) ?_ k s hs)
    (measure_bound μ hbound s)
  intro s hs hn i
  exact measure_decreases φ μ hdec hs hn i

end NSSE.SubtypeShapeRank
