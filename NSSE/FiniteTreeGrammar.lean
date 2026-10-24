import NSSE.FiniteSubtypeTrees

/-! # Finite grammars with a uniform finite unfolding bound

A decreasing measure on the good states proves stabilization after at
most the number of grammar states. The measure is proof data only; the
actual finite unfolding does not compute or take it as an argument.
-/

namespace NSSE.FiniteTreeGrammar

open FiniteSubtypeTrees

inductive Label | bot | node | top
  deriving DecidableEq

structure Grammar (S : Type*) (d : Nat) where
  label : S → Label
  next : S → Fin d → S

variable {S : Type*} {d : Nat}

def unfold (G : Grammar S d) : Nat → S → Tree d
  | 0, _ => .bot
  | k + 1, s => match G.label s with
    | .bot => .bot
    | .top => .top
    | .node => .node (fun i => unfold G k (G.next s i))

section Finite

variable [Fintype S]

def lowerCount (μ : S → Nat) (s : S) : Nat :=
  (Finset.univ.filter (fun r => μ r < μ s)).card

theorem lowerCount_lt_card (μ : S → Nat) (s : S) : lowerCount μ s < Fintype.card S := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro he
  have h : s ∈ Finset.univ.filter (fun r => μ r < μ s) := by rw [he]; exact Finset.mem_univ s
  simp at h

theorem lowerCount_strict (μ : S → Nat) {a b : S} (h : μ a < μ b) :
    lowerCount μ a < lowerCount μ b := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2.trans h⟩
  · intro he
    have hb : a ∈ Finset.univ.filter (fun r => μ r < μ b) := by simp [h]
    rw [← he] at hb
    simp at hb

theorem unfold_stable (G : Grammar S d) (Good : S → Prop) (μ : S → Nat)
    (hnext : ∀ s, Good s → G.label s = .node → ∀ i, Good (G.next s i))
    (hdec : ∀ s, Good s → G.label s = .node → ∀ i, μ (G.next s i) < μ s)
    (k : Nat) : ∀ s, Good s → lowerCount μ s < k → unfold G k s = unfold G (k + 1) s := by
  induction k with
  | zero => intro s _ h; omega
  | succ k ih =>
      intro s hs hk
      cases he : G.label s with
      | bot => simp [unfold, he]
      | top => simp [unfold, he]
      | node =>
          simp only [unfold, he]
          congr 1
          funext i
          apply ih _ (hnext s hs he i)
          have := lowerCount_strict μ (hdec s hs he i)
          omega

/-- Uniform equation at the literal number of finite control states. -/
theorem unfold_equation (G : Grammar S d) (Good : S → Prop) (μ : S → Nat)
    (hnext : ∀ s, Good s → G.label s = .node → ∀ i, Good (G.next s i))
    (hdec : ∀ s, Good s → G.label s = .node → ∀ i, μ (G.next s i) < μ s)
    (s : S) (hs : Good s) :
    unfold G (Fintype.card S) s = match G.label s with
      | .bot => .bot
      | .top => .top
      | .node => .node (fun i => unfold G (Fintype.card S) (G.next s i)) := by
  rw [unfold_stable G Good μ hnext hdec _ s hs (lowerCount_lt_card μ s)]
  rfl

end Finite

end NSSE.FiniteTreeGrammar
