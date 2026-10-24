import NSSE.PolarityInstance
import NSSE.ClosureAbsorb

/-!
# Theorem A′ (local decomposition of spine support pairs)  [v105]

Frontier theory, notes v92: for the live-unsafety systems, every
support pair `(s, t)` of two *spine* variables with `s ≠ t` is

* **(S) a seed** — one of the two sits at the root of its family
  (path `ε`), or
* **(M) mediated** — there is `w ∉ {s, t}` with `s R w R t`, or
* **(G) a guarded step** — both paths end in the *same* letter `i`,
  `s = fam(π·i)`, `t = fam′(κ·i)`, and the parent pair
  `(fam(π), fam′(κ))` is itself a support pair.

The paper argument is a case analysis on the *minimal* derivation of
`(s, t)`; in Lean the structural induction over the `Supp` derivation
does the same work: in the transitivity case a mediator `w ∈ {s, t}`
means one premise is `(s, t)` again, and the induction hypothesis for
that premise applies verbatim.

The concrete literal templates (`NSSE.PolarityInstance.FLE`/`LEF`) are
the ones already used for Lemma 5, so the two theorems are proved
about the *same* formal system. Composing with Lemma 1
(`ClosureAbsorb.supp_closed_eq`, v104) gives A′ for the closed system
as well (`aprime_closed`).

No `sorry`; imports only the two NSSE files above (no Mathlib).
-/

namespace NSSE.APrime

open NSSE.Polarity NSSE.PolarityInstance

universe u

variable {P : Type} [DecidableEq P]

/-- Spine variables: the family nodes. -/
def IsNode (v : V P) : Prop := ∃ f π, v = V.node f π

/-- Seed: a family node at path `ε`. -/
def Seed (v : V P) : Prop := ∃ f, v = V.node f []

set_option linter.unusedSectionVars false

theorem not_isNode_pl (p : P) : ¬ IsNode (V.pl (P := P) p) := by
  rintro ⟨f, π, h⟩; cases h

/-- The trichotomy, as a predicate on a support-like relation `R`. -/
def Concl (R : V P → V P → Prop) (s t : V P) : Prop :=
  (Seed s ∨ Seed t)
  ∨ (∃ w, w ≠ s ∧ w ≠ t ∧ R s w ∧ R w t)
  ∨ (∃ f g π κ i,
        s = V.node f (π ++ [i]) ∧ t = V.node g (κ ++ [i]) ∧
        R (V.node f π) (V.node g κ))

theorem concl_mono {R R' : V P → V P → Prop} (hmono : ∀ a b, R a b → R' a b)
    {s t : V P} : Concl R s t → Concl R' s t := by
  rintro (hS | ⟨w, hws, hwt, h₁, h₂⟩ | ⟨f, g, π, κ, i, hs, ht, hp⟩)
  · exact Or.inl hS
  · exact Or.inr (Or.inl ⟨w, hws, hwt, hmono _ _ h₁, hmono _ _ h₂⟩)
  · exact Or.inr (Or.inr ⟨f, g, π, κ, i, hs, ht, hmono _ _ hp⟩)

variable (x y u₁ z₁ u₂ z₂ u₃ z₃ : P) (PhiF PhiL : P → P → P → Prop)

/-- **Theorem A′.** Every support pair of two distinct spine variables
    is a seed pair, a mediated pair, or a same-letter guarded step. -/
theorem aprime :
    ∀ s t : V P,
      Supp (FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF) (LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL) s t →
      IsNode s → IsNode t → s ≠ t →
      Concl (Supp (FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF) (LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL)) s t := by
  intro s t h
  induction h with
  | refl v => intro _ _ hne; exact absurd rfl hne
  | @trans s w t h₁ h₂ ih₁ ih₂ =>
    intro hs ht hne
    by_cases hws : w = s
    · subst hws; exact ih₂ hs ht hne
    · by_cases hwt : w = t
      · subst hwt; exact ih₁ hs ht hne
      · exact Or.inr (Or.inl ⟨w, hws, hwt, h₁, h₂⟩)
  | @decomp₁ a₁ a₂ a b b₁ b₂ hf hl hp _ =>
    -- conclusion pair is (a₁, b₁): first components
    intro hs ht _
    cases hf with
    | phi _ => exact absurd hs (not_isNode_pl _)
    | coup3 => exact absurd hs (not_isNode_pl _)
    | coup1 => exact Or.inl (Or.inl ⟨_, rfl⟩)
    | coup2 => exact Or.inl (Or.inl ⟨_, rfl⟩)
    | skelT π =>
      cases hl with
      | phi _ => exact absurd ht (not_isNode_pl _)
      | coup1 => exact absurd ht (not_isNode_pl _)
      | coup2 => exact absurd ht (not_isNode_pl _)
      | coup3 => exact Or.inl (Or.inr ⟨_, rfl⟩)
      | skelT κ => exact Or.inr (Or.inr ⟨_, _, π, κ, false, rfl, rfl, hp⟩)
      | skelF κ => exact Or.inr (Or.inr ⟨_, _, π, κ, false, rfl, rfl, hp⟩)
      | skelG κ => exact Or.inr (Or.inr ⟨_, _, π, κ, false, rfl, rfl, hp⟩)
    | skelF π =>
      cases hl with
      | phi _ => exact absurd ht (not_isNode_pl _)
      | coup1 => exact absurd ht (not_isNode_pl _)
      | coup2 => exact absurd ht (not_isNode_pl _)
      | coup3 => exact Or.inl (Or.inr ⟨_, rfl⟩)
      | skelT κ => exact Or.inr (Or.inr ⟨_, _, π, κ, false, rfl, rfl, hp⟩)
      | skelF κ => exact Or.inr (Or.inr ⟨_, _, π, κ, false, rfl, rfl, hp⟩)
      | skelG κ => exact Or.inr (Or.inr ⟨_, _, π, κ, false, rfl, rfl, hp⟩)
    | skelG π =>
      cases hl with
      | phi _ => exact absurd ht (not_isNode_pl _)
      | coup1 => exact absurd ht (not_isNode_pl _)
      | coup2 => exact absurd ht (not_isNode_pl _)
      | coup3 => exact Or.inl (Or.inr ⟨_, rfl⟩)
      | skelT κ => exact Or.inr (Or.inr ⟨_, _, π, κ, false, rfl, rfl, hp⟩)
      | skelF κ => exact Or.inr (Or.inr ⟨_, _, π, κ, false, rfl, rfl, hp⟩)
      | skelG κ => exact Or.inr (Or.inr ⟨_, _, π, κ, false, rfl, rfl, hp⟩)
  | @decomp₂ a₁ a₂ a b b₁ b₂ hf hl hp _ =>
    -- conclusion pair is (a₂, b₂): second components
    intro hs ht _
    cases hf with
    | phi _ => exact absurd hs (not_isNode_pl _)
    | coup1 => exact absurd hs (not_isNode_pl _)
    | coup2 => exact absurd hs (not_isNode_pl _)
    | coup3 => exact absurd hs (not_isNode_pl _)
    | skelT π =>
      cases hl with
      | phi _ => exact absurd ht (not_isNode_pl _)
      | coup1 => exact absurd ht (not_isNode_pl _)
      | coup2 => exact absurd ht (not_isNode_pl _)
      | coup3 => exact absurd ht (not_isNode_pl _)
      | skelT κ => exact Or.inr (Or.inr ⟨_, _, π, κ, true, rfl, rfl, hp⟩)
      | skelF κ => exact Or.inr (Or.inr ⟨_, _, π, κ, true, rfl, rfl, hp⟩)
      | skelG κ => exact Or.inr (Or.inr ⟨_, _, π, κ, true, rfl, rfl, hp⟩)
    | skelF π =>
      cases hl with
      | phi _ => exact absurd ht (not_isNode_pl _)
      | coup1 => exact absurd ht (not_isNode_pl _)
      | coup2 => exact absurd ht (not_isNode_pl _)
      | coup3 => exact absurd ht (not_isNode_pl _)
      | skelT κ => exact Or.inr (Or.inr ⟨_, _, π, κ, true, rfl, rfl, hp⟩)
      | skelF κ => exact Or.inr (Or.inr ⟨_, _, π, κ, true, rfl, rfl, hp⟩)
      | skelG κ => exact Or.inr (Or.inr ⟨_, _, π, κ, true, rfl, rfl, hp⟩)
    | skelG π =>
      cases hl with
      | phi _ => exact absurd ht (not_isNode_pl _)
      | coup1 => exact absurd ht (not_isNode_pl _)
      | coup2 => exact absurd ht (not_isNode_pl _)
      | coup3 => exact absurd ht (not_isNode_pl _)
      | skelT κ => exact Or.inr (Or.inr ⟨_, _, π, κ, true, rfl, rfl, hp⟩)
      | skelF κ => exact Or.inr (Or.inr ⟨_, _, π, κ, true, rfl, rfl, hp⟩)
      | skelG κ => exact Or.inr (Or.inr ⟨_, _, π, κ, true, rfl, rfl, hp⟩)

/-- **A′ for the closed system.** Combining with Lemma 1 (v104): the
    closure adds no support pairs, so the trichotomy survives closure. -/
theorem aprime_closed :
    ∀ s t : V P,
      Supp (ClosureAbsorb.CF (FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF)
                             (LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL))
           (ClosureAbsorb.CL (FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF)
                             (LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL)) s t →
      IsNode s → IsNode t → s ≠ t →
      Concl (Supp (ClosureAbsorb.CF (FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF)
                                    (LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL))
                  (ClosureAbsorb.CL (FLE x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF)
                                    (LEF x y u₁ z₁ u₂ z₂ u₃ z₃ PhiL))) s t := by
  intro s t h hs ht hne
  have hbase := (ClosureAbsorb.supp_closed_eq _ _ s t).mp h
  refine concl_mono ?_ (aprime x y u₁ z₁ u₂ z₂ u₃ z₃ PhiF PhiL s t hbase hs ht hne)
  intro a b hab
  exact (ClosureAbsorb.supp_closed_eq _ _ a b).mpr hab

/-- Corollary (guarded steps consume one letter on each side): in case
    (G) the two paths shrink by the same letter, so a maximal chain of
    (G)-steps consumes a *common* word on both sides — the periodic
    diagonal of notes v90/v92. -/
theorem guarded_same_letter {R : V P → V P → Prop} {s t : V P}
    (h : Concl R s t)
    (hS : ¬ (Seed s ∨ Seed t))
    (hM : ¬ ∃ w, w ≠ s ∧ w ≠ t ∧ R s w ∧ R w t) :
    ∃ f g π κ i, s = V.node f (π ++ [i]) ∧ t = V.node g (κ ++ [i]) ∧
      R (V.node f π) (V.node g κ) := by
  rcases h with h | h | h
  · exact absurd h hS
  · exact absurd h hM
  · exact h

/-! ## Non-vacuity

The theorem quantifies over pairs of *distinct* spine variables in the
support relation; such pairs exist. Below, a concrete instance over
`P = Nat` derives `T_{0} R G_{0}` through the §3.2 coupling
(`T_ε ≤ x`, a φ-pair `x R y`, `y ≤ G_ε`) and one skeleton step, so the
hypotheses of `aprime` are inhabited and its conclusion lands in the
guarded-step case (G) with a seed parent pair. -/

namespace Nonvacuity

/-- φ supplies `f(x,x) ≤ p` and `p ≤ f(y,y)`, i.e. the pair `x R y`. -/
def phiF : Nat → Nat → Nat → Prop := fun a b c => a = 0 ∧ b = 0 ∧ c = 8
def phiL : Nat → Nat → Nat → Prop := fun c b₁ b₂ => c = 8 ∧ b₁ = 1 ∧ b₂ = 1

abbrev F' := FLE (P := Nat) 0 1 2 3 4 5 6 7 phiF
abbrev L' := LEF (P := Nat) 0 1 2 3 4 5 6 7 phiL
abbrev R' := Supp F' L'

/-- `T_ε ≤ x` (coupling 1). -/
theorem T_le_x : R' (V.node Fam.T []) (V.pl 0) :=
  Supp.decomp₁ FLE.coup1 LEF.coup1 (Supp.refl _)

/-- `x R y` (from the φ-literals). -/
theorem x_le_y : R' (V.pl 0) (V.pl 1) :=
  Supp.decomp₁ (FLE.phi ⟨rfl, rfl, rfl⟩) (LEF.phi ⟨rfl, rfl, rfl⟩) (Supp.refl _)

/-- `y ≤ G_ε` (coupling 3). -/
theorem y_le_G : R' (V.pl 1) (V.node Fam.G []) :=
  Supp.decomp₁ FLE.coup3 LEF.coup3 (Supp.refl _)

/-- The seed pair `T_ε R G_ε`. -/
theorem seed_pair : R' (V.node Fam.T []) (V.node Fam.G []) :=
  Supp.trans T_le_x (Supp.trans x_le_y y_le_G)

/-- A non-reflexive spine pair one level down: `T_0 R G_0`. -/
theorem step_pair : R' (V.node Fam.T [false]) (V.node Fam.G [false]) :=
  Supp.decomp₁ (FLE.skelT []) (LEF.skelG []) seed_pair

theorem step_isNode_left : IsNode (V.node (P := Nat) Fam.T [false]) := ⟨_, _, rfl⟩
theorem step_isNode_right : IsNode (V.node (P := Nat) Fam.G [false]) := ⟨_, _, rfl⟩
theorem step_ne :
    V.node (P := Nat) Fam.T [false] ≠ V.node (P := Nat) Fam.G [false] := by
  intro h; cases h

/-- The hypotheses of `aprime` are satisfiable, and here it yields (G). -/
theorem aprime_applies :
    Concl R' (V.node Fam.T [false]) (V.node Fam.G [false]) :=
  aprime 0 1 2 3 4 5 6 7 phiF phiL _ _ step_pair
    step_isNode_left step_isNode_right step_ne

end Nonvacuity

end NSSE.APrime
