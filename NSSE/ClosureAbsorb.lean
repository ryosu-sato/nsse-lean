import NSSE.Polarity

/-!
# Support invariance under closure (Lemma 1)  [v104]

The closure rules 1a/1b/2a/2b of [NP03] weaken literals along the
support preorder. We formalize the closed literal sets `CF`/`CL`
(base literals plus head- and component-weakenings along the base
support `S`) and prove that the support relation computed over the
closed literals coincides with the base support:

    Supp CF CL  =  Supp FLE LEF.

This is Lemma 1 of the frontier theory (notes v92). The paper-level
closure uses the support of the *growing* set; since by this theorem
that support never exceeds the base support, the two closures
coincide (bootstrapping remark, notes v92).

No `sorry`; imports only `NSSE.Polarity` (for `Supp`).
-/

namespace NSSE.ClosureAbsorb

open NSSE.Polarity

universe u
variable {V : Type u}
variable (FLE LEF : V → V → V → Prop)

/-- Base support. -/
abbrev S := Supp FLE LEF

/-- Closed lower literals: base, head weakening (rule 1a),
    component weakening (rule 2a). -/
inductive CF : V → V → V → Prop where
  | base {a₁ a₂ a} : FLE a₁ a₂ a → CF a₁ a₂ a
  | w1a {a₁ a₂ a y} : CF a₁ a₂ a → S FLE LEF a y → CF a₁ a₂ y
  | w2a {a₁ a₂ a y₁ y₂} :
      CF a₁ a₂ a → S FLE LEF y₁ a₁ → S FLE LEF y₂ a₂ → CF y₁ y₂ a

/-- Closed upper literals: base, head weakening (1b), component
    weakening (2b). -/
inductive CL : V → V → V → Prop where
  | base {b b₁ b₂} : LEF b b₁ b₂ → CL b b₁ b₂
  | w1b {b b₁ b₂ y} : CL b b₁ b₂ → S FLE LEF y b → CL y b₁ b₂
  | w2b {b b₁ b₂ y₁ y₂} :
      CL b b₁ b₂ → S FLE LEF b₁ y₁ → S FLE LEF b₂ y₂ → CL b y₁ y₂

/-- Key absorption lemma: a decomposition through closed literals is
    derivable in the base support. -/
theorem decomp_absorb :
    ∀ {a₁ a₂ a}, CF FLE LEF a₁ a₂ a →
    ∀ {b b₁ b₂}, CL FLE LEF b b₁ b₂ →
    S FLE LEF a b →
    S FLE LEF a₁ b₁ ∧ S FLE LEF a₂ b₂ := by
  intro a₁ a₂ a hcf
  induction hcf with
  | base hf =>
    intro b b₁ b₂ hcl
    induction hcl with
    | base hl =>
      intro hab
      exact ⟨Supp.decomp₁ hf hl hab, Supp.decomp₂ hf hl hab⟩
    | w1b hcl hS ih =>
      -- CL y b₁ b₂ from CL b b₁ b₂, S y b : premise pair (a, y)
      intro hab
      exact ih (Supp.trans hab hS)
    | w2b hcl hS₁ hS₂ ih =>
      -- CL b y₁ y₂ from CL b b₁ b₂, S b₁ y₁, S b₂ y₂
      intro hab
      obtain ⟨h₁, h₂⟩ := ih hab
      exact ⟨Supp.trans h₁ hS₁, Supp.trans h₂ hS₂⟩
  | w1a hcf hS ih =>
    -- CF a₁ a₂ y from CF a₁ a₂ a, S a y : premise pair (y, b)
    intro b b₁ b₂ hcl hyb
    exact ih hcl (Supp.trans hS hyb)
  | w2a hcf hS₁ hS₂ ih =>
    -- CF y₁ y₂ a from CF a₁ a₂ a, S y₁ a₁, S y₂ a₂
    intro b b₁ b₂ hcl hab
    obtain ⟨h₁, h₂⟩ := ih hcl hab
    exact ⟨Supp.trans hS₁ h₁, Supp.trans hS₂ h₂⟩

/-- **Lemma 1.** Support over the closed literal sets equals the base
    support. -/
theorem supp_closed_eq :
    ∀ s t, Supp (CF FLE LEF) (CL FLE LEF) s t ↔ S FLE LEF s t := by
  intro s t
  constructor
  · intro h
    induction h with
    | refl v => exact Supp.refl v
    | trans h₁ h₂ ih₁ ih₂ => exact Supp.trans ih₁ ih₂
    | decomp₁ hf hl hp ih => exact (decomp_absorb FLE LEF hf hl ih).1
    | decomp₂ hf hl hp ih => exact (decomp_absorb FLE LEF hf hl ih).2
  · intro h
    induction h with
    | refl v => exact Supp.refl v
    | trans h₁ h₂ ih₁ ih₂ => exact Supp.trans ih₁ ih₂
    | decomp₁ hf hl hp ih =>
      exact Supp.decomp₁ (CF.base hf) (CL.base hl) ih
    | decomp₂ hf hl hp ih =>
      exact Supp.decomp₂ (CF.base hf) (CL.base hl) ih

end NSSE.ClosureAbsorb
