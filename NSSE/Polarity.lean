/-!
# Polarity of the support relation (Lemma 5, abstract core)  [v103]

The inductive heart of the polarity lemma of the spine-frontier
theory (notes v95): variables are classified as `plain` (V_φ and
coupling variables), `leftish` (T- and F-spine nodes) or `rightish`
(G-spine nodes); if every decomposition-rule instance preserves the
polarity invariant on its conclusions (hypothesis `H`, a finite check
of the literal templates of the concrete system), then every support
pair (s, t) satisfies

    (leftOK s ∧ rightOK t)  ∨  s = t.

In particular leftish variables never occur on the right of a
non-reflexive support pair, and rightish ones never on the left.
The concrete-template check instantiating `H` for the live-unsafety
systems is notes v95 §1 (machine-verified there); its Lean
instantiation is future work.

Self-contained: no imports beyond core Lean; no `sorry`.
-/

namespace NSSE.Polarity

universe u

inductive Class | plain | leftish | rightish
deriving DecidableEq

open Class

variable {V : Type u}

def leftOK (side : V → Class) (v : V) : Prop :=
  side v = plain ∨ side v = leftish

def rightOK (side : V → Class) (v : V) : Prop :=
  side v = plain ∨ side v = rightish

/-- The polarity invariant for a pair. -/
def PolOK (side : V → Class) (s t : V) : Prop :=
  (leftOK side s ∧ rightOK side t) ∨ s = t

-- Abstract literal structure: `FLE a₁ a₂ a` stands for a lower
-- literal f(a₁,a₂) ≤ a, `LEF b b₁ b₂` for an upper literal
-- b ≤ f(b₁,b₂).
variable (FLE : V → V → V → Prop) (LEF : V → V → V → Prop)

/-- Syntactic support: reflexivity, transitivity, decomposition. -/
inductive Supp : V → V → Prop
  | refl (v : V) : Supp v v
  | trans {s w t : V} : Supp s w → Supp w t → Supp s t
  | decomp₁ {a₁ a₂ a b b₁ b₂ : V} :
      FLE a₁ a₂ a → LEF b b₁ b₂ → Supp a b → Supp a₁ b₁
  | decomp₂ {a₁ a₂ a b b₁ b₂ : V} :
      FLE a₁ a₂ a → LEF b b₁ b₂ → Supp a b → Supp a₂ b₂

variable (side : V → Class)

/-- Hypothesis on the literal templates: every decomposition instance
    whose premise pair satisfies the invariant produces conclusions
    satisfying it (both components). This is the finite check of the
    concrete system's literal shapes. -/
def TemplatesOK : Prop :=
  ∀ a₁ a₂ a b b₁ b₂, FLE a₁ a₂ a → LEF b b₁ b₂ →
    PolOK side a b →
    PolOK side a₁ b₁ ∧ PolOK side a₂ b₂

/-- **Lemma 5 (abstract).** Under `TemplatesOK`, every support pair
    satisfies the polarity invariant. -/
theorem polarity (H : TemplatesOK FLE LEF side) :
    ∀ s t, Supp FLE LEF s t → PolOK side s t := by
  intro s t h
  induction h with
  | refl v => exact Or.inr rfl
  | trans h₁ h₂ ih₁ ih₂ =>
    cases ih₁ with
    | inl hl₁ =>
      cases ih₂ with
      | inl hl₂ => exact Or.inl ⟨hl₁.1, hl₂.2⟩
      | inr he₂ => exact Or.inl (he₂ ▸ hl₁)
    | inr he₁ => exact he₁ ▸ ih₂
  | decomp₁ hf hl hp ih => exact (H _ _ _ _ _ _ hf hl ih).1
  | decomp₂ hf hl hp ih => exact (H _ _ _ _ _ _ hf hl ih).2

/-- Consequences: no leftish variable on the right, no rightish
    variable on the left, of a non-reflexive support pair. -/
theorem leftish_not_right (H : TemplatesOK FLE LEF side)
    {s t : V} (h : Supp FLE LEF s t) (hne : s ≠ t)
    (hl : side t = leftish) : False := by
  cases polarity FLE LEF side H s t h with
  | inl hok =>
    cases hok.2 with
    | inl hp => rw [hl] at hp; cases hp
    | inr hr => rw [hl] at hr; cases hr
  | inr he => exact hne he

theorem rightish_not_left (H : TemplatesOK FLE LEF side)
    {s t : V} (h : Supp FLE LEF s t) (hne : s ≠ t)
    (hr : side s = rightish) : False := by
  cases polarity FLE LEF side H s t h with
  | inl hok =>
    cases hok.1 with
    | inl hp => rw [hr] at hp; cases hp
    | inr hl => rw [hr] at hl; cases hl
  | inr he => exact hne he

end NSSE.Polarity
