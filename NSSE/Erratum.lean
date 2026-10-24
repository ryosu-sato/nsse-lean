/-!
# Finality invisibility (Lemma E1, corrected form)  [v101]

Core lemma of the erratum for Niehren–Priesnitz (I&C 2003) §12:
in a gap-universal cap automaton, the finality bit of a dead-end
state that is not a P-edge source leaves no trace in the back
translation φ_P of Table 7.

Self-contained: no imports beyond core Lean.
Letters are `Bool` (binary signature); words are `List Bool`.
-/

namespace NSSE.Erratum

universe u

/-- A cap automaton skeleton: transitions, finality, P-edges.
    (Initial state and language semantics are irrelevant to E1.) -/
structure CapAut (Q : Type u) where
  trans : Q → Bool → Q → Prop
  final : Q → Prop
  pedge : Q → Q → Prop

variable {Q : Type u}

/-- Runs from a state. -/
inductive RunFrom (A : CapAut Q) : Q → List Bool → Q → Prop
  | nil (q : Q) : RunFrom A q [] q
  | cons {q q' q'' : Q} {b : Bool} {w : List Bool} :
      A.trans q b q' → RunFrom A q' w q'' → RunFrom A q (b :: w) q''

/-- `q` is universal: every word runs from `q` to some final state. -/
def Universal (A : CapAut Q) (q : Q) : Prop :=
  ∀ w : List Bool, ∃ q', RunFrom A q w q' ∧ A.final q'

/-- Gap universality (Def. 3 of [NP03], reading resolved against the
    2004 dissertation): a transition from a non-final state into a
    final state forces the target to be universal. -/
def GapUniversal (A : CapAut Q) : Prop :=
  ∀ q₁ b q₂, ¬ A.final q₁ → A.trans q₁ b q₂ → A.final q₂ →
    Universal A q₂

/-- Literals of the back translation φ_P (Table 7), abstractly. -/
inductive Lit (Q : Type u)
  | left  (q q₁ q₂ : Q)           -- l(q) ≤ f(l(q₁), l(q₂))
  | right (q q₁ q₂ : Q)           -- f(r(q₁), r(q₂)) ≤ r(q)
  | top   (q : Q)                 -- r(q) = ⊤
  | pedg  (q : Q) (i : Bool) (q₂ : Q)  -- l(q) ≤ i[r(q₂)]

/-- Membership of a literal in φ_P per Table 7 (readings resolved
    against the dissertation, p. 101). -/
def phiP (A : CapAut Q) : Lit Q → Prop
  | Lit.left q q₁ q₂ => A.final q ∧ A.trans q false q₁ ∧ A.trans q true q₂
  | Lit.right q q₁ q₂ => A.trans q false q₁ ∧ A.trans q true q₂
  | Lit.top q' => A.final q' ∧ ∃ q b, ¬ A.final q ∧ A.trans q b q'
  | Lit.pedg q i q₂ => A.final q ∧
      ∃ q₁, A.trans q i q₁ ∧ A.pedge q₁ q₂ ∧ q₁ ≠ q₂

/-- `A` with the finality of `t` removed. -/
def dropFinal (A : CapAut Q) (t : Q) [DecidableEq Q] : CapAut Q where
  trans := A.trans
  final := fun q => A.final q ∧ q ≠ t
  pedge := A.pedge

/-- A dead end has no runs on nonempty words. -/
theorem deadEnd_not_universal (A : CapAut Q) (t : Q)
    (dead : ∀ b q', ¬ A.trans t b q') : ¬ Universal A t := by
  intro h
  obtain ⟨q', hrun, _⟩ := h [true]
  cases hrun with
  | cons hstep _ => exact dead _ _ hstep

/-- **Lemma E1 (finality invisibility, corrected).**
    If `A` is gap-universal, `t` is a dead end and not a P-edge
    source, then φ_P is identical for `A` and for `A` with `t`'s
    finality removed. -/
theorem finality_invisibility [DecidableEq Q]
    (A : CapAut Q) (t : Q)
    (gu : GapUniversal A)
    (dead : ∀ b q', ¬ A.trans t b q')
    (nosrc : ∀ q', ¬ A.pedge t q') :
    ∀ L : Lit Q, phiP A L ↔ phiP (dropFinal A t) L := by
  intro L
  cases L with
  | left q q₁ q₂ =>
    constructor
    · rintro ⟨hf, h₁, h₂⟩
      refine ⟨⟨hf, ?_⟩, h₁, h₂⟩
      rintro rfl; exact dead _ _ h₁
    · rintro ⟨⟨hf, _⟩, h₁, h₂⟩
      exact ⟨hf, h₁, h₂⟩
  | right q q₁ q₂ => exact Iff.rfl
  | top q' =>
    constructor
    · rintro ⟨hf, q, b, hnf, htr⟩
      -- q' final in A; witness q non-final in A.
      -- Case q' = t: gap universality makes t universal, contradiction.
      by_cases hq't : q' = t
      · subst hq't
        exact absurd (gu q b q' hnf htr hf)
            (deadEnd_not_universal A q' dead)
      · refine ⟨⟨hf, hq't⟩, q, b, ?_, htr⟩
        -- the witness stays non-final in A' since final' ⊆ final
        intro hcon; exact hnf hcon.1
    · rintro ⟨⟨hf, hq't⟩, q, b, hnf', htr⟩
      -- witness q non-final in A': either non-final in A, or q = t.
      by_cases hqt : q = t
      · subst hqt; exact absurd htr (dead _ _)
      · refine ⟨hf, q, b, ?_, htr⟩
        intro hfA; exact hnf' ⟨hfA, hqt⟩
  | pedg q i q₂ =>
    constructor
    · rintro ⟨hf, q₁, htr, hpe, hne⟩
      refine ⟨⟨hf, ?_⟩, q₁, htr, hpe, hne⟩
      rintro rfl; exact dead _ _ htr
    · rintro ⟨⟨hf, _⟩, q₁, htr, hpe, hne⟩
      exact ⟨hf, q₁, htr, hpe, hne⟩

end NSSE.Erratum
