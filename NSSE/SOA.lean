import NSSE
import Lean.Elab.Tactic.Omega

/-!
# Abstract shortest-avoider core for SOA

This module formalizes the quantifier skeleton used in Section 3 of
`soa_decidability_proof.md`.  The concrete admissible deletion relation is
left abstract, but every declared reduction is required to preserve
candidate membership and strictly shorten the word.
-/

namespace NSSE

universe u v

structure SOAProblem (α : Type u) where
  Candidate : Word α → Prop
  RootCov : Word α → Prop
  Reduction : Word α → Word α → Prop
  reduction_candidate :
    ∀ {u w}, Reduction u w → Candidate u
  reduction_shorter :
    ∀ {u w}, Reduction u w → u.length < w.length

namespace SOAProblem

def Avoider (P : SOAProblem α) (w : Word α) : Prop :=
  P.Candidate w ∧ ¬ P.RootCov w

def AllDel (P : SOAProblem α) (w : Word α) : Prop :=
  ∀ u, P.Reduction u w → P.RootCov u

def Critical (P : SOAProblem α) (w : Word α) : Prop :=
  P.Candidate w ∧ P.AllDel w ∧ ¬ P.RootCov w

theorem critical_avoider {P : SOAProblem α} {w : Word α}
    (h : P.Critical w) : P.Avoider w :=
  ⟨h.1, h.2.2⟩

/--
Every nonempty set of finite-word avoiders has a length-minimal member,
and every admissible proper reduction of that member is covered.
-/
theorem exists_critical_iff_exists_avoider (P : SOAProblem α) :
    (∃ w, P.Critical w) ↔ ∃ w, P.Avoider w := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, critical_avoider hw⟩
  · rintro ⟨w₀, hw₀⟩
    have main :
        ∀ n, ∀ w : Word α, w.length = n → P.Avoider w →
          ∃ v, P.Critical v := by
      intro n
      induction n using Nat.strongRecOn with
      | ind n ih =>
          intro w hwlen hw
          by_cases hall : P.AllDel w
          · exact ⟨w, hw.1, hall, hw.2⟩
          · classical
            unfold AllDel at hall
            rw [Classical.not_forall] at hall
            obtain ⟨u, hu⟩ := hall
            rw [Classical.not_imp] at hu
            have hshort : u.length < n := by
              simpa [← hwlen] using P.reduction_shorter hu.1
            exact ih u.length hshort u rfl
              ⟨P.reduction_candidate hu.1, hu.2⟩
    exact main w₀.length w₀ rfl hw₀

section ForbiddenQueries

variable {β : Type v}

def Forbids (Q : β → Word α → Prop) (F : β → Prop)
    (w : Word α) : Prop :=
  ∀ τ, F τ → ¬ Q τ w

def Generalized (P : SOAProblem α) (Q : β → Word α → Prop)
    (F : β → Prop) (w : Word α) : Prop :=
  P.Candidate w ∧ P.AllDel w ∧ Forbids Q F w

/--
The semantic v406 trichotomy.  After any candidate-preserving
shortening, either `AllDel` fails and exposes an actual avoider, a
forbidden query has a concrete positive witness, or the shortened word
realizes the same generalized state.
-/
theorem candidate_trichotomy
    (P : SOAProblem α) (Q : β → Word α → Prop) (F : β → Prop)
    {u : Word α} (huCandidate : P.Candidate u) :
    (∃ v, P.Reduction v u ∧ P.Avoider v) ∨
      (∃ τ, F τ ∧ Q τ u) ∨
      P.Generalized Q F u := by
  classical
  by_cases hall : P.AllDel u
  · by_cases hforbid : Forbids Q F u
    · exact Or.inr (Or.inr ⟨huCandidate, hall, hforbid⟩)
    · right
      left
      unfold Forbids at hforbid
      rw [Classical.not_forall] at hforbid
      obtain ⟨τ, hτ⟩ := hforbid
      rw [Classical.not_imp] at hτ
      rw [Classical.not_not] at hτ
      exact ⟨τ, hτ⟩
  · left
    unfold AllDel at hall
    rw [Classical.not_forall] at hall
    obtain ⟨v, hv⟩ := hall
    rw [Classical.not_imp] at hv
    exact ⟨v, hv.1, P.reduction_candidate hv.1, hv.2⟩

/--
For a length-minimal realization, the third branch of
`candidate_trichotomy` is impossible for a proper candidate-preserving
contraction.
-/
theorem minimal_generalized_contraction
    (P : SOAProblem α) (Q : β → Word α → Prop) (F : β → Prop)
    {w u : Word α}
    (hminimal :
      ∀ v, P.Candidate v → v.length < w.length →
        ¬ P.Generalized Q F v)
    (huCandidate : P.Candidate u) (hshort : u.length < w.length) :
    (∃ v, P.Reduction v u ∧ P.Avoider v) ∨
      (∃ τ, F τ ∧ Q τ u) := by
  rcases candidate_trichotomy P Q F huCandidate with havoid | hquery | hgen
  · exact Or.inl havoid
  · exact Or.inr hquery
  · exact False.elim (hminimal u huCandidate hshort hgen)

/--
When `RootCov` is exactly existence of a canonical positive query,
forbidding the full query type is literally its negation.  No finiteness
or iterative representative replacement is needed for this logical
equivalence.
-/
theorem forbids_all_iff_not_rootCov
    (P : SOAProblem α) (Q : β → Word α → Prop)
    (hroot : ∀ w, P.RootCov w ↔ ∃ τ, Q τ w)
    (w : Word α) :
    Forbids Q (fun _ => True) w ↔ ¬ P.RootCov w := by
  rw [hroot]
  constructor
  · intro h ⟨τ, hτ⟩
    exact h τ trivial hτ
  · intro h τ _ hτ
    exact h ⟨τ, hτ⟩

theorem generalized_all_iff_critical
    (P : SOAProblem α) (Q : β → Word α → Prop)
    (hroot : ∀ w, P.RootCov w ↔ ∃ τ, Q τ w)
    (w : Word α) :
    P.Generalized Q (fun _ => True) w ↔ P.Critical w := by
  unfold Generalized Critical
  rw [forbids_all_iff_not_rootCov P Q hroot w]

end ForbiddenQueries

end SOAProblem

end NSSE
