import NSSE.Erratum

/-!
# The minimal counterexample, formalized  [v102]

Instantiates Lemma E1 (`NSSE.Erratum.finality_invisibility`) on the
3-state automaton of the erratum and proves, in Lean:

* both `P` and `P⁻ = dropFinal P t` are complete and gap-universal
  (strict cap and shuffle are vacuous: there are no P-edges);
* their back translations coincide (instance of E1);
* their languages differ: `[false] ∈ L(P) \ L(P⁻)`.

Together: complete, restricted cap automata with identical back
translations and different languages exist — the formal core of the
erratum for [NP03] Proposition 16(2).
-/

namespace NSSE.Erratum.Instance

open NSSE.Erratum

inductive St | q0 | t | u
deriving DecidableEq

open St

/-- Transitions: q0 -false-> {t,u}, q0 -true-> {u}, u -b-> u. -/
def tr : St → Bool → St → Prop
  | .q0, false, .t => True
  | .q0, false, .u => True
  | .q0, true,  .u => True
  | .u,  _,    .u => True
  | _,   _,    _  => False

def P : CapAut St where
  trans := tr
  final := fun q => q = q0 ∨ q = t
  pedge := fun _ _ => False

def Pm : CapAut St := dropFinal P t

/-- Acceptance from the initial state q0 (class A; no P-edges). -/
def accepts (A : CapAut St) (w : List Bool) : Prop :=
  ∃ q', RunFrom A q0 w q' ∧ A.final q'

-- ---------- t is an invisible dead end ----------

theorem t_dead : ∀ b q', ¬ P.trans t b q' := by
  intro b q' h
  cases b <;> cases q' <;> exact h

theorem t_nosrc : ∀ q', ¬ P.pedge t q' := fun _ h => h

-- ---------- gap universality (vacuous) ----------

theorem gap_P : GapUniversal P := by
  intro q1 b q2 hnf htr hfin
  cases q1 with
  | q0 => exact absurd (Or.inl rfl) hnf
  | t  => exact absurd htr (t_dead b q2)
  | u  =>
    cases q2 with
    | q0 => cases b <;> exact absurd htr (fun h => h)
    | t  => cases b <;> exact absurd htr (fun h => h)
    | u  => cases hfin with
      | inl h => exact absurd h (by intro h; cases h)
      | inr h => exact absurd h (by intro h; cases h)

theorem gap_Pm : GapUniversal Pm := by
  intro q1 b q2 hnf htr hfin
  -- final(Pm) ⊆ final(P); non-final(P) ⊆ non-final(Pm)... we argue
  -- directly as for P: the only non-final-in-Pm states are t and u.
  cases q1 with
  | q0 => exact absurd ⟨Or.inl rfl, by intro h; cases h⟩ hnf
  | t  => exact absurd htr (t_dead b q2)
  | u  =>
    cases q2 with
    | q0 => cases b <;> exact absurd htr (fun h => h)
    | t  => cases b <;> exact absurd htr (fun h => h)
    | u  => exact absurd hfin.1 (by intro h; cases h with
              | inl h => cases h
              | inr h => cases h)

-- ---------- completeness: every word has a run ----------

theorem u_runs : ∀ w : List Bool, RunFrom P u w u := by
  intro w
  induction w with
  | nil => exact RunFrom.nil u
  | cons b w ih =>
    refine RunFrom.cons ?_ ih
    cases b <;> trivial

theorem complete_P : ∀ w : List Bool, ∃ q', RunFrom P q0 w q' := by
  intro w
  cases w with
  | nil => exact ⟨q0, RunFrom.nil q0⟩
  | cons b w =>
    refine ⟨u, RunFrom.cons ?_ (u_runs w)⟩
    cases b <;> trivial

-- (Pm has the same transitions, hence the same runs.)

-- ---------- the languages differ at [false] ----------

theorem accepts_P_false : accepts P [false] := by
  refine ⟨t, RunFrom.cons ?_ (RunFrom.nil t), Or.inr rfl⟩
  trivial

theorem not_accepts_Pm_false : ¬ accepts Pm [false] := by
  rintro ⟨q', hrun, hfin⟩
  cases hrun with
  | cons hstep hrest =>
    cases hrest
    -- now hstep : Pm.trans q0 false q'
    cases q' with
    | q0 => exact hstep
    | t  => exact hfin.2 rfl
    | u  => cases hfin.1 with
      | inl h => cases h
      | inr h => cases h

-- ---------- identical back translations (instance of E1) ----------

theorem same_phiP : ∀ L : Lit St, phiP P L ↔ phiP Pm L :=
  finality_invisibility P t gap_P t_dead t_nosrc

/-- **The erratum, formally**: two complete, gap-universal cap
automata (no P-edges, so strict-cap and shuffle are vacuous) with
identical back translations and different languages. -/
theorem erratum_core :
    (∀ L : Lit St, phiP P L ↔ phiP Pm L) ∧
    accepts P [false] ∧ ¬ accepts Pm [false] :=
  ⟨same_phiP, accepts_P_false, not_accepts_Pm_false⟩

end NSSE.Erratum.Instance
