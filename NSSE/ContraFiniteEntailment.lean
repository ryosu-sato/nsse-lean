import NSSE.ContraGadgetCycles
import NSSE.ContraEntailmentDecision

/-! # Finite-tree contravariant entailment (stage S6, part 2: Theorem F)

notes_v1366 §4. Finite-tree entailment uses the SAME automata and universality tests as regular
and arbitrary trees; only the satisfiability test changes (clash or signed C4):
```
decideFiniteEntails POL Q = !decideFiniteSatisfiable POL Q.constraints || decideBothSides POL Q
```
* `decideFiniteEntails_correct : decideFiniteEntails POL Q = true ↔ Entails (finiteConstructor POL) Q`
  (`d > 0`, no premise). Soundness is S3's (`decideBothSides_finite_sound`) and S6's
  (`finiteEntails_of_decide_false`). Completeness: for finitely satisfiable `φ` (clash-free and
  C4-free) and a rejected `(w, side)`, `Θ` is clash-free (v1364 Theorem D) and C4-free (Lemma F2),
  so the explicit finite unfolding of its shape model (`finiteModel`, Theorem F1) is a finite
  solution of `Θ`; its restriction is a finite solution of `φ` with the failure at `w`
  (v1364 Lemma E).
* `decideFiniteEntails_false`: a false answer is equivalent to a finite countermodel.
* Finite countermodel extraction (`extractFinite`): the rejected word is searched only after a
  negative answer, by the same per-word gadget test `wordSafe`; the returned values are explicit
  finite trees (`FTree POL`) of height `≤ |Θ|² + 1`.
-/

namespace NSSE.ContraFiniteEntailment

open SubtypeConstraints (Constraints Query)
open ContraTrees ContraFiniteTrees ContraConstraints ContraSupport ContraClashes ContraAutomaton
open ContraSoundness ContraGadget ContraFiniteCycles ContraFiniteSatisfiability ContraEntailmentDecision
open ForwardTableAutomaton (Side)

variable {n d : Nat} {POL : Polarity d}

namespace Setup'

open ContraGadget.Setup

/-- The finite countermodel of a gadget: the explicit finite unfolding of the shape model of `Θ`,
restricted to the original variables. -/
def finiteCountermodel (g : ContraGadget.Setup n d) (v : Fin n) : FTree g.POL :=
  finiteModel g.POL g.theta (enc (Tok.orig v))

theorem finiteCountermodel_spec (g : ContraGadget.Setup n d) (hθ : ¬ Clash g.POL g.theta)
    (hc4 : ¬ SignedC4 g.POL g.theta) :
    Satisfies (finiteConstructor g.POL) g.φ (finiteCountermodel g) ∧
      ¬ CSafe g.POL g.side (toC (finiteCountermodel g g.x)) (toC (finiteCountermodel g g.y)) g.w ∧
      ¬ finiteCountermodel g g.x ≤ finiteCountermodel g g.y := by
  have hm := finiteModel_satisfies g.theta hθ hc4
  have hm' := (finite_satisfies_iff g.theta _).mp hm
  have hf := g.failure hm'
  refine ⟨g.theta_satisfies_restrict _ _ hm, hf, fun hle => hf ?_⟩
  exact (le_iff_all_csafe _ _).mp ((toC_le_iff _ _).mpr hle) _ _

theorem finiteCountermodel_height (g : ContraGadget.Setup n d) (v : Fin n) :
    height (finiteCountermodel g v) ≤ size n g.N * size n g.N + 1 :=
  height_finiteModel _ _

end Setup'

/-! ## The decision -/

/-- The finite-tree decision: no finite solution, or both sides universal. -/
def decideFiniteEntails (POL : Polarity d) (Q : Query n d) : Bool :=
  !decideFiniteSatisfiable POL Q.constraints || decideBothSides POL Q

/-- A rejected word of a finitely satisfiable query gives a finite countermodel. -/
theorem rejected_finite_countermodel (hd : 0 < d) (Q : Query n d)
    (hfs : Satisfiable (finiteConstructor POL) Q.constraints) {side : Side} {w : List (Fin d)}
    (hrej : ¬ ForwardCapAutomaton.Accepts (automaton POL Q side) w) :
    ∃ ρ : Fin n → FTree POL, Satisfies (finiteConstructor POL) Q.constraints ρ ∧
      ¬ CSafe POL side (toC (ρ Q.left)) (toC (ρ Q.right)) w ∧ ¬ ρ Q.left ≤ ρ Q.right := by
  let g := ofQuery POL Q side w
  obtain ⟨hφ, hc4⟩ := (finiteSatisfiable_iff _).mp hfs
  have hθ := g.theta_clash_free hd hφ hrej
  have hθ4 : ¬ SignedC4 POL g.theta := fun h => hc4 (g.signedC4_of_theta h)
  exact ⟨_, Setup'.finiteCountermodel_spec g hθ hθ4⟩

/-- **Theorem F** (v1366 §4): the finite-tree decision is correct. -/
theorem decideFiniteEntails_correct (hd : 0 < d) (Q : Query n d) :
    decideFiniteEntails POL Q = true ↔ Entails (finiteConstructor POL) Q := by
  by_cases hfs : Satisfiable (finiteConstructor POL) Q.constraints
  · have hb : decideFiniteSatisfiable POL Q.constraints = true :=
      (decideFiniteSatisfiable_correct _).mpr hfs
    simp only [decideFiniteEntails, hb, Bool.not_true, Bool.false_or]
    refine ⟨decideBothSides_finite_sound Q, fun h => ?_⟩
    rw [decideBothSides_correct]
    by_contra hn
    have : ∃ side w, ¬ ForwardCapAutomaton.Accepts (automaton POL Q side) w := by
      by_contra hall
      push_neg at hall
      exact hn ⟨hall .left, hall .right⟩
    obtain ⟨side, w, hrej⟩ := this
    obtain ⟨ρ, hρ, _, hn'⟩ := rejected_finite_countermodel hd Q hfs hrej
    exact hn' (h ρ hρ)
  · have hb : decideFiniteSatisfiable POL Q.constraints = false := by
      cases h : decideFiniteSatisfiable POL Q.constraints
      · rfl
      · exact absurd ((decideFiniteSatisfiable_correct _).mp h) hfs
    simp only [decideFiniteEntails, hb, Bool.not_false, Bool.true_or, true_iff]
    exact entails_of_unsatisfiable _ Q hfs

theorem decideFiniteEntails_false (hd : 0 < d) (Q : Query n d) :
    decideFiniteEntails POL Q = false ↔
      ∃ ρ : Fin n → FTree POL, Satisfies (finiteConstructor POL) Q.constraints ρ ∧
        ¬ ρ Q.left ≤ ρ Q.right := by
  have hn : ¬ Entails (finiteConstructor POL) Q ↔
      ∃ ρ : Fin n → FTree POL, Satisfies (finiteConstructor POL) Q.constraints ρ ∧
        ¬ ρ Q.left ≤ ρ Q.right := by
    simp [Entails]
  rw [← hn, ← decideFiniteEntails_correct hd Q]
  cases decideFiniteEntails POL Q <;> simp

def finiteEntailmentDecision (hd : 0 < d) (Q : Query n d) :
    Decidable (Entails (finiteConstructor POL) Q) :=
  decidable_of_iff _ (decideFiniteEntails_correct hd Q)

/-- Arbitrary-tree entailment implies finite-tree entailment, and the converse holds when the
system has no signed C4 (then both decisions coincide). -/
theorem decideFiniteEntails_of_noC4 (Q : Query n d) (hc4 : ¬ SignedC4 POL Q.constraints) :
    decideFiniteEntails POL Q = decideEntails POL Q := by
  have : decideFiniteSatisfiable POL Q.constraints =
      ContraSatisfiability.decideSatisfiable POL Q.constraints := by
    simp only [decideFiniteSatisfiable, ContraSatisfiability.decideSatisfiable]
    rw [show c4Bool POL Q.constraints = false by
      cases h : c4Bool POL Q.constraints
      · rfl
      · exact absurd ((c4Bool_correct _).mp h) hc4]
    simp
  simp [decideFiniteEntails, decideEntails, this]

/-! ## Finite countermodel extraction AFTER a negative decision -/

theorem finite_search_terminates (hd : 0 < d) (Q : Query n d)
    (h : decideFiniteEntails POL Q = false) : ∃ bound, (search POL Q bound).isSome = true := by
  simp only [decideFiniteEntails, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
  have hfs := (decideFiniteSatisfiable_correct _).mp h.1
  have hs : Satisfiable (treeConstructor POL) Q.constraints := by
    obtain ⟨ρ, hρ⟩ := hfs
    exact ⟨fun x => toC (ρ x), (finite_satisfies_iff _ ρ).mp hρ⟩
  have hn : ¬ (ForwardCapAutomaton.Universal (automaton POL Q .left) ∧
      ForwardCapAutomaton.Universal (automaton POL Q .right)) := by
    rw [← decideBothSides_correct]; simp [h.2]
  obtain ⟨side, w, hrej⟩ : ∃ side w, ¬ ForwardCapAutomaton.Accepts (automaton POL Q side) w := by
    by_contra hall
    push_neg at hall
    exact hn ⟨hall .left, hall .right⟩
  have hns : ¬ QuerySafe POL Q side w := fun hq => hrej (complete_of_satisfiable hd Q hs side w hq)
  exact ⟨w.length, (search_correct Q w.length).mpr
    ⟨side, w, le_rfl, (wordSafe_false hd Q side w).mpr hns⟩⟩

def finiteSearchBound (POL : Polarity d) (hd : 0 < d) (Q : Query n d) : Nat :=
  if h : decideFiniteEntails POL Q = false then Nat.find (finite_search_terminates hd Q h) else 0

def finiteWitness (POL : Polarity d) (hd : 0 < d) (Q : Query n d) : Option (Side × List (Fin d)) :=
  if decideFiniteEntails POL Q = false then search POL Q (finiteSearchBound POL hd Q) else none

theorem finiteWitness_some (hd : 0 < d) (Q : Query n d) (p : Side × List (Fin d))
    (h : finiteWitness POL hd Q = some p) :
    decideFiniteEntails POL Q = false ∧ wordSafe POL Q p.1 p.2 = false := by
  by_cases hf : decideFiniteEntails POL Q = false
  · exact ⟨hf, (search_some Q _ p (by simpa only [finiteWitness, if_pos hf] using h)).2⟩
  · simp [finiteWitness, hf] at h

theorem finiteWitness_none_iff (hd : 0 < d) (Q : Query n d) :
    finiteWitness POL hd Q = none ↔ decideFiniteEntails POL Q = true := by
  constructor
  · intro hn
    by_contra ht
    have hf : decideFiniteEntails POL Q = false := by cases hb : decideFiniteEntails POL Q <;> simp_all
    have hs : (search POL Q (finiteSearchBound POL hd Q)).isSome = true := by
      rw [finiteSearchBound, dif_pos hf]
      exact Nat.find_spec (finite_search_terminates hd Q hf)
    have he : search POL Q (finiteSearchBound POL hd Q) = none := by
      simpa [finiteWitness, hf] using hn
    rw [he] at hs
    cases hs
  · intro ht; simp [finiteWitness, ht]

/-- An explicit finite countermodel: finite trees for the original variables. -/
structure FiniteCountermodel (POL : Polarity d) (n : Nat) where
  side : Side
  word : List (Fin d)
  values : Fin n → FTree POL

def extractFinite (POL : Polarity d) (hd : 0 < d) (Q : Query n d) :
    Option (FiniteCountermodel POL n) :=
  (finiteWitness POL hd Q).map
    (fun p => ⟨p.1, p.2, Setup'.finiteCountermodel (ofQuery POL Q p.1 p.2)⟩)

theorem extractFinite_correct (hd : 0 < d) (Q : Query n d) (c : FiniteCountermodel POL n)
    (h : extractFinite POL hd Q = some c) :
    Satisfies (finiteConstructor POL) Q.constraints c.values ∧
      ¬ CSafe POL c.side (toC (c.values Q.left)) (toC (c.values Q.right)) c.word ∧
      ¬ c.values Q.left ≤ c.values Q.right := by
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some'.mp h
  obtain ⟨hdec, hbad⟩ := finiteWitness_some hd Q p hp
  let g := ofQuery POL Q p.1 p.2
  simp only [decideFiniteEntails, Bool.or_eq_false_iff, Bool.not_eq_false'] at hdec
  obtain ⟨hφ, hc4⟩ := (decideFiniteSatisfiable_iff _).mp hdec.1
  have hθ : ¬ Clash POL g.theta := by
    intro hc
    have : wordSafe POL Q p.1 p.2 = true := (clashBool_correct _).mpr hc
    rw [hbad] at this; exact Bool.noConfusion this
  have hθ4 : ¬ SignedC4 POL g.theta := fun h => hc4 (g.signedC4_of_theta h)
  exact Setup'.finiteCountermodel_spec g hθ hθ4

theorem extractFinite_none_iff (hd : 0 < d) (Q : Query n d) :
    extractFinite POL hd Q = none ↔ Entails (finiteConstructor POL) Q := by
  simp only [extractFinite, Option.map_eq_none_iff, finiteWitness_none_iff,
    decideFiniteEntails_correct hd Q]

end NSSE.ContraFiniteEntailment
