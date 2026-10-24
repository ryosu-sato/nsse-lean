import NSSE.ContraCompleteness
import NSSE.BoundedWordEnumeration

/-! # The contravariant entailment decision: correctness and countermodel extraction (stage S4, part 4)

`ContraSoundness.decideEntails POL Q = !decideSatisfiable POL Q.constraints || decideBothSides POL Q`
(S3) is now a DECISION, unconditionally (for positive arity `d`), over arbitrary trees and over
regular trees, in the ORIGINAL coinductive contravariant order of S1:

* `decideEntails_correct : decideEntails POL Q = true ↔ Entails (treeConstructor POL) Q`
  (split on satisfiability; the satisfiable branch is `complete_of_satisfiable`, S4);
* `decideRegularEntails_correct : decideEntails POL Q = true ↔ RegularEntails POL Q`
  (the countermodel of S4 is regular);
* `decideEntails_false`: a false answer is equivalent to a REGULAR solution with `ρ x ≰ ρ y`.

Countermodel extraction mirrors the covariant `RegularCountermodelExtraction`: a per-word safety
test `wordSafe` (the clash test of the terminal gadget, `wordSafe_correct`), a terminating search
over words of increasing length AFTER a negative decision (no search on a positive one), and the
two-set graph of the gadget with original-variable root pointers (`extract`, `extract_correct`):
an explicit finite graph whose unfoldings are a solution of `φ` with `ρ x ≰ ρ y`.
-/

namespace NSSE.ContraEntailmentDecision

open SubtypeConstraints (Constraints Query)
open AbsorbingSubtypeTrees RegularSubtypeTrees
open ContraTrees ContraRegularTrees ContraConstraints ContraSupport ContraClashes ContraAutomaton
open ContraSoundness ContraGadget
open ForwardTableAutomaton (Side)

variable {n d : Nat} {POL : Polarity d}

/-! ## The decision -/

/-- **The contravariant entailment decision is correct** over arbitrary trees (original order). -/
theorem decideEntails_correct (hd : 0 < d) (Q : Query n d) :
    decideEntails POL Q = true ↔ Entails (treeConstructor POL) Q := by
  by_cases hs : Satisfiable (treeConstructor POL) Q.constraints
  · exact decideEntails_correct_of_complete Q (complete_of_satisfiable hd Q hs .left)
      (complete_of_satisfiable hd Q hs .right)
  · have hb : ContraSatisfiability.decideSatisfiable POL Q.constraints = false := by
      cases h : ContraSatisfiability.decideSatisfiable POL Q.constraints
      · rfl
      · exact absurd ((ContraSatisfiability.decideSatisfiable_correct _).mp h) hs
    simp only [decideEntails, hb, Bool.not_false, Bool.true_or, true_iff]
    exact entails_of_unsatisfiable _ Q hs

/-- A false answer has a rejected word on some side. -/
theorem false_rejected (Q : Query n d) (h : decideEntails POL Q = false) :
    Satisfiable (treeConstructor POL) Q.constraints ∧
      ∃ side w, ¬ ForwardCapAutomaton.Accepts (automaton POL Q side) w := by
  simp only [decideEntails, Bool.or_eq_false_iff, Bool.not_eq_false'] at h
  refine ⟨(ContraSatisfiability.decideSatisfiable_correct _).mp h.1, ?_⟩
  have hn : ¬ (ForwardCapAutomaton.Universal (automaton POL Q .left) ∧
      ForwardCapAutomaton.Universal (automaton POL Q .right)) := by
    rw [← decideBothSides_correct]; simp [h.2]
  by_contra hall
  push_neg at hall
  exact hn ⟨hall .left, hall .right⟩

/-- **A false answer is equivalent to a regular countermodel** in the original order. -/
theorem decideEntails_false (hd : 0 < d) (Q : Query n d) :
    decideEntails POL Q = false ↔
      ∃ ρ : Fin n → CTree POL, (∀ v, CRegular (ρ v)) ∧
        Satisfies (treeConstructor POL) Q.constraints ρ ∧ ¬ ρ Q.left ≤ ρ Q.right := by
  constructor
  · intro h
    obtain ⟨hs, side, w, hrej⟩ := false_rejected Q h
    obtain ⟨ρ, hr, hρ, hf⟩ := rejected_countermodel hd Q hs hrej
    exact ⟨ρ, hr, hρ, fun hle => hf ((le_iff_all_csafe _ _).mp hle side w)⟩
  · rintro ⟨ρ, _, hρ, hn⟩
    cases h : decideEntails POL Q
    · rfl
    · exact absurd ((decideEntails_correct hd Q).mp h ρ hρ) hn

/-- **Regular trees**: the same Boolean decides regular entailment. -/
theorem decideRegularEntails_correct (hd : 0 < d) (Q : Query n d) :
    decideEntails POL Q = true ↔ RegularEntails POL Q := by
  refine ⟨decideEntails_regular_sound Q, fun h => ?_⟩
  cases hb : decideEntails POL Q
  · obtain ⟨ρ, hr, hρ, hn⟩ := (decideEntails_false hd Q).mp hb
    exact absurd (h ρ hr hρ) hn
  · rfl

/-- `Ent_All = Ent_Reg` for one contravariant constructor of positive arity. -/
theorem entails_iff_regularEntails (hd : 0 < d) (Q : Query n d) :
    Entails (treeConstructor POL) Q ↔ RegularEntails POL Q :=
  (decideEntails_correct hd Q).symm.trans (decideRegularEntails_correct hd Q)

def entailmentDecision (hd : 0 < d) (Q : Query n d) : Decidable (Entails (treeConstructor POL) Q) :=
  decidable_of_iff _ (decideEntails_correct hd Q)

def regularEntailmentDecision (hd : 0 < d) (Q : Query n d) : Decidable (RegularEntails POL Q) :=
  decidable_of_iff _ (decideRegularEntails_correct hd Q)

theorem reflexive_decision (hd : 0 < d) (φ : Constraints n d) (x : Fin n) :
    decideEntails POL ⟨φ, x, x⟩ = true :=
  (decideEntails_correct hd _).mpr (fun _ _ => le_rfl)

/-! ## The per-word safety test -/

/-- The terminal gadget of a query, a side and a word, as a flat system. -/
def gadget (POL : Polarity d) (Q : Query n d) (side : Side) (w : List (Fin d)) :
    Constraints (size n w.length) d :=
  (ofQuery POL Q side w).theta

/-- `w` is `side`-safe iff the gadget clashes. -/
def wordSafe (POL : Polarity d) (Q : Query n d) (side : Side) (w : List (Fin d)) : Bool :=
  clashBool POL (gadget POL Q side w)

theorem wordSafe_correct (hd : 0 < d) (Q : Query n d) (side : Side) (w : List (Fin d)) :
    wordSafe POL Q side w = true ↔ QuerySafe POL Q side w := by
  let g := ofQuery POL Q side w
  rw [wordSafe, clashBool_correct]
  constructor
  · intro hc ρ hρ
    by_contra hf
    have hφ := no_clash_of_satisfiable (POL := POL) ⟨ρ, hρ⟩
    have hrej : ¬ g.Acc := fun hacc => hf (accepts_sound Q side w hacc ρ hρ)
    exact g.theta_clash_free hd hφ hrej hc
  · intro hs
    by_contra hθ
    obtain ⟨hm, hf⟩ := g.countermodel_spec hθ
    exact hf (hs _ hm)

theorem wordSafe_false (hd : 0 < d) (Q : Query n d) (side : Side) (w : List (Fin d)) :
    wordSafe POL Q side w = false ↔ ¬ QuerySafe POL Q side w := by
  rw [← wordSafe_correct hd]; simp

/-! ## Countermodel extraction AFTER a negative decision -/

def candidates (d bound : Nat) : List (Side × List (Fin d)) :=
  (wordsUpTo (finEnumeration d) bound).flatMap (fun w => [(.left, w), (.right, w)])

theorem mem_candidates (bound : Nat) (p : Side × List (Fin d)) :
    p ∈ candidates d bound ↔ p.2.length ≤ bound := by
  rcases p with ⟨s, w⟩
  cases s <;> simp [candidates, mem_wordsUpTo_iff]

def search (POL : Polarity d) (Q : Query n d) (bound : Nat) : Option (Side × List (Fin d)) :=
  (candidates d bound).find? (fun p => !wordSafe POL Q p.1 p.2)

theorem search_correct (Q : Query n d) (bound : Nat) :
    (search POL Q bound).isSome = true ↔ ∃ s w, w.length ≤ bound ∧ wordSafe POL Q s w = false := by
  simp only [search, List.find?_isSome, mem_candidates, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨s, w⟩, hlen, h⟩; exact ⟨s, w, hlen, h⟩
  · rintro ⟨s, w, hlen, h⟩; exact ⟨(s, w), hlen, h⟩

theorem search_some (Q : Query n d) (bound : Nat) (p : Side × List (Fin d))
    (h : search POL Q bound = some p) : p.2.length ≤ bound ∧ wordSafe POL Q p.1 p.2 = false := by
  have hm := List.mem_of_find?_eq_some h
  have hb := List.find?_some h
  exact ⟨(mem_candidates bound p).mp hm, by simpa only [Bool.not_eq_true'] using hb⟩

theorem search_terminates (hd : 0 < d) (Q : Query n d) (h : decideEntails POL Q = false) :
    ∃ bound, (search POL Q bound).isSome = true := by
  have hn : ¬ Entails (treeConstructor POL) Q := by
    rw [← decideEntails_correct hd]; simp [h]
  rw [entails_iff_all_safe] at hn
  obtain ⟨s, w, hw⟩ : ∃ s w, ¬ QuerySafe POL Q s w := by simpa only [not_forall] using hn
  exact ⟨w.length, (search_correct Q w.length).mpr ⟨s, w, le_rfl, (wordSafe_false hd Q s w).mpr hw⟩⟩

def searchBound (POL : Polarity d) (hd : 0 < d) (Q : Query n d) : Nat :=
  if h : decideEntails POL Q = false then Nat.find (search_terminates hd Q h) else 0

theorem searchBound_spec (hd : 0 < d) (Q : Query n d) (h : decideEntails POL Q = false) :
    (search POL Q (searchBound POL hd Q)).isSome = true := by
  rw [searchBound, dif_pos h]
  exact Nat.find_spec (search_terminates hd Q h)

/-- The rejected word, searched only after a negative decision. -/
def witness (POL : Polarity d) (hd : 0 < d) (Q : Query n d) : Option (Side × List (Fin d)) :=
  if decideEntails POL Q = false then search POL Q (searchBound POL hd Q) else none

theorem witness_some (hd : 0 < d) (Q : Query n d) (p : Side × List (Fin d))
    (h : witness POL hd Q = some p) :
    decideEntails POL Q = false ∧ p.2.length ≤ searchBound POL hd Q ∧
      wordSafe POL Q p.1 p.2 = false := by
  by_cases hf : decideEntails POL Q = false
  · exact ⟨hf, search_some Q _ p (by simpa only [witness, if_pos hf] using h)⟩
  · simp [witness, hf] at h

theorem witness_none_iff (hd : 0 < d) (Q : Query n d) :
    witness POL hd Q = none ↔ decideEntails POL Q = true := by
  constructor
  · intro hn
    by_contra ht
    have hf : decideEntails POL Q = false := by cases hb : decideEntails POL Q <;> simp_all
    have hs := searchBound_spec hd Q hf
    have he : search POL Q (searchBound POL hd Q) = none := by simpa [witness, hf] using hn
    rw [he] at hs
    cases hs
  · intro ht; simp [witness, ht]

/-- A finite-graph countermodel: the two-set graph of the terminal gadget of `(side, word)` and
root pointers for the ORIGINAL variables. -/
structure Countermodel (POL : Polarity d) (n : Nat) where
  side : Side
  word : List (Fin d)
  graph : Graph (ContraSatisfiability.State (size n word.length)) d
  roots : Fin n → ContraSatisfiability.State (size n word.length)

/-- The value of an original variable: the unfolding of the graph at its root, as a raw tree of
the ORIGINAL contravariant order. -/
def Countermodel.valuation (c : Countermodel POL n) (v : Fin n) : CTree POL :=
  ⟨c.graph.tree (c.roots v)⟩

theorem Countermodel.regular (c : Countermodel POL n) (v : Fin n) : CRegular (c.valuation v) :=
  c.graph.regular (c.roots v)

/-- The countermodel of a rejected `(side, w)`. -/
def candidate (POL : Polarity d) (Q : Query n d) (side : Side) (w : List (Fin d)) :
    Countermodel POL n :=
  ⟨side, w, ContraSatisfiability.graph POL (gadget POL Q side w),
    fun v => ContraSatisfiability.initial POL (gadget POL Q side w) (enc (Tok.orig v))⟩

theorem candidate_valuation (Q : Query n d) (side : Side) (w : List (Fin d)) :
    (candidate POL Q side w).valuation = (ofQuery POL Q side w).countermodel := rfl

def extract (POL : Polarity d) (hd : 0 < d) (Q : Query n d) : Option (Countermodel POL n) :=
  (witness POL hd Q).map (fun p => candidate POL Q p.1 p.2)

theorem extract_correct (hd : 0 < d) (Q : Query n d) (c : Countermodel POL n)
    (h : extract POL hd Q = some c) :
    (∀ v, CRegular (c.valuation v)) ∧
      Satisfies (treeConstructor POL) Q.constraints c.valuation ∧
      ¬ CSafe POL c.side (c.valuation Q.left) (c.valuation Q.right) c.word ∧
      ¬ c.valuation Q.left ≤ c.valuation Q.right ∧
      c.word.length ≤ searchBound POL hd Q := by
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some'.mp h
  obtain ⟨_, hlen, hbad⟩ := witness_some hd Q p hp
  have hθ : ¬ Clash POL (ofQuery POL Q p.1 p.2).theta := by
    intro hc
    have : wordSafe POL Q p.1 p.2 = true := (clashBool_correct _).mpr hc
    rw [hbad] at this; exact Bool.noConfusion this
  obtain ⟨hφ, hf⟩ := (ofQuery POL Q p.1 p.2).countermodel_spec hθ
  refine ⟨Countermodel.regular _, hφ, hf, fun hle => hf ((le_iff_all_csafe _ _).mp hle _ _), hlen⟩

theorem extract_none_iff (hd : 0 < d) (Q : Query n d) :
    extract POL hd Q = none ↔ Entails (treeConstructor POL) Q := by
  simp only [extract, Option.map_eq_none_iff, witness_none_iff, decideEntails_correct hd Q]

theorem extract_none_iff_regular (hd : 0 < d) (Q : Query n d) :
    extract POL hd Q = none ↔ RegularEntails POL Q :=
  (extract_none_iff hd Q).trans (entails_iff_regularEntails hd Q)

theorem extract_exists_iff_false (hd : 0 < d) (Q : Query n d) :
    (∃ c, extract POL hd Q = some c) ↔ decideEntails POL Q = false := by
  rw [← Option.isSome_iff_exists, Option.isSome_iff_ne_none]
  change (¬ extract POL hd Q = none) ↔ decideEntails POL Q = false
  rw [extract_none_iff, ← decideEntails_correct hd Q]
  cases decideEntails POL Q <;> simp

/-- The graph state count of an extracted countermodel. -/
theorem extract_state_count (c : Countermodel POL n) :
    Fintype.card (ContraSatisfiability.State (size n c.word.length)) =
      2 ^ (size n c.word.length) * 2 ^ (size n c.word.length) :=
  ContraSatisfiability.state_count

end NSSE.ContraEntailmentDecision
