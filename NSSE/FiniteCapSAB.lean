import NSSE.FiniteCapLive
import NSSE.ShortAvoiderBoundReduction

/-! # An actual numeric short-avoider bound for every finite cap input

First decide whether an original uncovered word exists. Only in the positive
branch search the successive bounded word lists. The complete cap decision
proves this search terminates; no SAB or termination oracle is assumed.
The output is certified for the actual finite-DFA cap-derived SOA instance.
-/

namespace NSSE.FiniteCapSAB

open FiniteSOARankDecision FiniteDFAOperations FiniteCapFrontEnd FiniteCapLive

variable {α : Type} [Fintype α] [DecidableEq α]

def markedDecision (c : Component α) (xs : List α) : Decidable (MarkedOccurrence c.denote xs) := by
  let A := c.left.automaton.executableProductive
  let B := c.right.automaton.executableProductive
  letI : DecidablePred A.automaton.accept := c.left.acceptDecision
  letI : DecidablePred B.automaton.accept := c.right.acceptDecision
  exact decidable_of_iff (FinitePeriodicWitness (automataCapComponent A B) xs)
    ((finitePeriodicWitness_iff _ xs).trans (periodicWitness_iff_markedOccurrence _ xs))

def markedTest (c : Component α) (xs : List α) : Bool :=
  letI := markedDecision c xs
  decide (MarkedOccurrence c.denote xs)

theorem markedTest_correct (c : Component α) (xs : List α) :
    markedTest c xs = true ↔ MarkedOccurrence c.denote xs := by
  unfold markedTest
  simp only [decide_eq_true_eq]

def wordTest (E : Input α) (xs : List α) : Bool :=
  decide ((G E).automaton.Accepts xs) && !(decide ((R E).automaton.Accepts xs)) &&
    !((prepared E).rows.any (fun c => markedTest c xs))

theorem wordTest_correct (E : Input α) (xs : List α) :
    wordTest E xs = true ↔ E.denote.Uncovered xs := by
  rw [uncovered_iff]
  simp [wordTest, Bool.not_eq_true', ← Bool.not_eq_true, List.any_eq_true,
    markedTest_correct, SOAInstance.RootCov, SOAInstance.RowCovers, toSOA, and_assoc]

/-- The candidate is an actual DFA, not just a semantic predicate. -/
def soa (E : Input α) : SOAInstance α :=
  toSOA (inter (G E) (complement (R E))) (prepared E).rows

theorem uncovered_iff_avoider (E : Input α) (xs : List α) :
    E.denote.Uncovered xs ↔ (soa E).Avoider xs := by
  rw [uncovered_iff]
  change (_ ∧ _ ∧ _) ↔
    ((inter (G E) (complement (R E))).automaton.Accepts xs ∧
      ¬ (toSOA (G E) (prepared E).rows).RootCov xs)
  rw [inter_accepts, complement_accepts]
  tauto

def exactTest (E : Input α) : ExactAvoiderTest (soa E) where
  test := wordTest E
  correct xs := (wordTest_correct E xs).trans (uncovered_iff_avoider E xs)

theorem search_terminates (alphabet : Enumeration α) (E : Input α)
    (h : decideUncovered alphabet E = true) :
    ∃ n, boundedAvoiderSearch (soa E) alphabet (exactTest E) n = true := by
  obtain ⟨xs, hx⟩ := (decideUncovered_correct alphabet E).mp h
  exact ⟨xs.length, (boundedAvoiderSearch_correct (soa E) alphabet (exactTest E) xs.length).mpr
    ⟨xs, (uncovered_iff_avoider E xs).mp hx, Nat.le_refl _⟩⟩

/-- A computable NUMBER from the original finite input, not an existence-only
bound. Nat.find is invoked only after the cap decision proves a witness exists. -/
def sabBound (alphabet : Enumeration α) (E : Input α) : Nat :=
  if h : decideUncovered alphabet E = true then Nat.find (search_terminates alphabet E h) else 0

theorem sabBound_correct (alphabet : Enumeration α) (E : Input α) :
    ShortAvoiderBound (soa E) (sabBound alphabet E) := by
  intro hex
  have h : decideUncovered alphabet E = true := by
    apply (decideUncovered_correct alphabet E).mpr
    obtain ⟨xs, hx⟩ := hex
    exact ⟨xs, (uncovered_iff_avoider E xs).mpr hx⟩
  rw [sabBound, dif_pos h]
  exact (boundedAvoiderSearch_correct (soa E) alphabet (exactTest E) _).mp
    (Nat.find_spec (search_terminates alphabet E h))

theorem sabBound_original (alphabet : Enumeration α) (E : Input α) :
    (∃ xs, E.denote.Uncovered xs) →
      ∃ xs, E.denote.Uncovered xs ∧ xs.length ≤ sabBound alphabet E := by
  rintro ⟨xs, hx⟩
  obtain ⟨ys, hy, hlen⟩ := sabBound_correct alphabet E
    ⟨xs, (uncovered_iff_avoider E xs).mp hx⟩
  exact ⟨ys, (uncovered_iff_avoider E ys).mpr hy, hlen⟩

theorem sabBound_eq_zero_of_universal (alphabet : Enumeration α) (E : Input α)
    (h : E.denote.Universal) : sabBound alphabet E = 0 := by
  have hf := (decideUncovered_false_iff alphabet E).mpr h
  simp [sabBound, hf]

/-- The old v645 compression theorem now receives the computed cap-derived SAB,
the constructed exact test, and the actual alphabet enumeration. -/
def hornCertificate (alphabet : Enumeration α) (E : Input α) : HornSOARootCertificate (soa E) :=
  hornCertificateOfShortAvoiderBound (soa E) alphabet (exactTest E)
    (sabBound alphabet E) (sabBound_correct alphabet E)

end NSSE.FiniteCapSAB
