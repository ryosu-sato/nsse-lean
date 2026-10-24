import NSSE.BlockCandidateTransport

/-! # Exact finite regular operations on the epsilon-free Row data language -/

namespace NSSE.RowRegularOperations

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks SymbolicAutomata
open GuardedBlockRelation SymbolicReachability

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {n r : Nat}

abbrev Single (L : FirstOrder.Language.{u, v}) (P : Type w) (n : Nat) :=
  Automaton L P n 1 (fun _ => 1)

def letter {D : Type*} (x : D) : Column D (fun _ : Fin 1 => 1) := ⟨0, fun _ => x⟩

theorem letter_surjective {D : Type*} : Function.Surjective (letter : D → Column D (fun _ : Fin 1 => 1)) := by
  rintro ⟨s, xs⟩
  refine ⟨xs 0, ?_⟩
  fin_cases s
  unfold letter
  congr 1
  funext i
  fin_cases i
  rfl

def toAutomaton (R : Row L P n) : Single L P n where
  initial := R.initial
  final := R.final
  silent _ _ := ⊥
  step _ := R.data

def ofAutomaton (A : Single L P n) : Row L P n where
  initial := A.epsilonFree.initial
  final := A.epsilonFree.final
  data := A.epsilonFree.step 0
  left _ _ := ⊥
  right _ _ := ⊥
  guard := ⊥

theorem toAutomaton_correct (R : Row L P n) {D : Type*} [L.Structure D]
    (p : P → D) (xs : List D) :
    (toAutomaton R).Accepts p (xs.map letter) ↔ (R.dataNFA p).Accepts xs := by
  rw [(toAutomaton R).accepts_iff_data_of_noSilent p (by intro q r; simp [toAutomaton]) (xs.map letter),
    ← mapInput_accepts]
  rfl

theorem ofAutomaton_correct (A : Single L P n) {D : Type*} [L.Structure D]
    (p : P → D) (xs : List D) :
    ((ofAutomaton A).dataNFA p).Accepts xs ↔ A.Accepts p (xs.map letter) := by
  change (mapInput (A.epsilonFree.dataInterpret p) letter).Accepts xs ↔ _
  rw [mapInput_accepts, A.epsilonFree_correct]

def complement (R : Row L P n) := ofAutomaton (SymbolicComplement.compile (toAutomaton R))

theorem complement_correct (R : Row L P n) {D : Type*} [L.Structure D]
    (p : P → D) (xs : List D) :
    ((complement R).dataNFA p).Accepts xs ↔ ¬ (R.dataNFA p).Accepts xs := by
  rw [complement, ofAutomaton_correct, SymbolicComplement.compile_correct, toAutomaton_correct]

def intersect (R : Row L P n) (S : Row L P r) :=
  ofAutomaton (SymbolicConjunction.compile (toAutomaton R) (toAutomaton S))

theorem intersect_correct (R : Row L P n) (S : Row L P r) {D : Type*} [L.Structure D]
    (p : P → D) (xs : List D) :
    ((intersect R S).dataNFA p).Accepts xs ↔ (R.dataNFA p).Accepts xs ∧ (S.dataNFA p).Accepts xs := by
  rw [intersect, ofAutomaton_correct, SymbolicConjunction.compile_correct,
    toAutomaton_correct, toAutomaton_correct]

def difference (R : Row L P n) (S : Row L P r) := intersect R (complement S)

theorem difference_correct (R : Row L P n) (S : Row L P r) {D : Type*} [L.Structure D]
    (p : P → D) (xs : List D) :
    ((difference R S).dataNFA p).Accepts xs ↔ (R.dataNFA p).Accepts xs ∧ ¬ (S.dataNFA p).Accepts xs := by
  rw [difference, intersect_correct, complement_correct]

def nonemptyFormula (R : Row L P n) : L.Formula P := (toAutomaton R).nonemptyFormula

theorem nonemptyFormula_correct (R : Row L P n) {D : Type*} [L.Structure D] (p : P → D) :
    (nonemptyFormula R).Realize p ↔ ∃ xs : List D, (R.dataNFA p).Accepts xs := by
  rw [nonemptyFormula, Automaton.realize_nonemptyFormula]
  constructor
  · rintro ⟨cs, hcs⟩
    have hex : ∃ xs : List D, xs.map letter = cs := by
      clear hcs
      induction cs with
      | nil => exact ⟨[], rfl⟩
      | cons c cs ih =>
          obtain ⟨x, hx⟩ := letter_surjective c
          obtain ⟨xs, hxs⟩ := ih
          exact ⟨x :: xs, by simp [hx, hxs]⟩
    obtain ⟨xs, rfl⟩ := hex
    exact ⟨xs, (toAutomaton_correct R p xs).mp hcs⟩
  · rintro ⟨xs, hxs⟩
    exact ⟨xs.map letter, (toAutomaton_correct R p xs).mpr hxs⟩

/-- Seed-only existence is a finite base-language formula; no word-level
recursion or satisfiability oracle is consulted. -/
def seedOnlyFormula (R : Row L P n) : L.Formula P :=
  any n (fun q => any n (fun r => R.initial q ⊓ (closeColumn (R.data q r) ⊓ R.final r)))

theorem seedOnlyFormula_correct (R : Row L P n) {D : Type*} [L.Structure D] (p : P → D) :
    (seedOnlyFormula R).Realize p ↔ ∃ x : D, (R.dataNFA p).Accepts [x] := by
  simp only [seedOnlyFormula, realize_any, Formula.realize_inf, realize_closeColumn]
  constructor
  · rintro ⟨q, r, hq, ⟨xs, hstep⟩, hr⟩
    have he : (fun _ : Fin 1 => xs 0) = xs := by funext i; fin_cases i; rfl
    refine ⟨xs 0, q, r, hq, .cons ?_ (.nil r), hr⟩
    change (R.data q r).Realize (Sum.elim p (fun _ => xs 0))
    simpa only [he] using hstep
  · rintro ⟨x, q, r, hq, hrun, hr⟩
    cases hrun with
    | cons hs ht =>
        cases ht
        exact ⟨q, r, hq, ⟨fun _ => x, hs⟩, hr⟩

end NSSE.RowRegularOperations
