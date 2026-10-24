import NSSE.FiniteEntailmentDecision
import NSSE.BoundedWordEnumeration

/-! # Total finite countermodel extraction AFTER the full negative decision

The exact existing given-word safety test is used in successive finite
lists. Full decision correctness proves this search terminates. On a true
decision no search runs. All returned trees are computed, not chosen.
-/

namespace NSSE.FiniteCountermodelExtraction

open SubtypeConstraints FiniteSubtypeTrees FiniteSubtypeSafety ForwardTableAutomaton
open FiniteEntailmentDecision FinitePathSafetyDecision

variable {n d : Nat}

def candidates (d bound : Nat) : List (Side × List (Fin d)) :=
  (wordsUpTo (finEnumeration d) bound).flatMap (fun w => [(.left,w),(.right,w)])

theorem mem_candidates (bound : Nat) (p : Side × List (Fin d)) :
    p ∈ candidates d bound ↔ p.2.length ≤ bound := by
  rcases p with ⟨s,w⟩
  cases s <;> simp [candidates, mem_wordsUpTo_iff]

def search (Q : Query n d) (bound : Nat) : Option (Side × List (Fin d)) :=
  (candidates d bound).find? (fun p => !decideSafe Q p.1 p.2)

theorem search_correct (Q : Query n d) (bound : Nat) :
    (search Q bound).isSome = true ↔
      ∃ s w, w.length ≤ bound ∧ decideSafe Q s w = false := by
  simp only [search, List.find?_isSome, mem_candidates, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨s,w⟩,hlen,h⟩; exact ⟨s,w,hlen,h⟩
  · rintro ⟨s,w,hlen,h⟩; exact ⟨(s,w),hlen,h⟩

theorem search_some (Q : Query n d) (bound : Nat) (p : Side × List (Fin d))
    (h : search Q bound = some p) : p.2.length ≤ bound ∧ decideSafe Q p.1 p.2 = false := by
  have hm := List.mem_of_find?_eq_some h
  have hb := List.find?_some h
  exact ⟨(mem_candidates bound p).mp hm, by simpa only [Bool.not_eq_true'] using hb⟩

theorem search_terminates (Q : Query n d) (hd : 0 < d) (h : decideEntails Q = false) :
    ∃ bound, (search Q bound).isSome = true := by
  obtain ⟨s,w,hw⟩ := false_unsafe_word Q hd h
  exact ⟨w.length, (search_correct Q w.length).mpr ⟨s,w,le_rfl,hw⟩⟩

def searchBound (Q : Query n d) (hd : 0 < d) : Nat :=
  if h : decideEntails Q = false then Nat.find (search_terminates Q hd h) else 0

theorem searchBound_spec (Q : Query n d) (hd : 0 < d) (h : decideEntails Q = false) :
    (search Q (searchBound Q hd)).isSome = true := by
  rw [searchBound, dif_pos h]
  exact Nat.find_spec (search_terminates Q hd h)

def witness (Q : Query n d) (hd : 0 < d) : Option (Side × List (Fin d)) :=
  if decideEntails Q = false then search Q (searchBound Q hd) else none

theorem witness_some (Q : Query n d) (hd : 0 < d) (p : Side × List (Fin d))
    (h : witness Q hd = some p) :
    decideEntails Q = false ∧ p.2.length ≤ searchBound Q hd ∧ decideSafe Q p.1 p.2 = false := by
  by_cases hf : decideEntails Q = false
  · exact ⟨hf, search_some Q _ p (by simpa only [witness, if_pos hf] using h)⟩
  · simp [witness, hf] at h

theorem witness_none_iff (Q : Query n d) (hd : 0 < d) :
    witness Q hd = none ↔ decideEntails Q = true := by
  constructor
  · intro hn
    by_contra ht
    have hf : decideEntails Q = false := by cases hb : decideEntails Q <;> simp_all
    have hs := searchBound_spec Q hd hf
    have he : search Q (searchBound Q hd) = none := by simpa [witness, hf] using hn
    rw [he] at hs
    cases hs
  · intro ht; simp [witness, ht]

structure Countermodel (n d : Nat) where
  side : Side
  word : List (Fin d)
  valuation : Fin n → Tree d

def extract (Q : Query n d) (hd : 0 < d) : Option (Countermodel n d) :=
  (witness Q hd).map (fun p => ⟨p.1,p.2,FiniteRecognition.countermodel Q p.1 p.2⟩)

theorem extract_none_iff (Q : Query n d) (hd : 0 < d) :
    extract Q hd = none ↔ Entails (constructor d) Q := by
  simp only [extract, Option.map_eq_none_iff, witness_none_iff, decideEntails_correct Q hd]

theorem extract_correct (Q : Query n d) (hd : 0 < d) (c : Countermodel n d)
    (h : extract Q hd = some c) :
    Satisfies (constructor d) Q.constraints c.valuation ∧
      ¬ Safe c.side (c.valuation Q.left) (c.valuation Q.right) c.word ∧
      ¬ c.valuation Q.left ≤ c.valuation Q.right ∧
      c.word.length ≤ searchBound Q hd ∧
      ∀ x, height (c.valuation x) ≤ (n + FiniteUnsafetyCompiler.extra c.word) *
        (n + FiniteUnsafetyCompiler.extra c.word) := by
  obtain ⟨p,hp,rfl⟩ := Option.map_eq_some'.mp h
  obtain ⟨hf,hlen,hbad⟩ := witness_some Q hd p hp
  have hs := false_satisfiable Q hf
  have hr : ¬ ForwardCapAutomaton.Accepts (ConstraintForwardTables.automaton Q p.1) p.2 := by
    rw [FiniteRecognition.accepts_iff_decideSafe Q hd p.1 p.2 hs]
    simp [hbad]
  obtain ⟨hφ,hu⟩ := FiniteRecognition.rejected_countermodel Q hd p.1 p.2 hs hr
  exact ⟨hφ,hu,fun he => hu (below_safe he p.1 p.2),hlen,
    fun x => FiniteRecognition.countermodel_height Q p.1 p.2 hs x⟩

theorem extract_exists_iff_false (Q : Query n d) (hd : 0 < d) :
    (∃ c, extract Q hd = some c) ↔ decideEntails Q = false := by
  rw [← Option.isSome_iff_exists, Option.isSome_iff_ne_none]
  change (¬ extract Q hd = none) ↔ decideEntails Q = false
  rw [extract_none_iff, ← decideEntails_correct Q hd]
  cases decideEntails Q <;> simp

/-- A NUMBER computed from Q, not a caller-supplied counterexample bound. -/
def heightBound (Q : Query n d) (hd : 0 < d) : Nat :=
  let count := n + 2 * searchBound Q hd + 4
  count * count

theorem extract_height_bound (Q : Query n d) (hd : 0 < d) (c : Countermodel n d)
    (h : extract Q hd = some c) (x : Fin n) : height (c.valuation x) ≤ heightBound Q hd := by
  obtain ⟨_,_,_,hlen,hheight⟩ := extract_correct Q hd c h
  have hcount : n + FiniteUnsafetyCompiler.extra c.word ≤ n + 2 * searchBound Q hd + 4 := by
    unfold FiniteUnsafetyCompiler.extra
    omega
  exact (hheight x).trans (Nat.mul_le_mul hcount hcount)

end NSSE.FiniteCountermodelExtraction
