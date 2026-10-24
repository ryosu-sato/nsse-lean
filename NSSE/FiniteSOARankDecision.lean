import NSSE.OriginalCapRow
import NSSE.SeededDFARow
import NSSE.NonliveBorderRank
import NSSE.ConcreteSOA

/-! # Concrete finite-DFA SOA inputs enter the complete rank decision

Both the candidate and every original anchor/root row are constructed from
actual DFAs. The output decision concerns the original SOA Avoider, not a
new acceptance proxy. The nonlive corollary derives its rank premise from
finite original candidate control.
-/

namespace NSSE.FiniteSOARankDecision

open RankAvoidanceCompiler GuardedRowFiring SymbolicGuardedBlocks

structure InputDFA (α : Type) where
  count : Nat
  automaton : NSSE.DFA α (Fin count)
  acceptDecision : DecidablePred automaton.accept

instance {α : Type} (A : InputDFA α) : DecidablePred A.automaton.accept := A.acceptDecision

structure Component (α : Type) where
  left : InputDFA α
  right : InputDFA α

def Component.denote {α : Type} (R : Component α) : NSSE.CapComponent α :=
  NSSE.CapComponent.ofDFA R.left.automaton R.right.automaton

variable {α : Type}

def toSOA (C : InputDFA α) (rows : List (Component α)) : NSSE.SOAInstance α where
  candidate := C.automaton.language
  rows := rows.map Component.denote

def problem (C : InputDFA α) (rows : List (Component α)) : Problem where
  language := AlphabetTableRows.language α
  Parameters := Empty
  states := (BlockCandidateTransport.states C.count).length
  candidate := SeededDFARow.compile C.automaton
  rowCount := rows.length
  rowStates i := (OriginalCapRow.states (rows.get i).left.count (rows.get i).right.count).length
  rows i := OriginalCapRow.compile (rows.get i).left.automaton (rows.get i).right.automaton

instance problemModel (C : InputDFA α) (rows : List (Component α)) :
    (problem C rows).language.Structure α := AlphabetTableRows.model α

theorem candidate_correct (C : InputDFA α) (rows : List (Component α))
    (p : Empty → α) (s : α) (body : List α) :
    ((problem C rows).candidate.dataNFA p).Accepts (s :: body) ↔ C.automaton.Accepts body :=
  SeededDFARow.compile_correct C.automaton p s body

theorem row_correct (C : InputDFA α) (rows : List (Component α))
    (p : Empty → α) (s : α) (body : List α) (i : Fin rows.length) :
    Fires ((problem C rows).rows i) p s body ↔ NSSE.MarkedOccurrence (rows.get i).denote body :=
  OriginalCapRow.fires_correct (rows.get i).left.automaton (rows.get i).right.automaton p s body

theorem rootCov_iff_index (C : InputDFA α) (rows : List (Component α)) (body : List α) :
    (toSOA C rows).RootCov body ↔
      ∃ i : Fin rows.length, NSSE.MarkedOccurrence (rows.get i).denote body := by
  constructor
  · rintro ⟨R, hR, hocc⟩
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hR
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hrow
    exact ⟨i, by simpa only [hi] using hocc⟩
  · rintro ⟨i, hocc⟩
    refine ⟨(rows.get i).denote, ?_, hocc⟩
    exact List.mem_map.mpr ⟨rows.get i, List.mem_iff_get.mpr ⟨i, rfl⟩, rfl⟩

/-- A concrete seed is needed only to witness a nonempty base alphabet.
The candidate permits every seed and the original cap rows ignore it. -/
theorem avoid_iff (C : InputDFA α) (rows : List (Component α)) (p : Empty → α) (seed : α) :
    Avoid (problem C rows) p ↔ ∃ body : List α, (toSOA C rows).Avoider body := by
  unfold Avoid
  simp only [candidate_correct, row_correct]
  change (∃ s body, C.automaton.Accepts body ∧
    ∀ i : Fin rows.length, ¬ NSSE.MarkedOccurrence (rows.get i).denote body) ↔
    ∃ body : List α, C.automaton.Accepts body ∧ ¬ (toSOA C rows).RootCov body
  simp only [rootCov_iff_index, not_exists]
  constructor
  · rintro ⟨_, body, hC, hrows⟩
    exact ⟨body, hC, hrows⟩
  · rintro ⟨body, hC, hrows⟩
    exact ⟨seed, body, hC, hrows⟩

theorem rankBound_of_candidate [DecidableEq α] (C : InputDFA α) (rows : List (Component α))
    (p : Empty → α) (h : Nat)
    (hb : ∀ body, C.automaton.Accepts body → TerminalBorderRank.suffixBorderRank body ≤ h) :
    RankBound (problem C rows) p h := by
  intro s body hC
  exact hb body ((candidate_correct C rows p s body).mp hC)

def decide (C : InputDFA α) (rows : List (Component α)) (h : Nat)
    [Fintype α] [DecidableEq α] : Bool :=
  FiniteRankDecision.decideAvoidance h (problem C rows)
    (AlphabetTableRows.relationDecision α) (Empty.elim : Empty → α)

theorem decide_correct (C : InputDFA α) (rows : List (Component α)) (h : Nat)
    [Fintype α] [DecidableEq α] (seed : α)
    (hb : ∀ body, C.automaton.Accepts body → TerminalBorderRank.suffixBorderRank body ≤ h) :
    decide C rows h = true ↔ ∃ body : List α, (toSOA C rows).Avoider body :=
  (FiniteRankDecision.decideAvoidance_correct h (problem C rows)
    (AlphabetTableRows.relationDecision α) (Empty.elim : Empty → α)
    (rankBound_of_candidate C rows Empty.elim h hb)).trans (avoid_iff C rows Empty.elim seed)

/-- The rank is computed from the ORIGINAL prefix-closed G-DFA state
count. Only exact inclusion of the chosen regular candidate in its
nonlive language is needed; no rank or short-word bound is supplied. -/
theorem rankBound_of_nonlive [DecidableEq α] (G C : InputDFA α) (rows : List (Component α))
    (p : Empty → α) (hpc : NonliveBorderRank.PrefixClosed G.automaton)
    (hsub : ∀ body, C.automaton.Accepts body →
      (NonliveBorderRank.nonliveDFA G.automaton).Accepts body) :
    RankBound (problem C rows) p (G.count - 2) := by
  apply rankBound_of_candidate
  intro body hC
  obtain ⟨hG, hn⟩ := (NonliveBorderRank.nonliveDFA_accepts_iff G.automaton hpc body).mp (hsub body hC)
  have hr := NonliveBorderRank.nonlive_rank_le_states_sub_two G.automaton hpc Finset.univ
    (fun _ _ => Finset.mem_univ _) hG hn
  simpa using hr

theorem decide_nonlive_correct [Fintype α] [DecidableEq α]
    (G C : InputDFA α) (rows : List (Component α)) (seed : α)
    (hpc : NonliveBorderRank.PrefixClosed G.automaton)
    (hsub : ∀ body, C.automaton.Accepts body →
      (NonliveBorderRank.nonliveDFA G.automaton).Accepts body) :
    decide C rows (G.count - 2) = true ↔ ∃ body : List α, (toSOA C rows).Avoider body :=
  (FiniteRankDecision.decideAvoidance_correct (G.count - 2) (problem C rows)
    (AlphabetTableRows.relationDecision α) (Empty.elim : Empty → α)
    (rankBound_of_nonlive G C rows Empty.elim hpc hsub)).trans (avoid_iff C rows Empty.elim seed)

end NSSE.FiniteSOARankDecision
