import NSSE.DirectEmptyTailRemoval
import NSSE.DirectRowBooleanSize

/-! # Additive guard growth through actual direct empty-tail subtraction -/

namespace NSSE.DirectEmptyTailSize

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ExactReachabilitySize
open DirectRowBooleanSize ExactGuardedRunSize ComputedScalarLoweringBudget

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n B k c : Nat} {ns : Fin k → Nat}

def emptyBound (n B : Nat) := 6+B+n*(8+2*B)

theorem empty_tail_fields (R : Row L P n) (h : Fields R B) (last : P) :
    Fields (EmptyTailFiring.compile R last) (emptyBound n B) := by
  have hb : B ≤ emptyBound n B := by unfold emptyBound; omega
  have h₁ : 1 ≤ emptyBound n B := by unfold emptyBound; omega
  have hf (q : Fin n) : nodes (SymbolicReachability.any n (fun r => R.right q r ⊓ R.final r)) ≤ 1+n*(8+2*B) := by
    have hh := nodes_any_le n (5+2*B) (fun r => R.right q r ⊓ R.final r) (fun r => by
      rw [nodes_inf]; have := h.right q r; have := h.final r; omega)
    simpa only [show 3+(5+2*B) = 8+2*B by omega] using hh
  have hs (q r : Fin n) : nodes (EmptyTailFiring.switchGuard R last q r) ≤ emptyBound n B := by
    have hh := nodes_any_le n (5+2*B) (fun z => R.data q z ⊓ (R.left z r).relabel Sum.inl) (fun z => by
      rw [nodes_inf, nodes_relabel]; have := h.data q z; have := h.left z r; omega)
    simp only [show 3+(5+2*B) = 8+2*B by omega] at hh
    simp only [EmptyTailFiring.switchGuard, nodes_inf, guardAt, nodes_relabel]
    have := h.guard
    unfold emptyBound
    omega
  have hi (s : EmptyTailAutomaton.State (Fin n)) : nodes (EmptyTailFiring.initialGuard R s) ≤ emptyBound n B := by
    cases s
    · exact (h.initial _).trans hb
    · exact h₁
    · exact h₁
  have hfinal (s : EmptyTailAutomaton.State (Fin n)) : nodes (EmptyTailFiring.finalGuard R s) ≤ emptyBound n B := by
    cases s
    · exact h₁
    · exact h₁
    · exact (hf _).trans (by unfold emptyBound; omega)
  have hd (s t : EmptyTailAutomaton.State (Fin n)) : nodes (EmptyTailFiring.dataGuard R last s t) ≤ emptyBound n B := by
    cases s <;> cases t <;> simp only [EmptyTailFiring.dataGuard]
    all_goals first | exact (h.data _ _).trans hb | exact hs _ _ | exact h₁
  exact { data := fun q r => hd _ _
          initial := fun q => hi _
          final := fun q => hfinal _
          left := fun _ _ => h₁
          right := fun _ _ => h₁
          guard := h₁ }

def rowContribution (R : EmptyTailRemoval.Candidate L P) :=
  5+complementBound (3*R.1) (emptyBound R.1 (rowSize R.2))

def extra (rows : List (EmptyTailRemoval.Candidate L P)) := (rows.map rowContribution).sum

theorem subtractList_fields (C : EmptyTailRemoval.Candidate L P)
    (rows : List (EmptyTailRemoval.Candidate L P)) (last : P) (h : Fields C.2 B) :
    Fields (DirectEmptyTailRemoval.subtractList C rows last).2 (B+extra rows) := by
  induction rows generalizing C B with
  | nil => simpa only [DirectEmptyTailRemoval.subtractList, extra, List.map_nil, List.sum_nil, Nat.add_zero] using h
  | cons R rows ih =>
    have hr := of_budget R.2 (row_budget R.2)
    have hd := difference_fields C.2 (EmptyTailFiring.compile R.2 last) h (empty_tail_fields R.2 hr last)
    have hh := ih ⟨_, DirectRowBooleanOperations.difference C.2 (EmptyTailFiring.compile R.2 last)⟩ hd
    simpa only [DirectEmptyTailRemoval.subtractList, extra, List.map_cons, List.sum_cons, rowContribution,
      EmptyTailFiring.length_states, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh

theorem subtractFamily_fields (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P) :
    Fields (DirectEmptyTailRemoval.subtractFamily rows C last).2
      (rowSize C+extra (EmptyTailRemoval.rowList rows)) :=
  subtractList_fields ⟨c,C⟩ _ last (of_budget C (row_budget C))

def totalBound (N G : Nat) := N+G+N*(2*G)+N*N*(3*G)

theorem subtractFamily_size (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P) :
    rowSize (DirectEmptyTailRemoval.subtractFamily rows C last).2 ≤
      totalBound (c*((List.finRange k).map (fun i => 2^(3*ns i)+1)).prod)
        (rowSize C+extra (EmptyTailRemoval.rowList rows)) := by
  have h := subtractFamily_fields rows C last
  have hh := RankNextGuardSize.rowSize_le _ h.toRowSize h.initial h.final
  simpa only [DirectEmptyTailRemoval.subtractFamily_states, totalBound] using hh

end NSSE.DirectEmptyTailSize
