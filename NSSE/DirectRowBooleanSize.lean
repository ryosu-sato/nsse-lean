import NSSE.DirectRowBooleanOperations
import NSSE.RankNextGuardSize

/-! # Polynomial primitive guard bounds without epsilon-closure expansion -/

namespace NSSE.DirectRowBooleanSize

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ExactReachabilitySize
open ExactGuardedRunSize UniformArrayAtomBound RowRegularOperations

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n r B C : Nat}

/-- Guard budget separate from the number of states. -/
structure Fields (R : Row L P n) (B : Nat) : Prop extends RowSize R B where
  initial : ∀ q, nodes (R.initial q) ≤ B
  final : ∀ q, nodes (R.final q) ≤ B

theorem of_budget (R : Row L P n) (h : RowBudget R B) : Fields R B where
  toRowSize := h.toRowSize
  initial := h.initial
  final := h.final

theorem mono (R : Row L P n) (h : Fields R B) {B' : Nat} (hb : B ≤ B') : Fields R B' where
  data q r := (h.data q r).trans hb
  left q r := (h.left q r).trans hb
  right q r := (h.right q r).trans hb
  guard := h.guard.trans hb
  initial q := (h.initial q).trans hb
  final q := (h.final q).trans hb

def predecessorBound (n B : Nat) := 1+n*(9+2*B)
def complementBound (n B : Nat) := predecessorBound n B+5+n*(7+predecessorBound n B)

theorem first_le (R : Row L P n) (h : Fields R B) (q : Fin n) :
    nodes (SymbolicComplement.first (toAutomaton R) 0 q) ≤ predecessorBound n B := by
  apply (nodes_any_le n (5+2*B) _ (fun t => ?_)).trans
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left n (by omega)) 1
  · simp only [nodes_inf, nodes_relabel]
    change 5+nodes (R.initial t)+nodes (R.data t q) ≤ _
    have := h.initial t; have := h.data t q; omega

theorem next_le (R : Row L P n) (h : Fields R B) (S : SymbolicComplement.Mask n) (q : Fin n) :
    nodes (SymbolicComplement.next (toAutomaton R) S 0 q) ≤ predecessorBound n B := by
  apply (nodes_any_le n (B+1) _ (fun t => ?_)).trans
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left n (by omega)) 1
  · dsimp only
    split
    · exact (h.data t q).trans (by omega)
    · change 1 ≤ B+1; omega

theorem cell_le {X : Type*} (S : SymbolicComplement.Mask n) (f : Fin n → L.Formula X)
    (h : ∀ q, nodes (f q) ≤ B) : nodes (SymbolicComplement.cell S f) ≤ 3+n*(7+B) := by
  change nodes (ExactReachabilityTable.every n _) ≤ _
  rw [nodes_every]
  have hh (q : Fin n) : 5+nodes (if S q then f q else (f q).not) ≤ 7+B := by
    split
    · have := h q; omega
    · rw [nodes_not]; have := h q; omega
  have hs := Finset.sum_le_sum (fun q (_ : q ∈ Finset.univ) => hh q)
  simpa using Nat.add_le_add_left hs 3

theorem final_le (R : Row L P n) (h : Fields R B) (S : SymbolicComplement.State n) :
    nodes (SymbolicComplement.finalGuard (toAutomaton R) S) ≤ predecessorBound n B := by
  cases S with
  | none =>
    apply (nodes_any_le n (5+2*B) _ (fun q => ?_)).trans
    · exact Nat.add_le_add_left (Nat.mul_le_mul_left n (by omega)) 1
    · rw [nodes_inf]
      have := h.initial q; have := h.final q
      change 5+nodes (R.initial q)+nodes (R.final q) ≤ _
      omega
  | some S =>
    apply (nodes_any_le n (B+1) _ (fun q => ?_)).trans
    · exact Nat.add_le_add_left (Nat.mul_le_mul_left n (by omega)) 1
    · dsimp only
      split
      · exact (h.final q).trans (by omega)
      · change 1 ≤ B+1; omega

theorem complement_fields (R : Row L P n) (h : Fields R B) :
    Fields (DirectRowBooleanOperations.complement R) (complementBound n B) := by
  have hg : 3 ≤ complementBound n B := by unfold complementBound; omega
  have hd (s t : SymbolicComplement.State n) :
      nodes (SymbolicComplement.stepGuard (toAutomaton R) 0 s t) ≤ complementBound n B := by
    cases s <;> cases t
    · change 1 ≤ _; omega
    · exact (cell_le _ _ (first_le R h)).trans (by unfold complementBound; omega)
    · change 1 ≤ _; omega
    · exact (cell_le _ _ (next_le R h _)).trans (by unfold complementBound; omega)
  have hi (s : SymbolicComplement.State n) :
      nodes (SymbolicComplement.startGuard (toAutomaton R) s) ≤ complementBound n B := by
    cases s
    · change 3 ≤ _; exact hg
    · change 1 ≤ _; omega
  exact { data := fun q r => hd _ _
          left := fun _ _ => by change 1 ≤ _; omega
          right := fun _ _ => by change 1 ≤ _; omega
          guard := by change 1 ≤ _; omega
          initial := fun q => hi _
          final := fun q => by
            rw [show (DirectRowBooleanOperations.complement R).final q =
              (SymbolicComplement.finalGuard (toAutomaton R) (SymbolicComplement.decodeState n q)).not from rfl,
              nodes_not]
            have := final_le R h (SymbolicComplement.decodeState n q)
            unfold complementBound; omega }

theorem intersect_fields (R : Row L P n) (S : Row L P r) (hr : Fields R B) (hs : Fields S C) :
    Fields (DirectRowBooleanOperations.intersect R S) (5+B+C) where
  data q r := by
    rw [show (DirectRowBooleanOperations.intersect R S).data q r = _ ⊓ _ from rfl, nodes_inf]
    exact Nat.add_le_add (Nat.add_le_add_left (hr.data _ _) 5) (hs.data _ _)
  initial q := by
    rw [show (DirectRowBooleanOperations.intersect R S).initial q = _ ⊓ _ from rfl, nodes_inf]
    exact Nat.add_le_add (Nat.add_le_add_left (hr.initial _) 5) (hs.initial _)
  final q := by
    rw [show (DirectRowBooleanOperations.intersect R S).final q = _ ⊓ _ from rfl, nodes_inf]
    exact Nat.add_le_add (Nat.add_le_add_left (hr.final _) 5) (hs.final _)
  left _ _ := by change 1 ≤ 5+B+C; omega
  right _ _ := by change 1 ≤ 5+B+C; omega
  guard := by change 1 ≤ 5+B+C; omega

theorem difference_fields (R : Row L P n) (S : Row L P r) (hr : Fields R B) (hs : Fields S C) :
    Fields (DirectRowBooleanOperations.difference R S) (5+B+complementBound r C) :=
  intersect_fields R _ hr (complement_fields S hs)

end NSSE.DirectRowBooleanSize
