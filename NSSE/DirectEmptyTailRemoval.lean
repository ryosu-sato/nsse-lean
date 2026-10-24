import NSSE.DirectRowBooleanOperations

/-! # Empty-tail subtraction using direct epsilon-free Boolean operations -/

namespace NSSE.DirectEmptyTailRemoval

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks
open ArrayAtomExistentialPackages EmptyTailRemoval

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {k c : Nat} {ns : Fin k → Nat}

def subtractList (C : Candidate L P) (rows : List (Candidate L P)) (last : P) : Candidate L P :=
  match rows with
  | [] => C
  | R :: rows => subtractList
      ⟨_, DirectRowBooleanOperations.difference C.2 (EmptyTailFiring.compile R.2 last)⟩ rows last

def subtractFamily (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P) : Candidate L P :=
  subtractList ⟨c, C⟩ (rowList rows) last

theorem subtractList_correct (C : Candidate L P) (rows : List (Candidate L P)) (last : P)
    {D : Type*} [L.Structure D] (p : P → D) (xs : List D) :
    ((subtractList C rows last).2.dataNFA p).Accepts xs ↔
      (C.2.dataNFA p).Accepts xs ∧ ∀ R ∈ rows, ¬ EmptyTailFiring.Witness R.2 last p xs := by
  induction rows generalizing C with
  | nil => simp [subtractList]
  | cons R rows ih =>
    rw [subtractList, ih, DirectRowBooleanOperations.difference_correct, EmptyTailFiring.compile_witness]
    simp only [List.forall_mem_cons]
    tauto

theorem subtractFamily_correct (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P)
    {D : Type*} [L.Structure D] (p : P → D) (xs : List D) :
    ((subtractFamily rows C last).2.dataNFA p).Accepts xs ↔
      (C.dataNFA p).Accepts xs ∧ ∀ i, ¬ EmptyTailFiring.Witness (rows i) last p xs := by
  rw [subtractFamily, subtractList_correct]
  simp [rowList]

theorem equivalent (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P)
    {D : Type*} [L.Structure D] (p : P → D) (xs : List D) :
    ((subtractFamily rows C last).2.dataNFA p).Accepts xs ↔
      ((EmptyTailRemoval.subtractFamily rows C last).2.dataNFA p).Accepts xs :=
  (subtractFamily_correct rows C last p xs).trans
    (EmptyTailRemoval.subtractFamily_all_inputs rows C last p xs).symm

theorem subtractList_qf (C : Candidate L P) (rows : List (Candidate L P)) (last : P)
    (hc : RowQF C.2) (hr : ∀ R ∈ rows, RowQF R.2) : RowQF (subtractList C rows last).2 := by
  induction rows generalizing C with
  | nil => exact hc
  | cons R rows ih =>
    apply ih
    · exact DirectRowBooleanOperations.difference_qf C.2 _ hc
        (RankCleanedQuantifierFree.empty_tail_qf R.2 (hr R (by simp)) last)
    · intro S hs
      exact hr S (by simp [hs])

theorem subtractFamily_qf (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (last : P) (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) : RowQF (subtractFamily rows C last).2 := by
  apply subtractList_qf _ _ _ hc
  intro R hR
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hR
  exact hr i

/-- Exact multiplier, using only the original list's row sizes. -/
def stateFactor (rows : List (Candidate L P)) : Nat :=
  (rows.map (fun R => 2^(3*R.1)+1)).prod

theorem subtractList_states (C : Candidate L P) (rows : List (Candidate L P)) (last : P) :
    (subtractList C rows last).1 = C.1 * stateFactor rows := by
  induction rows generalizing C with
  | nil => simp [subtractList, stateFactor]
  | cons R rows ih =>
    rw [subtractList, ih]
    change (SymbolicConjunction.pairs C.1 (SymbolicComplement.states (EmptyTailFiring.states R.1).length).length).length *
      stateFactor rows = _
    simp only [SymbolicConjunction.length_pairs, SymbolicComplement.length_states, EmptyTailFiring.length_states]
    simp [stateFactor, Nat.mul_assoc]

theorem subtractFamily_states (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (last : P) :
    (subtractFamily rows C last).1 = c * ((List.finRange k).map (fun i => 2^(3*ns i)+1)).prod := by
  rw [subtractFamily, subtractList_states]
  simp [stateFactor, rowList, List.map_map, Function.comp_def]

end NSSE.DirectEmptyTailRemoval
