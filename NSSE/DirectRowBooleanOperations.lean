import NSSE.RankCleanedQuantifierFree

/-! # Row Boolean operations without redundant epsilon-closure expansion -/

namespace NSSE.DirectRowBooleanOperations

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks SymbolicAutomata
open RowRegularOperations GuardedBlockRelation

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n r : Nat}

/-- Rows already have no silent transitions. Copy the truth-cell construction
straight into Row fields, retaining the original data guards. -/
def complement (R : Row L P n) : Row L P (SymbolicComplement.states n).length where
  initial i := SymbolicComplement.startGuard (toAutomaton R) (SymbolicComplement.decodeState n i)
  final i := (SymbolicComplement.finalGuard (toAutomaton R) (SymbolicComplement.decodeState n i)).not
  data i j := SymbolicComplement.stepGuard (toAutomaton R) 0
    (SymbolicComplement.decodeState n i) (SymbolicComplement.decodeState n j)
  left _ _ := ⊥
  right _ _ := ⊥
  guard := ⊥

def intersect (R : Row L P n) (S : Row L P r) : Row L P (SymbolicConjunction.pairs n r).length where
  initial i := R.initial (SymbolicConjunction.decode n r i).1 ⊓ S.initial (SymbolicConjunction.decode n r i).2
  final i := R.final (SymbolicConjunction.decode n r i).1 ⊓ S.final (SymbolicConjunction.decode n r i).2
  data i j := R.data (SymbolicConjunction.decode n r i).1 (SymbolicConjunction.decode n r j).1 ⊓
    S.data (SymbolicConjunction.decode n r i).2 (SymbolicConjunction.decode n r j).2
  left _ _ := ⊥
  right _ _ := ⊥
  guard := ⊥

def difference (R : Row L P n) (S : Row L P r) := intersect R (complement S)

theorem complement_correct (R : Row L P n) {D : Type*} [L.Structure D] (p : P → D) (xs : List D) :
    ((complement R).dataNFA p).Accepts xs ↔ ¬ (R.dataNFA p).Accepts xs := by
  change (mapInput (SymbolicComplement.pullback
    (SymbolicComplement.interpret (toAutomaton R) true p) (SymbolicComplement.decodeState n)) letter).Accepts xs ↔ _
  rw [mapInput_accepts, SymbolicComplement.pullback_accepts _ _ (SymbolicComplement.decodeState_surjective n),
    SymbolicComplement.interpret_correct]
  simp only [Bool.true_eq, ↓reduceIte]
  rw [← mapInput_accepts]
  rfl

theorem intersect_correct (R : Row L P n) (S : Row L P r)
    {D : Type*} [L.Structure D] (p : P → D) (xs : List D) :
    ((intersect R S).dataNFA p).Accepts xs ↔ (R.dataNFA p).Accepts xs ∧ (S.dataNFA p).Accepts xs := by
  have he : (intersect R S).dataNFA p =
      SymbolicComplement.pullback (SymbolicConjunction.product (R.dataNFA p) (S.dataNFA p))
        (SymbolicConjunction.decode n r) := by
    unfold Row.dataNFA intersect SymbolicComplement.pullback SymbolicConjunction.product
    congr 1
    · funext q; exact propext Formula.realize_inf
    · funext q x r; exact propext Formula.realize_inf
    · funext q; exact propext Formula.realize_inf
  rw [he]
  rw [SymbolicComplement.pullback_accepts _ _ (SymbolicConjunction.decode_surjective n r),
    SymbolicConjunction.product_accepts]

theorem difference_correct (R : Row L P n) (S : Row L P r)
    {D : Type*} [L.Structure D] (p : P → D) (xs : List D) :
    ((difference R S).dataNFA p).Accepts xs ↔ (R.dataNFA p).Accepts xs ∧ ¬ (S.dataNFA p).Accepts xs := by
  rw [difference, intersect_correct, complement_correct]

open ArrayAtomExistentialPackages ExactReachabilityTable RowBooleanClosureQuantifierFree

theorem intersect_qf (R : Row L P n) (S : Row L P r) (hr : RowQF R) (hs : RowQF S) :
    RowQF (intersect R S) where
  initial _ := (hr.initial _).inf (hs.initial _)
  final _ := (hr.final _).inf (hs.final _)
  data _ _ := (hr.data _ _).inf (hs.data _ _)
  left _ _ := BoundedFormula.isQF_bot
  right _ _ := BoundedFormula.isQF_bot
  guard := BoundedFormula.isQF_bot

theorem complement_qf (R : Row L P n) (h : RowQF R) : RowQF (complement R) := by
  let A := toAutomaton R
  have he := toAutomaton_qf R h
  have hi (s : SymbolicComplement.State n) : (SymbolicComplement.startGuard A s).IsQF := by
    cases s
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot
  have hf (s : SymbolicComplement.State n) : (SymbolicComplement.finalGuard A s).IsQF := by
    cases s with
    | none => exact any_qf n _ (fun q => (he.initial q).inf (he.final q))
    | some S =>
      apply any_qf
      intro q
      dsimp only
      split
      · exact he.final q
      · exact BoundedFormula.isQF_bot
  have hd (s t : SymbolicComplement.State n) : (SymbolicComplement.stepGuard A 0 s t).IsQF := by
    cases s <;> cases t
    · exact BoundedFormula.isQF_bot
    · apply cell_qf
      intro r
      exact any_qf n _ (fun q => (relabel_qf _ (he.initial q) _).inf (he.step 0 q r))
    · exact BoundedFormula.isQF_bot
    · apply cell_qf
      intro r
      apply any_qf
      intro q
      dsimp only
      split
      · exact he.step 0 q r
      · exact BoundedFormula.isQF_bot
  exact { initial := fun _ => hi _
          final := fun _ => (hf _).not
          data := fun _ _ => hd _ _
          left := fun _ _ => BoundedFormula.isQF_bot
          right := fun _ _ => BoundedFormula.isQF_bot
          guard := BoundedFormula.isQF_bot }

theorem difference_qf (R : Row L P n) (S : Row L P r) (hr : RowQF R) (hs : RowQF S) :
    RowQF (difference R S) := intersect_qf _ _ hr (complement_qf S hs)

end NSSE.DirectRowBooleanOperations
