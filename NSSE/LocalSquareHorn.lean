import NSSE.GuardedCompiler
import NSSE.SolverHornFamily

/-!
# Horn terminal for a local insertion-square mismatch

The local same-payload square is either a common primitive-power
periodic certificate or a literal fixed word-equation mismatch.  The
latter is an exact solver and hence a concrete Horn family.
-/

namespace NSSE

universe u

structure InsertionSquareMismatchQuery (α : Type u) where
  left : Word α
  middle : Word α
  right : Word α
  payload : Word α

def InsertionSquareMismatchQuery.formula
    (query : InsertionSquareMismatchQuery α) : Prop :=
  Word.insertAt
      (query.left ++ query.middle ++ query.right)
      query.payload query.left.length ≠
    Word.insertAt
      (query.left ++ query.middle ++ query.right)
      query.payload (query.left.length + query.middle.length)

def insertionSquareMismatchSolver [DecidableEq α] :
    ExactSolver (InsertionSquareMismatchQuery α) where
  formula := InsertionSquareMismatchQuery.formula
  decide := fun query =>
    !(decide
      (Word.insertAt
          (query.left ++ query.middle ++ query.right)
          query.payload query.left.length =
        Word.insertAt
          (query.left ++ query.middle ++ query.right)
          query.payload
            (query.left.length + query.middle.length)))
  correct := by
    intro query
    simp [InsertionSquareMismatchQuery.formula]

def insertionSquareMismatchQuery
    (A T B X : Word α) : InsertionSquareMismatchQuery α where
  left := A
  middle := T
  right := B
  payload := X

def insertionSquareMismatchHornFamily [DecidableEq α]
    (A T B X : Word α) : HornFamily :=
  exactSolverHornFamily insertionSquareMismatchSolver
    (insertionSquareMismatchQuery A T B X)

theorem insertionSquareMismatchHornFamily_derives_iff
    [DecidableEq α] (A T B X : Word α) :
    HornDerives
        (insertionSquareMismatchHornFamily A T B X).compiler
        (insertionSquareMismatchHornFamily A T B X).root ↔
      Word.insertAt (A ++ T ++ B) X A.length ≠
        Word.insertAt (A ++ T ++ B) X
          (A.length + T.length) := by
  simpa [insertionSquareMismatchHornFamily,
    insertionSquareMismatchSolver,
    insertionSquareMismatchQuery,
    InsertionSquareMismatchQuery.formula] using
    (exactSolverHornFamily_derives_iff
      insertionSquareMismatchSolver
      (insertionSquareMismatchQuery A T B X))

theorem localInsertionSquare_periodic_or_Horn
    [DecidableEq α]
    (A T B X : Word α) (hX : X ≠ []) :
    (∃ root : Word α, ∃ m n : Nat,
      root.IsPrimitive ∧
      0 < m ∧
      X = Word.power root m ∧
      T = Word.power root n) ∨
      HornDerives
        (insertionSquareMismatchHornFamily A T B X).compiler
        (insertionSquareMismatchHornFamily A T B X).root := by
  cases Word.classify_insertion_square A T B X hX with
  | periodic root m n primitive payloadPositive payloadPower middlePower =>
      exact Or.inl
        ⟨root, m, n, primitive, payloadPositive,
          payloadPower, middlePower⟩
  | mismatch different =>
      exact Or.inr
        ((insertionSquareMismatchHornFamily_derives_iff
          A T B X).2 different)

theorem decideInsertionSquareMismatchRoot_correct
    [DecidableEq α] (A T B X : Word α) :
    decideHornState
        (insertionSquareMismatchHornFamily A T B X).compiler
        (insertionSquareMismatchHornFamily A T B X).root = true ↔
      Word.insertAt (A ++ T ++ B) X A.length ≠
        Word.insertAt (A ++ T ++ B) X
          (A.length + T.length) := by
  rw [decideHornState_correct
    (insertionSquareMismatchHornFamily A T B X).compiler
    (insertionSquareMismatchHornFamily A T B X).root
    (insertionSquareMismatchHornFamily A T B X).root_lt]
  exact insertionSquareMismatchHornFamily_derives_iff A T B X

end NSSE
