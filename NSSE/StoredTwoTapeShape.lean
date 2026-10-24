import NSSE.StoredRunTableBound

/-! Constant-size stored shape operations for the actual two-tape enumeration. -/
namespace NSSE.StoredTwoTapeShape
open ConvolutionShapes

def bits (s : Shape 2) : StoredRelationTuple.Data Bool 2 :=
  ⟨match s.val with
    | 0 => [false,false]
    | 1 => [true,false]
    | 2 => [false,true]
    | _ => [true,true],by split <;> rfl⟩
theorem bits_value (s : Shape 2) (i : Fin 2) :
    (StoredRelationTuple.read (bits s) i).1 = mask s i := by
  fin_cases s <;> fin_cases i <;> rfl

def read (s : Shape 2) (i : Fin 2) : Bool × Nat :=
  let a := StoredRelationTuple.read (bits s) i
  (a.1,8+a.2)
theorem read_value (s : Shape 2) (i : Fin 2) : (read s i).1 = mask s i := bits_value s i
theorem read_bound (s : Shape 2) (i : Fin 2) : (read s i).2 ≤ 10 := by
  have h := StoredRelationTuple.read_bound (bits s) i
  simp only [read]; omega

def positions (s : Shape 2) : List (Fin 2) := match s.val with
  | 0 => []
  | 1 => [0]
  | 2 => [1]
  | _ => [0,1]
theorem positions_value (s : Shape 2) : positions s = tapes (mask s) := by fin_cases s <;> rfl
def slots (s : Shape 2) : StoredRelationTuple.Data (Fin 2) (tapes (mask s)).length :=
  ⟨positions s,congrArg List.length (positions_value s)⟩
theorem slots_bound (s : Shape 2) : (tapes (mask s)).length ≤ 2 := by fin_cases s <;> decide

def tape (s : Shape 2) (i : Fin (tapes (mask s)).length) : Fin 2 × Nat :=
  let a := StoredRelationTuple.read (slots s) i
  (a.1,8+a.2)
theorem tape_value (s : Shape 2) (i : Fin (tapes (mask s)).length) :
    (tape s i).1 = ConvolutionShapes.tape (mask s) i := by
  fin_cases s <;> fin_cases i <;> rfl
theorem tape_bound (s : Shape 2) (i : Fin (tapes (mask s)).length) : (tape s i).2 ≤ 10 := by
  have h := StoredRelationTuple.read_bound (slots s) i
  have hl := slots_bound s
  simp only [tape]; omega
end NSSE.StoredTwoTapeShape
