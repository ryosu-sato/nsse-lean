import NSSE.ProductivityCompilerSize

/-! Finite terminal tables replace arbitrary Horn terminal callbacks. -/

namespace NSSE.MaterializedHornProgram

open ExplicitUnaryTableLanguage

structure Program where
  count : Nat
  terminals : List Bool
  rules : List HornRule

def Program.compiler (P : Program) : FiniteHornCompiler where
  stateCount := P.count
  terminal i := (lookup P.terminals i).1
  rules := P.rules

def materialize (C : FiniteHornCompiler) : Program where
  count := C.stateCount
  terminals := tabulate (fun i : Fin C.stateCount => C.terminal i.val)
  rules := C.rules

theorem terminal_correct (C : FiniteHornCompiler) (i : Nat) (hi : i < C.stateCount) :
    (materialize C).compiler.terminal i = C.terminal i :=
  tabulate_correct _ ⟨i,hi⟩

theorem build_eq (C : FiniteHornCompiler) (original rest : List Bool) (i : Nat)
    (hi : i+rest.length ≤ C.stateCount) :
    hornBuild (materialize C).compiler original i rest = hornBuild C original i rest := by
  induction rest generalizing i with
  | nil => rfl
  | cons b rest ih =>
    have hi' : i < C.stateCount := by simp only [List.length_cons] at hi; omega
    have hr : i+1+rest.length ≤ C.stateCount := by simp only [List.length_cons] at hi; omega
    simp only [hornBuild, hornNewBit, terminal_correct C i hi', ih (i+1) hr]
    rfl

theorem update_eq (C : FiniteHornCompiler) (mask : List Bool) (h : mask.length = C.stateCount) :
    hornUpdate (materialize C).compiler mask = hornUpdate C mask :=
  build_eq C mask mask 0 (by omega)

theorem iterate_eq (C : FiniteHornCompiler) (k : Nat) :
    iterateMask (hornUpdate (materialize C).compiler) k (hornInitial C) =
      iterateMask (hornUpdate C) k (hornInitial C) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [iterateMask, ih]
    apply update_eq
    rw [iterateMask_length _ (hornUpdate_inflationary C), hornInitial_length]

theorem decide_eq (C : FiniteHornCompiler) (i : Nat) :
    decideHornState (materialize C).compiler i = decideHornState C i := by
  change maskBit (iterateMask (hornUpdate (materialize C).compiler) (hornInitial C).length (hornInitial C)) i = _
  rw [iterate_eq]
  rfl

end NSSE.MaterializedHornProgram
