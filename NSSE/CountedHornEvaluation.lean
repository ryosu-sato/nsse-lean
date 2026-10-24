import NSSE.MaterializedHornProgram

/-! Executable eager Horn evaluation with table, equality and list-cell
recursion counters. Integer/allocator/construction costs remain separate. -/

namespace NSSE.CountedHornEvaluation

open ExplicitUnaryTableLanguage FiniteValuationLookup MaterializedHornProgram

def children (mask : List Bool) : List Nat → Bool × Nat
  | [] => (true,1)
  | i::is => let a := lookup mask i; let b := children mask is
    (a.1 && b.1,1+a.2+b.2)

def fires (mask : List Bool) (parent : Nat) : List HornRule → Bool × Nat
  | [] => (false,1)
  | r::rs => let e := equalNat parent r.parent; let a := children mask r.children
    let b := fires mask parent rs
    ((e.1 && a.1) || b.1,1+e.2+a.2+b.2)

def newBit (P : Program) (mask : List Bool) (i : Nat) (old : Bool) : Bool × Nat :=
  let a := lookup P.terminals i
  let b := fires mask i P.rules
  (old || a.1 || b.1,1+a.2+b.2)

def build (P : Program) (mask : List Bool) : Nat → List Bool → List Bool × Nat
  | _, [] => ([],1)
  | i, b::bs => let a := newBit P mask i b; let r := build P mask (i+1) bs
    (a.1::r.1,1+a.2+r.2)

def iterate (P : Program) : Nat → List Bool → List Bool × Nat
  | 0, mask => (mask,1)
  | k+1, mask => let a := iterate P k mask; let b := build P a.1 0 a.1
    (b.1,1+a.2+b.2)

def decide (P : Program) (i : Nat) : Bool × Nat :=
  let a := iterate P P.count (List.replicate P.count false)
  let b := lookup a.1 i
  (b.1,1+a.2+b.2)

theorem children_value (mask : List Bool) (is : List Nat) :
    (children mask is).1 = allMaskBits mask is := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [children, allMaskBits, List.all_cons, lookup_value, maskBit, ih]

theorem equalNat_value (a b : Nat) : (equalNat a b).1 = Decidable.decide (b=a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [equalNat_correct, decide_eq_true_eq]
  exact eq_comm

theorem fires_value (mask : List Bool) (p : Nat) (rs : List HornRule) :
    (fires mask p rs).1 = hornFires rs p mask := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [fires, hornFires, List.any_cons, equalNat_value, children_value, ih]

theorem newBit_value (P : Program) (mask : List Bool) (i : Nat) (b : Bool) :
    (newBit P mask i b).1 = hornNewBit P.compiler mask i b := by
  simp only [newBit, hornNewBit, Program.compiler, fires_value]

theorem build_value (P : Program) (mask bs : List Bool) (i : Nat) :
    (build P mask i bs).1 = hornBuild P.compiler mask i bs := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih => simp only [build, hornBuild, newBit_value, ih]

theorem iterate_value (P : Program) (k : Nat) (mask : List Bool) :
    (iterate P k mask).1 = iterateMask (hornUpdate P.compiler) k mask := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate, build_value, ih, iterateMask, hornUpdate]

theorem decide_value (P : Program) (i : Nat) : (decide P i).1 = decideHornState P.compiler i := by
  simp only [decide, lookup_value, iterate_value, decideHornState, decideLeastFixedPoint,
    hornInitial, Program.compiler, List.length_replicate, maskBit]

theorem materialize_value (C : FiniteHornCompiler) (i : Nat) :
    (decide (materialize C) i).1 = decideHornState C i :=
  (decide_value _ _).trans (decide_eq C i)

end NSSE.CountedHornEvaluation
