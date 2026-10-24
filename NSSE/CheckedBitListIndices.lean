import NSSE.CheckedBitListConsumption

namespace NSSE.CheckedBitListIndices
open BitListTokenReader (eval)
open CheckedBitListIndex (Index)

def read (limit : List Bool) : List (List Bool) →
    Option (List (Index limit) × List (List Bool)) × Nat
  | [] => (none,1)
  | count::rest => let r := CheckedBitListChildren.read limit count rest; (r.1,1+r.2)

theorem value (limit : List Bool) (bs : List (List Bool)) :
    (read limit bs).1.map (fun p => (p.1.map Index.denote,p.2.map eval)) =
      StoredInputCodec.readList (StoredInputCodec.index (eval limit)) (bs.map eval) := by
  cases bs with
  | nil => rfl
  | cons count rest => exact CheckedBitListChildren.value limit count rest

def budget (limit : List Bool) (bs : List (List Bool)) :=
  1+(bs.length+1)*(2*(bs.map List.length).sum+3*limit.length+6)+3*(bs.map List.length).sum

theorem bound (limit : List Bool) (bs : List (List Bool)) :
    (read limit bs).2 ≤ budget limit bs := by
  cases bs with
  | nil => simp only [read,budget]; omega
  | cons count rest =>
    have h := CheckedBitListChildren.bound limit count rest
    have hm : CheckedBitListChildren.budget limit count rest ≤
        ((count::rest).length+1)*(2*((count::rest).map List.length).sum+3*limit.length+6)
          +3*((count::rest).map List.length).sum := by
      dsimp only [CheckedBitListChildren.budget, List.length_cons, List.map_cons, List.sum_cons]
      gcongr <;> omega
    simp only [read,budget]
    omega

theorem consumption (limit : List Bool) (bs : List (List Bool))
    (xs : List (Index limit)) (rest : List (List Bool))
    (h : (read limit bs).1 = some (xs,rest)) :
    rest.length + xs.length + 1 = bs.length ∧
      (rest.map List.length).sum ≤ (bs.map List.length).sum := by
  cases bs with
  | nil => simp [read] at h
  | cons count tail =>
    have hh := CheckedBitListConsumption.children limit count tail xs rest h
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega
end NSSE.CheckedBitListIndices
