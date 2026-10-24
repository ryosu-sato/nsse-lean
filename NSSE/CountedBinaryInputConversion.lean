import NSSE.CountedBitListValue

namespace NSSE.CountedBinaryInputConversion
open BitListTokenReader (eval)
open CheckedBitListIndex (Index)
open CheckedBitListBound (Bound)
open CheckedBitListInput (Input)
open CountedListConstruction (map)

variable {limit arity : List Bool}

def indices (xs : List (Index limit)) : List (Fin (eval limit)) × Nat :=
  map CountedBitListValue.index xs

theorem indices_value (xs : List (Index limit)) : (indices xs).1 = xs.map Index.denote := by
  simp [indices,CountedListConstruction.map_value,CountedBitListValue.index_value]

def indicesBudget (xs : List (Index limit)) :=
  1+xs.length*(eval limit+2)+4*(xs.map (fun x => x.digits.length)).sum

theorem indices_bound (xs : List (Index limit)) : (indices xs).2 ≤ indicesBudget xs := by
  induction xs with
  | nil => simp [indices,map,indicesBudget]
  | cons x xs ih =>
    have h := CountedBitListValue.index_bound x
    simp only [indices,map] at *
    simp only [indicesBudget,List.length_cons,List.map_cons,List.sum_cons] at *
    nlinarith

def bound (a : Bound limit arity) : StoredSubtypeInput.Bound (eval limit) (eval arity) × Nat :=
  let h := CountedBitListValue.index a.head
  let c := indices a.children
  (⟨h.1,c.1,by rw [indices_value,List.length_map]; exact a.length_eq⟩,1+h.2+c.2)

theorem bound_value (a : Bound limit arity) : (bound a).1 = a.denote := by
  simp [bound,CountedBitListValue.index_value,indices_value,Bound.denote]

def boundBudget (a : Bound limit arity) :=
  2+eval limit+4*a.head.digits.length+indicesBudget a.children

theorem bound_bound (a : Bound limit arity) : (bound a).2 ≤ boundBudget a := by
  have hh := CountedBitListValue.index_bound a.head
  have hc := indices_bound a.children
  simp only [bound,boundBudget]
  omega

def bounds (xs : List (Bound limit arity)) := map bound xs

theorem bounds_value (xs : List (Bound limit arity)) : (bounds xs).1 = xs.map Bound.denote := by
  simp [bounds,CountedListConstruction.map_value,bound_value]

def boundsBudget (xs : List (Bound limit arity)) := 1+xs.length+(xs.map boundBudget).sum

theorem bounds_bound (xs : List (Bound limit arity)) : (bounds xs).2 ≤ boundsBudget xs := by
  induction xs with
  | nil => simp [bounds,map,boundsBudget]
  | cons x xs ih =>
    have h := bound_bound x
    simp only [bounds,map] at *
    simp only [boundsBudget,List.length_cons,List.map_cons,List.sum_cons] at *
    omega

def convert (I : Input limit arity) : StoredSubtypeInput.Input (eval limit) (eval arity) × Nat :=
  let u := bounds I.upper
  let l := bounds I.lower
  let b := indices I.bot
  let t := indices I.top
  (⟨u.1,l.1,b.1,t.1⟩,1+u.2+l.2+b.2+t.2)

theorem value (I : Input limit arity) : (convert I).1 = I.denote := by
  simp [convert,bounds_value,indices_value,Input.denote]

def budget (I : Input limit arity) :=
  1+boundsBudget I.upper+boundsBudget I.lower+indicesBudget I.bot+indicesBudget I.top

theorem conversion_bound (I : Input limit arity) : (convert I).2 ≤ budget I := by
  have hu := bounds_bound I.upper
  have hl := bounds_bound I.lower
  have hb := indices_bound I.bot
  have ht := indices_bound I.top
  simp only [convert,budget]
  omega
end NSSE.CountedBinaryInputConversion
