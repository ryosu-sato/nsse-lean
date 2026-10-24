import NSSE.BoundedWordEnumeration

/-!
# Executable enumeration of functions on finite enumerated types

A function is represented by its value vector over the chosen complete
domain list.  `idxOf` gives executable lookup; completeness proves that
the vector obtained by mapping any function reconstructs that function.
-/

namespace NSSE

universe u v

theorem getElem?_idxOf_of_mem
    [DecidableEq α]
    (values : List α) (x : α)
    (hmem : x ∈ values) :
    values[values.idxOf x]? = some x := by
  induction values with
  | nil => simp at hmem
  | cons head tail ih =>
      by_cases heq : x = head
      · subst head
        rw [List.idxOf, List.findIdx_cons]
        simp
      · have htail : x ∈ tail := by
          simpa [heq] using hmem
        rw [List.idxOf, List.findIdx_cons]
        have hhead : (head == x) = false := by
          have hne : head ≠ x := fun h => heq h.symm
          simp [hne]
        simpa [hhead] using ih htail

theorem getElem?_map_idxOf_of_mem
    [DecidableEq α]
    (values : List α) (f : α → β) (x : α)
    (hmem : x ∈ values) :
    (values.map f)[values.idxOf x]? = some (f x) := by
  rw [List.getElem?_map, getElem?_idxOf_of_mem values x hmem]
  rfl

def functionOfVector
    [DecidableEq α]
    (domain : Enumeration α) (fallback : β)
    (vector : List β) : α → β :=
  fun x => (vector[domain.values.idxOf x]?).getD fallback

theorem functionOfVector_map
    [DecidableEq α]
    (domain : Enumeration α) (fallback : β)
    (f : α → β) :
    functionOfVector domain fallback (domain.values.map f) = f := by
  funext x
  unfold functionOfVector
  rw [getElem?_map_idxOf_of_mem
    domain.values f x (domain.complete x)]
  rfl

def functionEnumeration
    [DecidableEq α]
    (domain : Enumeration α) (codomain : Enumeration β)
    (fallback : β) :
    Enumeration (α → β) where
  values :=
    (wordsOfLength codomain domain.values.length).map
      (functionOfVector domain fallback)
  complete := by
    intro f
    simp only [List.mem_map]
    let vector := domain.values.map f
    refine ⟨vector, ?_, ?_⟩
    · apply
        (mem_wordsOfLength_iff codomain domain.values.length vector).2
      simp [vector]
    · exact functionOfVector_map domain fallback f

def decidableEqFunctionOfEnumeration
    [DecidableEq β]
    (domain : Enumeration α) :
    DecidableEq (α → β) :=
  fun f g =>
    decidable_of_iff
      ((domain.values.all fun x => decide (f x = g x)) = true)
      (by
        constructor
        · intro hall
          funext x
          have hx :=
            (List.all_eq_true.mp hall) x (domain.complete x)
          simpa using hx
        · intro heq
          subst g
          simp)

end NSSE
