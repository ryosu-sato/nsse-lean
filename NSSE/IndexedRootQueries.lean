import NSSE.ConcreteSOA
import NSSE.FiniteRegisteredStructuralTrace
import NSSE.CanonicalForbiddenTransitionLabels

/-!
# Finite canonical root-query indices

An SOA instance stores its root rows in a finite list.  Since rows contain
language predicates and need not have decidable equality, canonical queries
are positions in that list rather than row values.
-/

namespace NSSE

universe u

theorem exists_fin_getElem_eq_of_mem
    {value : α} {values : List α}
    (hvalue : value ∈ values) :
    ∃ index : Fin values.length, values[index] = value := by
  induction values with
  | nil =>
      simp at hvalue
  | cons head tail ih =>
      simp only [List.mem_cons] at hvalue
      rcases hvalue with rfl | htail
      · exact ⟨⟨0, by simp⟩, rfl⟩
      · obtain ⟨index, hindex⟩ := ih htail
        exact ⟨index.succ, by simpa using hindex⟩

def SOAInstance.IndexedRootQuery
    (I : SOAInstance α) (index : Fin I.rows.length)
    (word : Word α) : Prop :=
  SOAInstance.RowCovers I.rows[index] word

theorem SOAInstance.rootCov_iff_exists_indexedRootQuery
    (I : SOAInstance α) (word : Word α) :
    I.RootCov word ↔
      ∃ index : Fin I.rows.length,
        I.IndexedRootQuery index word := by
  constructor
  · rintro ⟨row, hrow, hcovers⟩
    obtain ⟨index, hindex⟩ :=
      exists_fin_getElem_eq_of_mem hrow
    exact ⟨index, by simpa [IndexedRootQuery, hindex] using hcovers⟩
  · rintro ⟨index, hcovers⟩
    exact ⟨I.rows[index], List.getElem_mem _,
      by simpa [IndexedRootQuery] using hcovers⟩

def SOAInstance.indexedRootQueryEnumeration
    (I : SOAInstance α) :
    Enumeration (Fin I.rows.length) :=
  finEnumeration I.rows.length

theorem length_finValues (count : Nat) :
    (finValues count).length = count := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      simp [finValues, ih]

@[simp] theorem SOAInstance.indexedRootQueryEnumeration_length
    (I : SOAInstance α) :
    I.indexedRootQueryEnumeration.values.length = I.rows.length := by
  exact length_finValues I.rows.length

theorem SOAInstance.forbids_all_indexedRows_iff_not_rootCov
    (I : SOAInstance α) (word : Word α) :
    SOAProblem.Forbids I.IndexedRootQuery (fun _ => True) word ↔
      ¬ I.RootCov word :=
  SOAProblem.forbids_all_iff_not_rootCov I.asProblem
    I.IndexedRootQuery I.rootCov_iff_exists_indexedRootQuery word

theorem SOAInstance.generalized_all_indexedRows_iff_critical
    (I : SOAInstance α) (word : Word α) :
    I.asProblem.Generalized I.IndexedRootQuery (fun _ => True) word ↔
      I.Critical word := by
  rw [SOAProblem.generalized_all_iff_critical
    I.asProblem I.IndexedRootQuery
      I.rootCov_iff_exists_indexedRootQuery]
  rfl

end NSSE
