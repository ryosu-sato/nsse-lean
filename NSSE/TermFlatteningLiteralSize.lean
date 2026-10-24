import NSSE.TermFlatteningSize
import NSSE.CountedFiniteSatisfiability

/-! Literal count of the actual flattening, including equality expansion. -/
namespace NSSE.TermFlatteningLiteralSize
open SubtypeTerms SubtypeTermLayout SubtypeTermDefinitions SubtypeTermFlattening
open SubtypeConstraintOperations CountedFiniteSatisfiability
variable {n d : Nat}

theorem combine_size (a b : SubtypeConstraints.Constraints n d) :
    literals (combine a b) = literals a + literals b := by
  simp [literals, combine, List.length_append]; omega

theorem join_size (xs : List (SubtypeConstraints.Constraints n d)) :
    literals (join xs) = (xs.map literals).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change literals (combine x (join xs)) = _
    simp [combine_size, ih]

theorem term_size (L : Layout n d) (t : Term n d) :
    literals (termClause L t) ≤ 2 := by
  cases t <;> simp [termClause, empty, literals]

theorem definitions_size (L : Layout n d) :
    literals (definitions L) ≤ 2*L.terms.length := by
  rw [definitions, join_size, List.map_map]
  have h := CountedFiniteTreeComparison.sum_bound L.terms
    (fun t => literals (termClause L t)) 2 (fun t _ => term_size L t)
  simpa only [Function.comp_def, Nat.mul_comm] using h

theorem edges_size (L : Layout n d) (i : Fin d) :
    literals (edges L i) = 2*L.pairs.length := by
  rw [edges, join_size, List.map_map]
  simp [Function.comp_def, edgeClause, literals,
    List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm]

theorem flatten_size (Q : Query n d) (i : Fin d) :
    literals (flatten Q i).constraints ≤ 8*TermFlatteningSize.size Q := by
  have ht := definitions_size (layout Q)
  have he := edges_size (layout Q) i
  have hn := TermFlatteningSize.layout_count Q
  change literals (combine _ _) ≤ _
  rw [combine_size]
  dsimp only [Layout.count] at hn
  omega
end NSSE.TermFlatteningLiteralSize
