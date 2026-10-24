import NSSE.StoredSubterms
import NSSE.StoredEdgeEmission

namespace NSSE.StoredTermQuery
open StoredSubtypeTerm
variable {n : Nat}

inductive Literal (n : Nat)
  | le (left right : Term n)
  | eq (left right : Term n)

structure Query (n : Nat) where
  premises : List (Literal n)
  left : Term n
  right : Term n

def inequalities : Literal n → List (Term n × Term n) × Nat
  | .le a b => ([(a,b)],3)
  | .eq a b => ([(a,b),(b,a)],5)

def expanded (Q : Query n) : List (Term n × Term n) × Nat :=
  CountedListConstruction.flatMap inequalities Q.premises

theorem bound (Q : Query n) : (expanded Q).2 ≤ 1+9*Q.premises.length := by
  have h := CountedListConstruction.flatMap_bound inequalities Q.premises 5 2
    (by intro t _; cases t <;> simp [inequalities])
    (by intro t _; cases t <;> simp [inequalities])
  simpa only [expanded,Nat.mul_comm] using h

theorem length_bound (Q : Query n) : (expanded Q).1.length ≤ 2*Q.premises.length := by
  simp only [expanded,CountedListConstruction.flatMap_value]
  have h (xs : List (Literal n)) : (xs.flatMap (fun t => (inequalities t).1)).length ≤ 2*xs.length := by
    induction xs with
    | nil => simp
    | cons t xs ih =>
      simp only [inequalities] at ih
      cases t <;> simp only [List.flatMap_cons,inequalities,List.length_append,
        List.length_cons,List.length_nil] <;> omega
  exact h Q.premises

def packLiteral {d : Nat} : SubtypeTerms.Literal n d → Literal n
  | .le a b => .le (pack a) (pack b)
  | .eq a b => .eq (pack a) (pack b)
def packQuery {d : Nat} (Q : SubtypeTerms.Query n d) : Query n :=
  ⟨Q.premises.map packLiteral,pack Q.left,pack Q.right⟩

theorem packed_literal {d : Nat} (t : SubtypeTerms.Literal n d) :
    (inequalities (packLiteral t)).1 = StoredEdgeEmission.packPairs (SubtypeTerms.inequalities t) := by
  cases t <;> rfl

theorem packed_value {d : Nat} (Q : SubtypeTerms.Query n d) :
    (expanded (packQuery Q)).1 = StoredEdgeEmission.packPairs (SubtypeTerms.expanded Q) := by
  simp only [expanded,packQuery,CountedListConstruction.flatMap_value,List.flatMap_map,
    Function.comp_def,packed_literal,StoredEdgeEmission.packPairs,SubtypeTerms.expanded,List.map_flatMap]
end NSSE.StoredTermQuery
