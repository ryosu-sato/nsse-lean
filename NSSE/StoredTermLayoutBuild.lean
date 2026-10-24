import NSSE.StoredLayoutTerms

namespace NSSE.StoredTermLayoutBuild
open StoredSubtypeTerm
variable {n : Nat}

structure Layout (n : Nat) where
  terms : List (Term n)
  pairs : List (Term n × Term n)
  termCount : Nat
  pairCount : Nat
  terms_length : terms.length = termCount
  pairs_length : pairs.length = pairCount

def build (Q : StoredTermQuery.Query n) : Layout n × Nat :=
  let e := StoredTermQuery.expanded Q
  let t := StoredLayoutTerms.terms Q.left Q.right e.1
  let m := StoredTermReference.lengthCount t.1
  let p := StoredTermReference.lengthCount e.1
  (⟨t.1,e.1,m.1,p.1,(StoredTermReference.length_value t.1).symm,
    (StoredTermReference.length_value e.1).symm⟩,1+e.2+t.2+m.2+p.2)

def budget (q W : Nat) := 9+9*q+8*W^2+5*W+2*q*(5+8*W^2+5*W)

theorem bound (Q : StoredTermQuery.Query n) (W : Nat)
    (hl : weight Q.left ≤ W) (hr : weight Q.right ≤ W)
    (hp : ∀ p ∈ (StoredTermQuery.expanded Q).1, weight p.1 ≤ W ∧ weight p.2 ≤ W) :
    (build Q).2 ≤ budget Q.premises.length W := by
  have he := StoredTermQuery.bound Q
  have hn := StoredTermQuery.length_bound Q
  have ht := StoredLayoutTerms.bound Q.left Q.right (StoredTermQuery.expanded Q).1 W hl hr hp
  have hm := StoredLayoutTerms.length_bound Q.left Q.right (StoredTermQuery.expanded Q).1 W hl hr hp
  have hx := Nat.mul_le_mul_right (5+8*W^2+5*W) hn
  simp only [build,StoredTermReference.length_cost,budget]
  nlinarith

theorem packed_terms {d : Nat} (Q : SubtypeTerms.Query n d) :
    (build (StoredTermQuery.packQuery Q)).1.terms = (SubtypeTerms.terms Q).map pack := by
  simp only [build,StoredTermQuery.packed_value]
  simp only [StoredTermQuery.packQuery]
  exact StoredLayoutTerms.packed_value Q

theorem packed_pairs {d : Nat} (Q : SubtypeTerms.Query n d) :
    (build (StoredTermQuery.packQuery Q)).1.pairs = StoredEdgeEmission.packPairs (SubtypeTerms.expanded Q) :=
  StoredTermQuery.packed_value Q

theorem packed_termCount {d : Nat} (Q : SubtypeTerms.Query n d) :
    (build (StoredTermQuery.packQuery Q)).1.termCount = (SubtypeTerms.terms Q).length := by
  rw [←(build (StoredTermQuery.packQuery Q)).1.terms_length,packed_terms,List.length_map]

theorem packed_pairCount {d : Nat} (Q : SubtypeTerms.Query n d) :
    (build (StoredTermQuery.packQuery Q)).1.pairCount = (SubtypeTerms.expanded Q).length := by
  rw [←(build (StoredTermQuery.packQuery Q)).1.pairs_length,packed_pairs]
  simp only [StoredEdgeEmission.packPairs,List.length_map]

theorem packed_wellFormed {d : Nat} (Q : SubtypeTerms.Query n d) :
    ∀ t ∈ (build (StoredTermQuery.packQuery Q)).1.terms, WellFormed d t := by
  rw [packed_terms]
  intro t ht
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
  exact pack_wellFormed u
end NSSE.StoredTermLayoutBuild
