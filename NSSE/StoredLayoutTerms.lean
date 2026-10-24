import NSSE.StoredTermQuery

namespace NSSE.StoredLayoutTerms
open StoredSubtypeTerm
variable {n : Nat}

def pair (p : Term n × Term n) : List (Term n) × Nat :=
  let a := StoredSubterms.subterms p.1
  let b := StoredSubterms.subterms p.2
  let c := CountedListConstruction.append a.1 b.1
  (c.1,1+a.2+b.2+c.2)

theorem pair_length (p : Term n × Term n) (W : Nat) (h : weight p.1 ≤ W ∧ weight p.2 ≤ W) :
    (pair p).1.length ≤ 2*W := by
  have ha := StoredSubterms.length_bound p.1
  have hb := StoredSubterms.length_bound p.2
  simp only [pair,CountedListConstruction.append_value,List.length_append]; omega

theorem pair_bound (p : Term n × Term n) (W : Nat) (h : weight p.1 ≤ W ∧ weight p.2 ≤ W) :
    (pair p).2 ≤ 2+8*W^2+W := by
  have ha : (StoredSubterms.subterms p.1).2 ≤ 4*W^2 :=
    (StoredSubterms.bound p.1).trans (by gcongr; exact h.1)
  have hb : (StoredSubterms.subterms p.2).2 ≤ 4*W^2 :=
    (StoredSubterms.bound p.2).trans (by gcongr; exact h.2)
  have hl := StoredSubterms.length_bound p.1
  simp only [pair,CountedListConstruction.append_cost]; omega

def terms (left right : Term n) (ps : List (Term n × Term n)) : List (Term n) × Nat :=
  let l := StoredSubterms.subterms left
  let r := StoredSubterms.subterms right
  let p := CountedListConstruction.flatMap pair ps
  let a := CountedListConstruction.append l.1 r.1
  let b := CountedListConstruction.append a.1 p.1
  (b.1,2+l.2+r.2+p.2+a.2+b.2)

theorem bound (left right : Term n) (ps : List (Term n × Term n)) (W : Nat)
    (hl : weight left ≤ W) (hr : weight right ≤ W)
    (hp : ∀ p ∈ ps, weight p.1 ≤ W ∧ weight p.2 ≤ W) :
    (terms left right ps).2 ≤ 5+8*W^2+3*W+ps.length*(4+8*W^2+3*W) := by
  have ha : (StoredSubterms.subterms left).2 ≤ 4*W^2 :=
    (StoredSubterms.bound left).trans (by gcongr)
  have hb : (StoredSubterms.subterms right).2 ≤ 4*W^2 :=
    (StoredSubterms.bound right).trans (by gcongr)
  have hc := CountedListConstruction.flatMap_bound pair ps (2+8*W^2+W) (2*W)
    (fun p h => pair_bound p W (hp p h)) (fun p h => pair_length p W (hp p h))
  have hd := StoredSubterms.length_bound left
  have he := StoredSubterms.length_bound right
  simp only [terms,CountedListConstruction.append_cost,CountedListConstruction.append_value,List.length_append]
  have hn : 2+(2+8*W^2+W)+2*W = 4+8*W^2+3*W := by omega
  rw [hn] at hc
  omega

theorem length_bound (left right : Term n) (ps : List (Term n × Term n)) (W : Nat)
    (hl : weight left ≤ W) (hr : weight right ≤ W)
    (hp : ∀ p ∈ ps, weight p.1 ≤ W ∧ weight p.2 ≤ W) :
    (terms left right ps).1.length ≤ 2*W+ps.length*(2*W) := by
  have hf : (ps.flatMap (fun p => (pair p).1)).length ≤ ps.length*(2*W) := by
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have ha := pair_length p W (hp p (by simp))
      have hb := ih (fun a ha => hp a (by simp [ha]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      nlinarith
  have ha := StoredSubterms.length_bound left
  have hb := StoredSubterms.length_bound right
  simp only [terms,CountedListConstruction.append_value,CountedListConstruction.flatMap_value,List.length_append]
  omega

theorem pair_value {d : Nat} (p : SubtypeTerms.Term n d × SubtypeTerms.Term n d) :
    (pair (pack p.1,pack p.2)).1 = (SubtypeTerms.subterms p.1 ++ SubtypeTerms.subterms p.2).map pack := by
  simp only [pair,CountedListConstruction.append_value,StoredSubterms.packed_value,List.map_append]

theorem packed_value {d : Nat} (Q : SubtypeTerms.Query n d) :
    (terms (pack Q.left) (pack Q.right) (StoredEdgeEmission.packPairs (SubtypeTerms.expanded Q))).1 =
      (SubtypeTerms.terms Q).map pack := by
  simp only [terms,CountedListConstruction.append_value,CountedListConstruction.flatMap_value,
    StoredEdgeEmission.packPairs,List.flatMap_map,Function.comp_def,pair_value,
    StoredSubterms.packed_value,SubtypeTerms.terms,List.map_append,List.map_flatMap]
end NSSE.StoredLayoutTerms
