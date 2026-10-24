import NSSE.StoredEdgeEmission

/-! Counted assembly from stored layout data. Layout construction is separate. -/
namespace NSSE.StoredTermAssembly
open StoredSubtypeTerm
variable {n d p : Nat}

structure Query (n d : Nat) where
  constraints : StoredSubtypeInput.Input n d
  left : Fin n
  right : Fin n

def assemble (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (ht : ∀ t ∈ ts, WellFormed d t) (i : Fin d) (left right : Term n) :
    Query (n+(ts.length+(p+1))) d × Nat :=
  let a := StoredTermDefinitions.collect ts p ts ht
  let b := StoredEdgeEmission.edges ts ps hp i
  let c := StoredTermDefinitions.combine a.1 b.1
  let l := StoredTermReference.resolve ts p left
  let r := StoredTermReference.resolve ts p right
  (⟨c.1,l.1,r.1⟩,1+a.2+b.2+c.2+l.2+r.2)

def budget (n m p d W : Nat) :=
  7+m*(8+StoredTermClause.budget n m d W)+StoredEdgeEmission.budget n m p d W+
    2*m+2*(n+2*m+8+m*(1+2*W))

theorem bound (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (ht : ∀ t ∈ ts, WellFormed d t) (i : Fin d) (left right : Term n) (W : Nat)
    (hw : ∀ t ∈ ts, weight t ≤ W) (hps : ∀ a ∈ ps, weight a.1 ≤ W ∧ weight a.2 ≤ W)
    (hl : weight left ≤ W) (hr : weight right ≤ W) :
    (assemble ts ps hp ht i left right).2 ≤ budget n ts.length p d W := by
  have ha := StoredTermDefinitions.bound ts p ts ht W hw
  have hb := StoredEdgeEmission.bound ts ps hp i W hps
  have hc := StoredTermDefinitions.emitted_bound ts p ts ht
  have hd := StoredTermReference.uniform_bound ts p left n ts.length W (by rfl) (by rfl) hl
  have he := StoredTermReference.uniform_bound ts p right n ts.length W (by rfl) (by rfl) hr
  simp only [assemble,StoredTermDefinitions.combine_cost,budget]
  dsimp only at hc
  omega

theorem emitted_bound (ts : List (Term n)) (ps : List (Term n × Term n)) (hp : ps.length=p)
    (ht : ∀ t ∈ ts, WellFormed d t) (i : Fin d) (left right : Term n) :
    let I := (assemble ts ps hp ht i left right).1.constraints
    I.upper.length+I.lower.length+I.bot.length+I.top.length ≤ 2*ts.length+2*p := by
  have ha := StoredTermDefinitions.emitted_bound ts p ts ht
  have hb := StoredEdgeEmission.emitted ts ps hp i (CountedFinEnumeration.enumerate p).1
  simp only [CountedFinEnumeration.value,List.length_finRange] at hb
  simp only [assemble,StoredTermDefinitions.combine,CountedListConstruction.append_value,
    List.length_append,StoredEdgeEmission.edges,CountedFinEnumeration.value]
  dsimp only at ha hb
  omega

def transport {a b : Nat} (h : a=b) (Q : Query a d) : SubtypeConstraints.Query b d :=
  ⟨StoredTermClause.transport h Q.constraints,Fin.cast h Q.left,Fin.cast h Q.right⟩

theorem packed_value (L : SubtypeTermLayout.Layout n d) (i : Fin d)
    (left right : SubtypeTerms.Term n d) :
    transport (by simp only [List.length_map]; rfl)
      (assemble (p := L.pairs.length) (L.terms.map pack) (StoredEdgeEmission.packPairs L.pairs)
        (by simp [StoredEdgeEmission.packPairs])
        (by intro t ht; obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht; exact pack_wellFormed u)
        i (pack left) (pack right)).1 =
      ⟨SubtypeConstraintOperations.combine (SubtypeTermDefinitions.definitions L)
        (SubtypeTermFlattening.edges L i),L.ref left,L.ref right⟩ := by
  simp only [assemble,transport,StoredTermDefinitions.combine_value,
    StoredTermDefinitions.definitions_value,StoredEdgeEmission.value,StoredEdgeClause.ref_packed]

theorem flatten_value (Q : SubtypeTerms.Query n d) (i : Fin d) :
    let L := SubtypeTermLayout.layout Q
    transport (by simp only [List.length_map]; rfl)
      (assemble (p := L.pairs.length) (L.terms.map pack) (StoredEdgeEmission.packPairs L.pairs)
        (by simp [StoredEdgeEmission.packPairs])
        (by intro t ht; obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht; exact pack_wellFormed u)
        i (pack Q.left) (pack Q.right)).1 = SubtypeTermFlattening.flatten Q i :=
  packed_value (SubtypeTermLayout.layout Q) i Q.left Q.right
end NSSE.StoredTermAssembly
