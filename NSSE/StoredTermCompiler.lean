import NSSE.StoredQueryWellFormed
import NSSE.StoredTermAssembly

namespace NSSE.StoredTermCompiler
open StoredSubtypeTerm
variable {n d : Nat}

structure Result (d : Nat) where
  count : Nat
  output : StoredTermAssembly.Query count d

def dimension (L : StoredTermLayoutBuild.Layout n) : Nat × Nat :=
  let a := CountedSupportRule.add L.termCount (L.pairCount+1)
  let b := CountedSupportRule.add n a.1
  (b.1,2+a.2+b.2)

theorem dimension_value (L : StoredTermLayoutBuild.Layout n) :
    (dimension L).1 = n+(L.terms.length+(L.pairCount+1)) := by
  simp only [dimension,CountedSupportRule.add_value,L.terms_length]

theorem dimension_cost (L : StoredTermLayoutBuild.Layout n) :
    (dimension L).2 = n+L.termCount+4 := by
  simp only [dimension,CountedSupportRule.add_cost]; omega

def castQuery {a b : Nat} (h : a=b) (Q : StoredTermAssembly.Query a d) : StoredTermAssembly.Query b d :=
  h ▸ Q

def compile (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q) (i : Fin d) : Result d × Nat :=
  let L := StoredTermLayoutBuild.build Q
  let k := dimension L.1
  let a := StoredTermAssembly.assemble L.1.terms L.1.pairs L.1.pairs_length
    (StoredQueryWellFormed.generated Q h) i Q.left Q.right
  (⟨k.1,castQuery (dimension_value L.1).symm a.1⟩,2+L.2+k.2+a.2)

def budget (S d : Nat) :=
  2+(16*S^3+18*S^2+24*S+9)+(S+(2*S+4*S^2)+4)+
    StoredTermAssembly.budget S (2*S+4*S^2) (2*S) d S

theorem bound (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q) (i : Fin d) :
    (compile Q h i).2 ≤ budget (StoredQuerySize.size Q) d := by
  let S := StoredQuerySize.size Q
  let L := (StoredTermLayoutBuild.build Q).1
  have hn : n ≤ S := by dsimp [S,StoredQuerySize.size]; omega
  have hm : L.termCount ≤ 2*S+4*S^2 := StoredQuerySize.termCount Q
  have hml : L.terms.length ≤ 2*S+4*S^2 := L.terms_length.trans_le hm
  have hp : L.pairCount ≤ 2*S := StoredQuerySize.pairCount Q
  have ha := StoredTermAssembly.bound L.terms L.pairs L.pairs_length
    (StoredQueryWellFormed.generated Q h) i Q.left Q.right S
    (StoredQuerySize.generated_terms Q) (StoredQuerySize.pairs Q)
    (StoredQuerySize.left Q) (StoredQuerySize.right Q)
  have ham : StoredTermAssembly.budget n L.terms.length L.pairCount d S ≤
      StoredTermAssembly.budget S (2*S+4*S^2) (2*S) d S := by
    unfold StoredTermAssembly.budget StoredTermClause.budget StoredEdgeEmission.budget
      StoredEdgeClause.budget StoredPaddedLiteral.budget
    gcongr
  have hb := StoredQuerySize.build_cubic Q
  have hac := ha.trans ham
  simp only [compile,dimension_cost,budget]
  change 2+(StoredTermLayoutBuild.build Q).2+(n+L.termCount+4)+_ ≤
    2+(16*S^3+18*S^2+24*S+9)+(S+(2*S+4*S^2)+4)+_
  dsimp only [L,S] at *
  omega
theorem count_packed (Q : SubtypeTerms.Query n d) (i : Fin d) :
    (compile (StoredTermQuery.packQuery Q) (StoredQueryWellFormed.packed Q) i).1.count =
      (SubtypeTermLayout.layout Q).count := by
  simp only [compile,dimension_value,StoredTermLayoutBuild.packed_terms,List.length_map,
    StoredTermLayoutBuild.packed_pairCount]
  rfl

theorem transport_cast {a b c : Nat} (h : a=b) (k : b=c) (Q : StoredTermAssembly.Query a d) :
    StoredTermAssembly.transport k (castQuery h Q) = StoredTermAssembly.transport (h.trans k) Q := by
  subst b; subst c; rfl

theorem assembly_value (Q : SubtypeTerms.Query n d) (i : Fin d)
    (ts : List (Term n)) (ps : List (Term n × Term n)) (p : Nat)
    (hp : ps.length=p) (ht : ∀ t ∈ ts, WellFormed d t)
    (hk : n+(ts.length+(p+1)) = (SubtypeTermLayout.layout Q).count)
    (hts : ts = (SubtypeTerms.terms Q).map pack)
    (hps : ps = StoredEdgeEmission.packPairs (SubtypeTerms.expanded Q))
    (hpc : p = (SubtypeTerms.expanded Q).length) :
    StoredTermAssembly.transport hk
      (StoredTermAssembly.assemble ts ps hp ht i (pack Q.left) (pack Q.right)).1 =
      SubtypeTermFlattening.flatten Q i := by
  subst ts; subst ps; subst p
  exact StoredTermAssembly.flatten_value Q i

theorem value (Q : SubtypeTerms.Query n d) (i : Fin d) :
    StoredTermAssembly.transport (count_packed Q i)
      (compile (StoredTermQuery.packQuery Q) (StoredQueryWellFormed.packed Q) i).1.output =
      SubtypeTermFlattening.flatten Q i := by
  simp only [compile,transport_cast]
  exact assembly_value Q i _ _ _ _ _ _ (StoredTermLayoutBuild.packed_terms Q)
    (StoredTermLayoutBuild.packed_pairs Q) (StoredTermLayoutBuild.packed_pairCount Q)
end NSSE.StoredTermCompiler
