import NSSE.StoredCompilerSize
import NSSE.ListFiniteSATSize
import NSSE.TermEntailmentDecision

namespace NSSE.StoredTermFiniteSAT
variable {n d : Nat}

def decide (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q) (hd : 0<d) : Bool × Nat :=
  let c := StoredTermCompiler.compile Q h ⟨0,hd⟩
  let s := ListFiniteSatisfiability.decide c.1.output.constraints
  (s.1,1+c.2+s.2)

theorem solver_transport {m : Nat} (h : n=m) (Q : StoredTermAssembly.Query n d) :
    (ListFiniteSatisfiability.decide Q.constraints).1 =
      FiniteSubtypeDecision.decideSatisfiable (StoredTermAssembly.transport h Q).constraints := by
  subst m
  rw [ListFiniteSatisfiability.value]
  congr 1
  have ht : StoredTermLiteral.transport (rfl : n=n) =
      (StoredSubtypeInput.Bound.denote : StoredSubtypeInput.Bound n d → _) := by
    funext a
    apply Prod.ext
    · rfl
    · funext i; rfl
  simp only [StoredTermAssembly.transport,StoredTermClause.transport,ht,
    StoredSubtypeInput.Input.denote,Fin.cast_refl,List.map_id]

theorem value (Q : SubtypeTerms.Query n d) (hd : 0<d) :
    (decide (StoredTermQuery.packQuery Q) (StoredQueryWellFormed.packed Q) hd).1 =
      TermEntailmentDecision.decideFiniteSatisfiable Q hd := by
  simp only [decide]
  rw [solver_transport (StoredTermCompiler.count_packed Q ⟨0,hd⟩),StoredTermCompiler.value]
  rfl

theorem correct (Q : SubtypeTerms.Query n d) (hd : 0<d) :
    (decide (StoredTermQuery.packQuery Q) (StoredQueryWellFormed.packed Q) hd).1 = true ↔
      SubtypeTerms.Satisfiable (FiniteSubtypeTrees.constructor d) Q := by
  rw [value,TermEntailmentDecision.decideFiniteSatisfiable_correct]

def budget (S d : Nat) := 1+StoredTermCompiler.budget S d+
  ListFiniteSATSize.budget (4*S^2+5*S+1) d (8*S^2+8*S)

theorem bound (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q) (hd : 0<d) :
    (decide Q h hd).2 ≤ budget (StoredQuerySize.size Q) d := by
  let c := StoredTermCompiler.compile Q h ⟨0,hd⟩
  let S := StoredQuerySize.size Q
  let M := 8*S^2+8*S
  have hm : StoredCompilerSize.literals c.1.output ≤ M := StoredCompilerSize.output Q h ⟨0,hd⟩
  have hn := StoredCompilerSize.count Q h ⟨0,hd⟩
  have hc := StoredTermCompiler.bound Q h ⟨0,hd⟩
  have hs := ListFiniteSATSize.bound c.1.output.constraints M
    (by unfold StoredCompilerSize.literals at hm; omega)
    (by unfold StoredCompilerSize.literals at hm; omega)
    (by unfold StoredCompilerSize.literals at hm; omega)
    (by unfold StoredCompilerSize.literals at hm; omega)
  have ht := ListFiniteSATSize.mono c.1.count d M (4*S^2+5*S+1) d hn (by rfl)
  have hf := hs.trans ht
  simp only [decide,budget]
  dsimp only [c,S,M] at *
  omega
end NSSE.StoredTermFiniteSAT
