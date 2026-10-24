import NSSE.StoredTermCompiler

namespace NSSE.StoredCompilerSize
variable {n d : Nat}

def literals (Q : StoredTermAssembly.Query n d) :=
  Q.constraints.upper.length+Q.constraints.lower.length+Q.constraints.bot.length+Q.constraints.top.length

theorem cast_literals {m : Nat} (h : n=m) (Q : StoredTermAssembly.Query n d) :
    literals (StoredTermCompiler.castQuery h Q) = literals Q := by subst m; rfl

theorem count (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q) (i : Fin d) :
    (StoredTermCompiler.compile Q h i).1.count ≤ 4*(StoredQuerySize.size Q)^2+5*StoredQuerySize.size Q+1 := by
  have hm := StoredQuerySize.termCount Q
  have hp := StoredQuerySize.pairCount Q
  have hn : n ≤ StoredQuerySize.size Q := by unfold StoredQuerySize.size; omega
  simp only [StoredTermCompiler.compile,StoredTermCompiler.dimension_value,
    (StoredTermLayoutBuild.build Q).1.terms_length]
  omega

theorem output (Q : StoredTermQuery.Query n) (h : StoredQueryWellFormed.query d Q) (i : Fin d) :
    literals (StoredTermCompiler.compile Q h i).1.output ≤ 8*(StoredQuerySize.size Q)^2+8*StoredQuerySize.size Q := by
  let L := (StoredTermLayoutBuild.build Q).1
  have ha := StoredTermAssembly.emitted_bound L.terms L.pairs L.pairs_length
    (StoredQueryWellFormed.generated Q h) i Q.left Q.right
  have hm := StoredQuerySize.termCount Q
  have hp := StoredQuerySize.pairCount Q
  simp only [StoredTermCompiler.compile]
  rw [cast_literals]
  unfold literals
  rw [←(StoredTermLayoutBuild.build Q).1.terms_length] at hm
  dsimp only [L] at ha
  omega
end NSSE.StoredCompilerSize
