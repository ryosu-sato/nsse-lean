import NSSE.AutomataMembership

/-!
# A semantic productivity certificate

For the noncomputable Presburger semantics it is useful to construct a
`ProductiveDFA` without asking the caller to supply a Boolean table.  The
table below is obtained by classical reflection of the exact accepting-tail
predicate.  This is not an executable reachability algorithm and makes no
decidability claim.
-/

namespace NSSE

universe u v

namespace DFA

noncomputable def classicalProductive
    (A : DFA α Q) : ProductiveDFA α Q := by
  classical
  exact
    { automaton := A
      productive := fun state =>
        decide (∃ tail, A.accept (A.runFrom state tail))
      productive_iff := by
        intro state
        simp }

@[simp] theorem classicalProductive_automaton
    (A : DFA α Q) :
    A.classicalProductive.automaton = A :=
  rfl

theorem classicalProductive_language
    (A : DFA α Q) :
    A.classicalProductive.language = A.language :=
  rfl

@[simp] theorem classicalProductive_productive_iff
    (A : DFA α Q) (state : Q) :
    A.classicalProductive.productive state = true ↔
      ∃ tail, A.accept (A.runFrom state tail) :=
  A.classicalProductive.productive_iff state

end DFA

end NSSE
