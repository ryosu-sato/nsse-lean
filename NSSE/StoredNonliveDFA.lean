import NSSE.StoredDFAExtensions

namespace NSSE.StoredNonliveDFA
variable {d : Nat}

def original (A : FiniteSOARankDecision.InputDFA (Fin d)) : FiniteSOARankDecision.InputDFA (Fin d) :=
  ⟨A.count,NonliveBorderRank.nonliveDFA A.automaton,inferInstance⟩

def final (A : StoredOrdinaryDFABuild.Data) (s : List Bool) (q : Fin A.count) : Bool × Nat :=
  let a := StoredDFAAccess.final A q
  let l := StoredForwardLookup.get false s q.val
  (a.1 && !l.1,2+a.2+l.2)

def build (A : StoredOrdinaryDFABuild.Data) : StoredOrdinaryDFABuild.Data × Nat :=
  let e := StoredDFAExtensions.build (d := d) A A.count
  let f := CountedFinEnumeration.tabulate A.count (final A e.1)
  ({A with final := f.1},1+e.2+f.2)

def budget (n d : Nat) := 1+StoredDFAExtensions.budget n d n+
  StoredForwardTableBuild.tabBudget n (2+2*n)

theorem final_bound (A : StoredOrdinaryDFABuild.Data) (s : List Bool) (q : Fin A.count) :
    (final A s q).2 ≤ 2+2*A.count := by
  have ha := StoredDFAAccess.final_bound A q
  have hl := (StoredForwardLookup.get_bound false s q.val).trans q.isLt
  simp only [final]; omega

theorem bound (A : StoredOrdinaryDFABuild.Data) (h : StoredDFAProductCells.Valid (d := d) A) :
    (build (d := d) A).2 ≤ budget A.count d := by
  have he := StoredDFAExtensions.bound A h A.count
  have hf := CountedFinEnumeration.tabulate_bound A.count
    (final A (StoredDFAExtensions.build (d := d) A A.count).1) (2+2*A.count) (final_bound A _)
  simp only [build,budget]
  dsimp only [StoredForwardTableBuild.tabBudget] at *
  omega

theorem possible_live (A : FiniteSOARankDecision.InputDFA (Fin d)) (q : Fin A.count) :
    StoredDFAExtensions.possible A A.count q ↔ (NonliveBorderRank.liveDFA A.automaton).accept q := by
  unfold StoredDFAExtensions.possible NonliveBorderRank.liveDFA
  dsimp only
  rw [Fintype.card_fin]

theorem value (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A)).1 =
      StoredOrdinaryDFABuild.snapshot (original A) := by
  have hf (q : Fin A.count) :
      (final (StoredOrdinaryDFABuild.snapshot A)
        (StoredDFAExtensions.build (d := d) (StoredOrdinaryDFABuild.snapshot A) A.count).1 q).1 =
        decide ((NonliveBorderRank.nonliveDFA A.automaton).accept q) := by
    change _ = decide (A.automaton.accept q ∧ ¬ (NonliveBorderRank.liveDFA A.automaton).accept q)
    apply Bool.eq_iff_iff.mpr
    simp only [final]
    rw [StoredDFAExtensions.value]
    simp only [StoredDFAAccess.final,StoredOrdinaryDFABuild.snapshot,
      StoredForwardLookup.get_ofFn,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,
      decide_eq_false_iff_not]
    exact and_congr Iff.rfl (not_congr (possible_live A q))
  simp only [build,CountedFinEnumeration.tabulate_value]
  change {StoredOrdinaryDFABuild.snapshot A with final := List.ofFn (fun q : Fin A.count =>
    (final (StoredOrdinaryDFABuild.snapshot A)
      (StoredDFAExtensions.build (d := d) (StoredOrdinaryDFABuild.snapshot A) A.count).1 q).1)} = _
  simp only [StoredOrdinaryDFABuild.snapshot,original]
  congr 1
  exact congrArg List.ofFn (funext hf)

theorem bound_snapshot (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A)).2 ≤ budget A.count d :=
  bound _ (StoredDFAProductCells.valid_snapshot A)
end NSSE.StoredNonliveDFA
