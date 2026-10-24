import NSSE.ConcreteValuationEvaluationTower
import NSSE.FiniteCapTerminal

/-! Original cap and seeded candidate automata represented by explicit
unary Boolean tables, with Fin 0 parameter valuations. -/

namespace NSSE.ExplicitOriginalSOARows

open GuardedBlockRelation GuardedRowFiring SymbolicGuardedBlocks OriginalCapRow
open ArrayAtomExistentialPackages ExplicitUnaryTableLanguage

variable {d n m : Nat}

def compile (A : NSSE.DFA (Fin d) (Fin n)) (B : NSSE.DFA (Fin d) (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept] :=
  RowParameterTransport.mapRow (Empty.elim : Empty → Fin 0)
    (ExplicitFiniteTableRows.compile (finiteAutomaton A B))

theorem compile_accepts_marked (A : NSSE.DFA (Fin d) (Fin n)) (B : NSSE.DFA (Fin d) (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept]
    (p : Fin 0 → Fin d) (s : Fin d) (pref gap tail : List (Fin d)) :
    ((compile A B).markedNFA p).Accepts
      (.inl s :: (pref.map Sum.inl ++ .inr false ::
        (gap.map Sum.inl ++ .inr true :: tail.map Sum.inl))) ↔
      A.Accepts pref ∧ B.Accepts gap ∧ tail ≠ [] := by
  rw [compile, RowParameterTransport.markedNFA_map, ExplicitFiniteTableRows.compile_markedNFA, finiteAutomaton,
    SymbolicComplement.pullback_accepts _ _ (stateAt_surjective n m), accepts_marked]

theorem firesAt_correct (A : NSSE.DFA (Fin d) (Fin n)) (B : NSSE.DFA (Fin d) (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept]
    (p : Fin 0 → Fin d) (s : Fin d) (body : List (Fin d)) (j t : Nat) :
    FiresAt (compile A B) p s body j t ↔
      j < t ∧ t < body.length ∧ A.Accepts (body.take j) ∧
        B.Accepts ((body.drop j).take (t - j)) ∧ NSSE.OccursSuffixAt body j t := by
  rw [FiresAt, markedOn_body]
  simp only [List.map_cons, List.cons_append, List.append_assoc]
  rw [compile_accepts_marked]
  simp only [compile, RowParameterTransport.mapRow, ExplicitFiniteTableRows.compile, FirstOrder.Language.Formula.realize_relabel, FirstOrder.Language.Formula.realize_top,
    true_and]
  constructor
  · rintro ⟨hjt, _, ⟨hA, hB, ht⟩, hcopy⟩
    exact ⟨hjt, List.length_lt_of_drop_ne_nil ht, hA, hB, hcopy⟩
  · rintro ⟨hjt, ht, hA, hB, hcopy⟩
    exact ⟨hjt, ht.le, ⟨hA, hB, fun he => (Nat.not_le_of_gt ht) (List.drop_eq_nil_iff.mp he)⟩, hcopy⟩

/-- The constructed Row fires exactly at the original cap occurrence;
both root and copied tail are positive, with the SAME literal cuts. -/
theorem fires_correct (A : NSSE.DFA (Fin d) (Fin n)) (B : NSSE.DFA (Fin d) (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept]
    (p : Fin 0 → Fin d) (s : Fin d) (body : List (Fin d)) :
    Fires (compile A B) p s body ↔ NSSE.MarkedOccurrence (NSSE.CapComponent.ofDFA A B) body := by
  simp only [Fires, firesAt_correct]
  rfl

theorem compile_qf (A : NSSE.DFA (Fin d) (Fin n)) (B : NSSE.DFA (Fin d) (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept] : RowQF (compile A B) :=
  RankCleanedQuantifierFree.parameter_map_qf _ _ (ExplicitFiniteTableRows.compile_qf _)

def candidate (C : NSSE.DFA (Fin d) (Fin n)) [DecidablePred C.accept] :=
  RowParameterTransport.mapRow (Empty.elim : Empty → Fin 0)
    (ExplicitFiniteTableRows.compileData (SeededDFARow.finiteAutomaton C))

theorem candidate_qf (C : NSSE.DFA (Fin d) (Fin n)) [DecidablePred C.accept] :
    RowQF (candidate C) :=
  RankCleanedQuantifierFree.parameter_map_qf _ _ (ExplicitFiniteTableRows.compileData_qf _)

theorem candidate_correct (C : NSSE.DFA (Fin d) (Fin n)) [DecidablePred C.accept]
    (p : Fin 0 → Fin d) (s : Fin d) (body : List (Fin d)) :
    ((candidate C).dataNFA p).Accepts (s :: body) ↔ C.Accepts body := by
  rw [candidate, RowParameterTransport.dataNFA_map, ExplicitFiniteTableRows.compileData_dataNFA,
    SeededDFARow.finiteAutomaton,
    SymbolicComplement.pullback_accepts _ _ (BlockCandidateTransport.stateAt_surjective n),
    SeededDFARow.accepts_cons]

theorem compile_size (A : NSSE.DFA (Fin d) (Fin n)) (B : NSSE.DFA (Fin d) (Fin m))
    [DecidablePred A.accept] [DecidablePred B.accept] :
    ComputedScalarLoweringBudget.rowSize (compile A B) ≤
      (n+m+3)+3+(n+m+3)*6+(n+m+3)*(n+m+3)*9 := by
  rw [compile, DirectRankResources.rowSize_parameter_map]
  simpa only [OriginalCapRow.length_states] using
    ExplicitFiniteTableRows.compile_size (OriginalCapRow.finiteAutomaton A B)

theorem candidate_size (C : NSSE.DFA (Fin d) (Fin n)) [DecidablePred C.accept] :
    ComputedScalarLoweringBudget.rowSize (candidate C) ≤ (n+1)+3+(n+1)*6+(n+1)*(n+1)*9 := by
  rw [candidate, DirectRankResources.rowSize_parameter_map]
  simpa only [BlockCandidateTransport.length_states] using
    ExplicitFiniteTableRows.compileData_size (SeededDFARow.finiteAutomaton C)

end NSSE.ExplicitOriginalSOARows
