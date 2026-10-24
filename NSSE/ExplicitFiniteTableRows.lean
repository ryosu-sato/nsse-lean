import NSSE.ExplicitUnaryTableLanguage

/-! Concrete finite-alphabet NFAs compiled to materialized unary Boolean tables.
Tabulation evaluates the input predicate once per table entry; no runtime
bound on an arbitrary input predicate is asserted here. -/

namespace NSSE.ExplicitFiniteTableRows

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ExplicitUnaryTableLanguage

variable {d n : Nat}

def compile (T : NSSE.NFA (Fin d ⊕ Bool) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] : Row language Empty n where
  initial q := truth (decide (T.start q))
  final q := truth (decide (T.accept q))
  data q r := unary (tabulate (fun x => decide (T.step q (.inl x) r)))
  left q r := truth (decide (T.step q (.inr false) r))
  right q r := truth (decide (T.step q (.inr true) r))
  guard := ⊤

theorem compile_markedNFA (T : NSSE.NFA (Fin d ⊕ Bool) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] (p : Empty → Fin d) :
    (compile T).markedNFA p = T := by
  unfold Row.markedNFA Row.dataNFA compile
  congr 1
  · funext q
    simp [truth_correct, unary_correct]
  · funext q x r
    cases x with
    | inl x => simp [truth_correct, unary_correct]
    | inr b => cases b <;> simp [truth_correct, unary_correct]
  · funext q
    simp [truth_correct, unary_correct]

def compileData (T : NSSE.NFA (Fin d) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] : Row language Empty n where
  initial q := truth (decide (T.start q))
  final q := truth (decide (T.accept q))
  data q r := unary (tabulate (fun x => decide (T.step q x r)))
  left _ _ := ⊥
  right _ _ := ⊥
  guard := ⊥

theorem compileData_dataNFA (T : NSSE.NFA (Fin d) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] (p : Empty → Fin d) :
    (compileData T).dataNFA p = T := by
  unfold Row.dataNFA compileData
  congr 1
  · funext q
    simp [truth_correct, unary_correct]
  · funext q x r
    simp [truth_correct, unary_correct]
  · funext q
    simp [truth_correct, unary_correct]

open ArrayAtomExistentialPackages DirectRowBooleanSize ExactReachabilitySize

theorem compile_qf (T : NSSE.NFA (Fin d ⊕ Bool) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] : RowQF (compile T) where
  initial _ := truth_qf _
  final _ := truth_qf _
  data _ _ := unary_qf _
  left _ _ := truth_qf _
  right _ _ := truth_qf _
  guard := BoundedFormula.IsQF.top

theorem compileData_qf (T : NSSE.NFA (Fin d) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] : RowQF (compileData T) where
  initial _ := truth_qf _
  final _ := truth_qf _
  data _ _ := unary_qf _
  left _ _ := BoundedFormula.isQF_bot
  right _ _ := BoundedFormula.isQF_bot
  guard := BoundedFormula.isQF_bot

theorem compile_fields (T : NSSE.NFA (Fin d ⊕ Bool) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] : Fields (compile T) 3 where
  initial _ := truth_nodes _
  final _ := truth_nodes _
  data _ _ := by change 1 ≤ 3; omega
  left _ _ := truth_nodes _
  right _ _ := truth_nodes _
  guard := by change 3 ≤ 3; omega

theorem compileData_fields (T : NSSE.NFA (Fin d) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] : Fields (compileData T) 3 where
  initial _ := truth_nodes _
  final _ := truth_nodes _
  data _ _ := by change 1 ≤ 3; omega
  left _ _ := by change 1 ≤ 3; omega
  right _ _ := by change 1 ≤ 3; omega
  guard := by change 1 ≤ 3; omega

/-- Total Boolean entries in the actual data-transition tables. -/
theorem data_table_entries (f : Fin n → Fin n → Fin d → Bool) :
    (∑ q : Fin n, ∑ r : Fin n, (tabulate (f q r)).length) = n*n*d := by
  simp only [tabulate_length, Finset.sum_const, Finset.card_fin, smul_eq_mul]
  simp [Nat.mul_assoc]

theorem compile_size (T : NSSE.NFA (Fin d ⊕ Bool) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] :
    ComputedScalarLoweringBudget.rowSize (compile T) ≤ n+3+n*6+n*n*9 := by
  have h := compile_fields T
  exact RankNextGuardSize.rowSize_le _ h.toRowSize h.initial h.final

theorem compileData_size (T : NSSE.NFA (Fin d) (Fin n))
    [DecidablePred T.start] [DecidablePred T.accept]
    [∀ q x r, Decidable (T.step q x r)] :
    ComputedScalarLoweringBudget.rowSize (compileData T) ≤ n+3+n*6+n*n*9 := by
  have h := compileData_fields T
  exact RankNextGuardSize.rowSize_le _ h.toRowSize h.initial h.final

end NSSE.ExplicitFiniteTableRows
