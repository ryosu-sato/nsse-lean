import NSSE.StoredUnaryLabel

namespace NSSE.StoredDataLabels
variable {d : Nat}

def marked (A : StoredCapRowNFABuild.Data) (q r : Fin A.count) : StoredUnaryLabel.Atom × Nat :=
  StoredUnaryLabel.build (fun i : Fin d => StoredMarkedNFAAccess.step A q r (.inl i))
def plain (A : StoredRightIdealNFABuild.Data) (q r : Fin A.count) : StoredUnaryLabel.Atom × Nat :=
  StoredUnaryLabel.build (fun i : Fin d => StoredPlainNFAAccess.step A q r i)

theorem marked_bound (A : StoredCapRowNFABuild.Data) (q r : Fin A.count) :
    (marked (d := d) A q r).2 ≤ 1+StoredForwardTableBuild.tabBudget d (2*A.count+d+3) :=
  StoredUnaryLabel.bound _ _ (fun i => StoredMarkedNFAAccess.step_bound A q r (.inl i))
theorem plain_bound (A : StoredRightIdealNFABuild.Data) (q r : Fin A.count) :
    (plain (d := d) A q r).2 ≤ 1+StoredForwardTableBuild.tabBudget d (2*A.count+d+2) :=
  StoredUnaryLabel.bound _ _ (fun i => StoredPlainNFAAccess.step_bound A q r i)

theorem marked_value (A : StoredCapRowNFABuild.Data) (q r : Fin A.count) :
    StoredUnaryLabel.denote (d := d) (P := Empty) (marked (d := d) A q r).1 =
      (AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) A)).data q r := by
  simp only [marked,StoredUnaryLabel.denote_value,AlphabetTableRows.compile,StoredMarkedNFAAccess.input,Bool.decide_coe]

theorem plain_value (A : StoredRightIdealNFABuild.Data) (q r : Fin A.count) :
    StoredUnaryLabel.denote (d := d) (P := Empty) (plain (d := d) A q r).1 =
      (AlphabetTableRows.compileData (StoredPlainNFAAccess.input (d := d) A)).data q r := by
  simp only [plain,StoredUnaryLabel.denote_value,AlphabetTableRows.compileData,StoredPlainNFAAccess.input,Bool.decide_coe]

def table (n : Nat) (f : Fin n → Fin n → StoredUnaryLabel.Atom × Nat) : List (List StoredUnaryLabel.Atom) × Nat :=
  CountedFinEnumeration.tabulate n (fun q => CountedFinEnumeration.tabulate n (f q))

theorem table_value (n : Nat) (f : Fin n → Fin n → StoredUnaryLabel.Atom × Nat) :
    (table n f).1 = List.ofFn (fun q => List.ofFn (fun r => (f q r).1)) := by
  simp only [table,CountedFinEnumeration.tabulate_value]

theorem table_bound (n c : Nat) (f : Fin n → Fin n → StoredUnaryLabel.Atom × Nat)
    (h : ∀ q r, (f q r).2 ≤ c) :
    (table n f).2 ≤ StoredForwardTableBuild.tabBudget n (StoredForwardTableBuild.tabBudget n c) :=
  CountedFinEnumeration.tabulate_bound n _ _ (fun q => CountedFinEnumeration.tabulate_bound n (f q) c (h q))

def buildMarked (A : StoredCapRowNFABuild.Data) := table A.count (marked (d := d) A)
def buildPlain (A : StoredRightIdealNFABuild.Data) := table A.count (plain (d := d) A)

theorem buildMarked_bound (A : StoredCapRowNFABuild.Data) :
    (buildMarked (d := d) A).2 ≤ StoredForwardTableBuild.tabBudget A.count
      (StoredForwardTableBuild.tabBudget A.count (1+StoredForwardTableBuild.tabBudget d (2*A.count+d+3))) :=
  table_bound _ _ _ (marked_bound A)
theorem buildPlain_bound (A : StoredRightIdealNFABuild.Data) :
    (buildPlain (d := d) A).2 ≤ StoredForwardTableBuild.tabBudget A.count
      (StoredForwardTableBuild.tabBudget A.count (1+StoredForwardTableBuild.tabBudget d (2*A.count+d+2))) :=
  table_bound _ _ _ (plain_bound A)

theorem buildMarked_value (A : StoredCapRowNFABuild.Data) :
    (buildMarked (d := d) A).1.map (List.map (StoredUnaryLabel.denote (d := d) (P := Empty))) =
      List.ofFn (fun q => List.ofFn (fun r => (AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) A)).data q r)) := by
  simp only [buildMarked,table_value,List.map_ofFn,Function.comp_def,marked_value]

theorem buildPlain_value (A : StoredRightIdealNFABuild.Data) :
    (buildPlain (d := d) A).1.map (List.map (StoredUnaryLabel.denote (d := d) (P := Empty))) =
      List.ofFn (fun q => List.ofFn (fun r => (AlphabetTableRows.compileData (StoredPlainNFAAccess.input (d := d) A)).data q r)) := by
  simp only [buildPlain,table_value,List.map_ofFn,Function.comp_def,plain_value]
def evaluateTable {n : Nat} (xs : List (List StoredUnaryLabel.Atom)) (q r : Fin n) (i : Fin d) : Bool × Nat :=
  let row := StoredForwardLookup.get [] xs q.val
  let a := StoredForwardLookup.get (.constant false) row.1 r.val
  let v := StoredUnaryLabel.evaluate a.1 i
  (v.1,2+row.2+a.2+v.2)

theorem evaluateTable_bound {n : Nat} (xs : List (List StoredUnaryLabel.Atom)) (q r : Fin n) (i : Fin d) :
    (evaluateTable xs q r i).2 ≤ 2*n+d+3 := by
  have hq := (StoredForwardLookup.get_bound [] xs q.val).trans q.isLt
  have hr := (StoredForwardLookup.get_bound (StoredUnaryLabel.Atom.constant false)
    (StoredForwardLookup.get [] xs q.val).1 r.val).trans r.isLt
  have hv := StoredUnaryLabel.evaluate_bound
    (StoredForwardLookup.get (.constant false) (StoredForwardLookup.get [] xs q.val).1 r.val).1 i
  simp only [evaluateTable]; omega

theorem evaluateTable_value {n : Nat} (f : Fin n → Fin n → StoredUnaryLabel.Atom × Nat) (q r : Fin n) (i : Fin d) :
    (evaluateTable (table n f).1 q r i).1 = (StoredUnaryLabel.evaluate (f q r).1 i).1 := by
  simp only [evaluateTable,table_value,StoredForwardLookup.get_ofFn]
theorem evaluateMarked_correct (A : StoredCapRowNFABuild.Data) (q r : Fin A.count) (i : Fin d) :
    (evaluateTable (buildMarked (d := d) A).1 q r i).1 = true ↔
      ((AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) A)).data q r).Realize
        (Sum.elim (Empty.elim : Empty → Fin d) (fun _ => i)) := by
  have h := StoredUnaryLabel.evaluate_correct (marked (d := d) A q r).1 (Empty.elim : Empty → Fin d) i
  rw [marked_value] at h
  simpa only [buildMarked,evaluateTable_value] using h

theorem evaluatePlain_correct (A : StoredRightIdealNFABuild.Data) (q r : Fin A.count) (i : Fin d) :
    (evaluateTable (buildPlain (d := d) A).1 q r i).1 = true ↔
      ((AlphabetTableRows.compileData (StoredPlainNFAAccess.input (d := d) A)).data q r).Realize
        (Sum.elim (Empty.elim : Empty → Fin d) (fun _ => i)) := by
  have h := StoredUnaryLabel.evaluate_correct (plain (d := d) A q r).1 (Empty.elim : Empty → Fin d) i
  rw [plain_value] at h
  simpa only [buildPlain,evaluateTable_value] using h
end NSSE.StoredDataLabels
