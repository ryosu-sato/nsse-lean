import NSSE.StoredPeriodIndex

namespace NSSE.StoredPeriodTable
variable {d p : Nat}

def initial (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (hp : 0<p) : PeriodMonitorState (Fin d) (Fin A.count) p :=
  ⟨⟨[],by simp⟩,⟨A.start,hA.start⟩,⟨0,hp⟩,true,false⟩

def cell (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (hp : 0<p) (states : List (PeriodMonitorState (Fin d) (Fin A.count) p))
    (s : PeriodMonitorState (Fin d) (Fin A.count) p) (i : Fin d) : Nat × Nat :=
  let t := StoredPeriodCells.step A hA hp s i
  let k := StoredPeriodIndex.index t.1 states
  (k.1,1+t.2+k.2)

def cellBudget (d n p k : Nat) := 1+StoredPeriodCells.stepBudget n d p+StoredPeriodIndex.budget d n p k

theorem cell_bound (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (hp : 0<p) (states : List (PeriodMonitorState (Fin d) (Fin A.count) p))
    (s : PeriodMonitorState (Fin d) (Fin A.count) p) (i : Fin d) :
    (cell A hA hp states s i).2 ≤ cellBudget d A.count p states.length := by
  have ht := StoredPeriodCells.step_bound A hA hp s i
  have hk := StoredPeriodIndex.bound (StoredPeriodCells.step A hA hp s i).1 states
  simp only [cell,cellBudget]
  omega

theorem cell_value (A : FiniteSOARankDecision.InputDFA (Fin d)) (hp : 0<p)
    (states : List (PeriodMonitorState (Fin d) (Fin A.count) p))
    (s : PeriodMonitorState (Fin d) (Fin A.count) p) (i : Fin d) :
    (cell (StoredOrdinaryDFABuild.snapshot A) (StoredDFAProductCells.valid_snapshot A) hp states s i).1 =
      states.idxOf (periodMonitorStep A.automaton hp s i) := by
  simp only [cell,StoredPeriodIndex.index_value,StoredPeriodCells.step_value]

def build (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (hp : 0<p) (states : List (PeriodMonitorState (Fin d) (Fin A.count) p)) :
    StoredOrdinaryDFABuild.Data × Nat :=
  let k := StoredTermReference.lengthCount states
  let s := StoredPeriodIndex.index (initial A hA hp) states
  let t := CountedListConstruction.map
    (fun q => CountedFinEnumeration.tabulate d (cell A hA hp states q)) states
  let f := CountedListConstruction.map (StoredPeriodCells.final A) states
  (⟨k.1,s.1,t.1,f.1⟩,3+k.2+s.2+t.2+f.2)

def budget (d n p k : Nat) :=
  3+(k+1)+StoredPeriodIndex.budget d n p k+
    (1+k*(1+StoredForwardTableBuild.tabBudget d (cellBudget d n p k)))+
    (1+k*(1+(n+2*p+5)))

theorem bound (A : StoredOrdinaryDFABuild.Data) (hA : StoredDFAProductCells.Valid (d := d) A)
    (hp : 0<p) (states : List (PeriodMonitorState (Fin d) (Fin A.count) p)) :
    (build A hA hp states).2 ≤ budget d A.count p states.length := by
  have hs := StoredPeriodIndex.bound (initial A hA hp) states
  have ht := CountedListConstruction.map_bound
    (fun q => CountedFinEnumeration.tabulate d (cell A hA hp states q)) states
    (StoredForwardTableBuild.tabBudget d (cellBudget d A.count p states.length))
    (fun q _ => CountedFinEnumeration.tabulate_bound _ _ _ (cell_bound A hA hp states q))
  have hf := CountedListConstruction.map_bound (StoredPeriodCells.final A) states
    (A.count+2*p+5) (fun q _ => StoredPeriodCells.final_bound A q)
  simp only [build,budget,StoredTermReference.length_cost]
  omega

theorem map_get {α β : Type} (xs : List α) (f : α → β) :
    List.ofFn (fun i : Fin xs.length => f (xs.get i)) = xs.map f := by
  apply List.ext_getElem <;> simp

theorem value (A : FiniteSOARankDecision.InputDFA (Fin d)) (hp : 0<p)
    (states : List (PeriodMonitorState (Fin d) (Fin A.count) p))
    (complete : ∀ s, s ∈ states) :
    (build (StoredOrdinaryDFABuild.snapshot A) (StoredDFAProductCells.valid_snapshot A) hp states).1 =
      StoredOrdinaryDFABuild.snapshot
        (FiniteDFAOperations.ofEnumerated (boundedPeriodDFA A.automaton p hp) states complete) := by
  simp only [build,StoredTermReference.length_value,StoredPeriodIndex.index_value,
    CountedListConstruction.map_value,CountedFinEnumeration.tabulate_value,cell_value]
  have hf (s : PeriodMonitorState (Fin d) (Fin A.count) p) :
      (StoredPeriodCells.final (StoredOrdinaryDFABuild.snapshot A) s).1 =
        decide ((boundedPeriodDFA A.automaton p hp).accept s) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using StoredPeriodCells.final_value A hp s)
  simp only [hf,StoredOrdinaryDFABuild.snapshot,FiniteDFAOperations.ofEnumerated,
    FiniteDFAOperations.encode]
  congr 1
  · exact (map_get states (fun s => List.ofFn (fun i : Fin d =>
      states.idxOf (periodMonitorStep A.automaton hp s i)))).symm
  · exact (List.map_congr_left (fun s _ => hf s)).trans
      (map_get states (fun s => decide ((boundedPeriodDFA A.automaton p hp).accept s))).symm
end NSSE.StoredPeriodTable
