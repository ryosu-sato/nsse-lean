import NSSE.StoredCapRowIndexed

namespace NSSE.StoredCapRowNFABuild
open StoredForwardTableBuild StoredForwardAutomatonBuild
variable {d : Nat}

structure Data where
  count : Nat
  start : List Bool
  step : List (List (List Bool))
  left : List (List Bool)
  right : List (List Bool)
  final : List Bool
  deriving BEq

def dimension (n m : Nat) : Nat × Nat :=
  let k := CountedSupportRule.add n m
  (k.1+3,3+k.2)
theorem dimension_value (n m : Nat) : (dimension n m).1 = n+m+3 := by
  simp only [dimension,CountedSupportRule.add_value]
theorem dimension_cost (n m : Nat) : (dimension n m).2 = n+4 := by
  simp only [dimension,CountedSupportRule.add_cost]; omega

def build (A B : StoredOrdinaryDFABuild.Data) : Data × Nat :=
  let k := dimension A.count B.count
  let e := dimension_value A.count B.count
  let s := CountedFinEnumeration.tabulate k.1 (fun q => StoredCapRowIndexed.start A B (Fin.cast e q))
  let t := tab3 k.1 d k.1 (fun q i r => StoredCapRowIndexed.step A B (Fin.cast e q) (Fin.cast e r) (.inl i))
  let l := tab2 k.1 k.1 (fun q r => StoredCapRowIndexed.step (d := d) A B (Fin.cast e q) (Fin.cast e r) (.inr false))
  let r := tab2 k.1 k.1 (fun q r => StoredCapRowIndexed.step (d := d) A B (Fin.cast e q) (Fin.cast e r) (.inr true))
  let f := CountedFinEnumeration.tabulate k.1 (fun q => StoredCapRowIndexed.final A B (Fin.cast e q))
  (⟨k.1,s.1,t.1,l.1,r.1,f.1⟩,1+k.2+s.2+t.2+l.2+r.2+f.2)

def budget (n m d : Nat) :=
  n+5+2*tabBudget (n+m+3) (2+StoredCapRowStates.decodeBudget n m)+
  tabBudget (n+m+3) (tabBudget d (tabBudget (n+m+3) (StoredCapRowIndexed.stepBudget n m d)))+
  2*tabBudget (n+m+3) (tabBudget (n+m+3) (StoredCapRowIndexed.stepBudget n m d))

theorem bound (A B : StoredOrdinaryDFABuild.Data) :
    (build (d := d) A B).2 ≤ budget A.count B.count d := by
  let k := dimension A.count B.count
  let e := dimension_value A.count B.count
  have hs := CountedFinEnumeration.tabulate_bound k.1
    (fun q => StoredCapRowIndexed.start A B (Fin.cast e q)) (2+StoredCapRowStates.decodeBudget A.count B.count)
    (fun q => StoredCapRowIndexed.start_bound A B (Fin.cast e q))
  have hf := CountedFinEnumeration.tabulate_bound k.1
    (fun q => StoredCapRowIndexed.final A B (Fin.cast e q)) (2+StoredCapRowStates.decodeBudget A.count B.count)
    (fun q => StoredCapRowIndexed.final_bound A B (Fin.cast e q))
  have ht := tab3_bound k.1 d k.1 (StoredCapRowIndexed.stepBudget A.count B.count d)
    (fun q i r => StoredCapRowIndexed.step A B (Fin.cast e q) (Fin.cast e r) (.inl i))
    (fun q i r => StoredCapRowIndexed.step_bound A B (Fin.cast e q) (Fin.cast e r) (.inl i))
  have hm (b : Bool) := tab2_bound k.1 k.1 (StoredCapRowIndexed.stepBudget A.count B.count d)
    (fun q r => StoredCapRowIndexed.step (d := d) A B (Fin.cast e q) (Fin.cast e r) (.inr b))
    (fun q r => StoredCapRowIndexed.step_bound (d := d) A B (Fin.cast e q) (Fin.cast e r) (.inr b))
  have hl := hm false
  have hr := hm true
  have hk : k.1 = A.count+B.count+3 := e
  conv_rhs at hs => rw [hk]
  conv_rhs at hf => rw [hk]
  conv_rhs at ht => rw [hk]
  conv_rhs at hl => rw [hk]
  conv_rhs at hr => rw [hk]
  dsimp only [k,e] at hs hf ht hl hr
  simp only [build,budget,dimension_cost]
  dsimp only [tabBudget] at *
  omega

def snapshot {n : Nat} (T : NSSE.NFA (Fin d ⊕ Bool) (Fin n)) [DecidablePred T.start]
    [DecidablePred T.accept] [∀ q x r, Decidable (T.step q x r)] : Data :=
  ⟨n,List.ofFn (fun q => decide (T.start q)),
    List.ofFn (fun q => List.ofFn (fun i => List.ofFn (fun r => decide (T.step q (.inl i) r)))),
    List.ofFn (fun q => List.ofFn (fun r => decide (T.step q (.inr false) r))),
    List.ofFn (fun q => List.ofFn (fun r => decide (T.step q (.inr true) r))),
    List.ofFn (fun q => decide (T.accept q))⟩

theorem value (A B : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (StoredOrdinaryDFABuild.snapshot A) (StoredOrdinaryDFABuild.snapshot B)).1 =
      snapshot (OriginalCapRow.finiteAutomaton A.automaton B.automaton) := by
  let T := OriginalCapRow.finiteAutomaton A.automaton B.automaton
  let e := (StoredCapRowStates.original_length A.count B.count).symm
  have hs (q : Fin (A.count+B.count+3)) :
      (StoredCapRowIndexed.start (StoredOrdinaryDFABuild.snapshot A) (StoredOrdinaryDFABuild.snapshot B) q).1 =
        decide (T.start (Fin.cast e q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredCapRowIndexed.start_value A B q
  have hf (q : Fin (A.count+B.count+3)) :
      (StoredCapRowIndexed.final (StoredOrdinaryDFABuild.snapshot A) (StoredOrdinaryDFABuild.snapshot B) q).1 =
        decide (T.accept (Fin.cast e q)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredCapRowIndexed.final_value A B q
  have ht (q r : Fin (A.count+B.count+3)) (x : Fin d ⊕ Bool) :
      (StoredCapRowIndexed.step (StoredOrdinaryDFABuild.snapshot A) (StoredOrdinaryDFABuild.snapshot B) q r x).1 =
        decide (T.step (Fin.cast e q) x (Fin.cast e r)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredCapRowIndexed.step_value A B q r x
  simp only [build,dimension_value,Fin.cast_refl,CountedFinEnumeration.tabulate_value,tab3_value,tab2_value,hs,hf,ht,snapshot]
  simp only [cast_back,Fin.cast_refl]
  congr 1
  · exact ofFn_cast e (fun q => decide (T.start q))
  · exact (ofFn_cast e (fun q => List.ofFn (fun i => List.ofFn
      (fun r => decide (T.step q (.inl i) (Fin.cast e r)))))).trans
      (congrArg List.ofFn (funext (fun q => congrArg List.ofFn (funext (fun i =>
        ofFn_cast e (fun r => decide (T.step q (.inl i) r)))))))
  · exact (ofFn_cast e (fun q => List.ofFn (fun r => decide (T.step q (.inr false) (Fin.cast e r))))).trans
      (congrArg List.ofFn (funext (fun q => ofFn_cast e (fun r => decide (T.step q (.inr false) r)))))
  · exact (ofFn_cast e (fun q => List.ofFn (fun r => decide (T.step q (.inr true) (Fin.cast e r))))).trans
      (congrArg List.ofFn (funext (fun q => ofFn_cast e (fun r => decide (T.step q (.inr true) r)))))
  · exact ofFn_cast e (fun q => decide (T.accept q))
end NSSE.StoredCapRowNFABuild
