import NSSE.StoredIndexedForward

namespace NSSE.StoredForwardAutomatonBuild
open StoredIndexedForward StoredForwardTableBuild
variable {n d : Nat}

structure Data where
  count : Nat
  start : Nat
  step : List (List (List Bool))
  final : List Bool
  pedge : List (List Bool)
  deriving BEq

def dimension (n : Nat) : Nat × Nat :=
  let r := CountedSupportRule.mul (n+1) (n+1)
  (r.1+1,3+r.2)
theorem dimension_value (n : Nat) : (dimension n).1 = (n+1)*(n+1)+1 := by
  simp only [dimension,CountedSupportRule.mul_value]
theorem dimension_cost (n : Nat) : (dimension n).2 = 4+(n+1)*(n+3) := by
  simp only [dimension,CountedSupportRule.mul_cost]; ring

def build (D : StoredForwardTableBuild.Data n) (side : ForwardTableAutomaton.Side) : Data × Nat :=
  let k := dimension n
  let s := StoredIndexedForward.start D
  let t := tab3 k.1 d k.1 (fun q i r => StoredIndexedForward.step D
    (Fin.cast (dimension_value n) q) i (Fin.cast (dimension_value n) r))
  let f := CountedFinEnumeration.tabulate k.1 (fun q => StoredIndexedForward.final (d := d) D side
    (Fin.cast (dimension_value n) q))
  let p := tab2 k.1 k.1 (fun q r => StoredIndexedForward.pedge side
    (Fin.cast (dimension_value n) q) (Fin.cast (dimension_value n) r))
  (⟨k.1,s.1.val,t.1,f.1,p.1⟩,1+k.2+s.2+t.2+f.2+p.2)

def budget (n d : Nat) :=
  let k := (n+1)*(n+1)+1
  1+(4+(n+1)*(n+3))+(n*(n+3)+n+9)+
    tabBudget k (tabBudget d (tabBudget k (stepBudget n d)))+
    tabBudget k (finalBudget n d)+tabBudget k (tabBudget k (pedgeBudget n))

theorem bound (D : StoredForwardTableBuild.Data n) (side : ForwardTableAutomaton.Side) :
    (build (d := d) D side).2 ≤ budget n d := by
  have hs := StoredIndexedForward.start_bound D
  have ht := tab3_bound (dimension n).1 d (dimension n).1 (stepBudget n d)
    (fun q i r => StoredIndexedForward.step D (Fin.cast (dimension_value n) q) i (Fin.cast (dimension_value n) r))
    (fun q i r => StoredIndexedForward.step_bound D _ _ i)
  have hf := CountedFinEnumeration.tabulate_bound (dimension n).1
    (fun q => StoredIndexedForward.final (d := d) D side (Fin.cast (dimension_value n) q))
    (finalBudget n d) (fun q => StoredIndexedForward.final_bound D side _)
  have hp := tab2_bound (dimension n).1 (dimension n).1 (pedgeBudget n)
    (fun q r => StoredIndexedForward.pedge side (Fin.cast (dimension_value n) q) (Fin.cast (dimension_value n) r))
    (fun q r => StoredIndexedForward.pedge_bound side _ _)
  simp only [build,budget,dimension_cost]
  simp only [dimension_value] at ht hf hp
  dsimp only [tabBudget] at *
  omega

-- Transport only proof indices; the actual builder uses its computed dimension.
theorem ofFn_cast {a b : Nat} {α : Type*} (h : a=b) (f : Fin b → α) :
    List.ofFn (fun i => f (Fin.cast h i)) = List.ofFn f := by subst b; rfl

theorem cast_back {a b : Nat} (h : a=b) (k : b=a) (i : Fin b) :
    Fin.cast h (Fin.cast k i) = i := Fin.ext rfl

def snapshot (A : ForwardCapAutomaton.Input (Fin d)) : Data :=
  ⟨A.count,A.start.val,List.ofFn (fun q => List.ofFn (fun i => List.ofFn (fun r => decide (A.step q i r)))),
    List.ofFn (fun q => decide (A.final q)),List.ofFn (fun q => List.ofFn (fun r => decide (A.pedge q r)))⟩

theorem value (D : StoredForwardTableBuild.Data n) (side : ForwardTableAutomaton.Side) :
    (build (d := d) D side).1 = snapshot (ForwardTableAutomaton.compile (StoredForwardLookup.denote (d := d) D) side) := by
  have ht (q r : Index n) (i : Fin d) : (StoredIndexedForward.step D q i r).1 =
      decide ((ForwardTableAutomaton.compile (StoredForwardLookup.denote D) side).step q i r) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredIndexedForward.step_value D side q r i
  have hf (q : Index n) : (StoredIndexedForward.final (d := d) D side q).1 =
      decide ((ForwardTableAutomaton.compile (StoredForwardLookup.denote (d := d) D) side).final q) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,StoredIndexedForward.final_value]
  have hp (q r : Index n) : (StoredIndexedForward.pedge side q r).1 =
      decide ((ForwardTableAutomaton.compile (StoredForwardLookup.denote (d := d) D) side).pedge q r) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact StoredIndexedForward.pedge_value (d := d) D side q r
  simp only [build,tab3_value,tab2_value,CountedFinEnumeration.tabulate_value,
    ht,hf,hp,ofFn_cast,StoredIndexedForward.start_value (d := d) D side,snapshot,dimension_value]
  simp only [cast_back,Fin.cast_refl]
  rfl
end NSSE.StoredForwardAutomatonBuild
