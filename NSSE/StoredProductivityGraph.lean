import NSSE.StoredDFAComplement

namespace NSSE.StoredProductivityGraph
open StoredOrdinaryDFABuild StoredForwardFinal StoredForwardTableBuild
variable {d : Nat}

def test (A : StoredOrdinaryDFABuild.Data) (q r : Fin A.count) (i : Fin d) : Bool × Nat :=
  let t := StoredDFAAccess.step A q i
  let e := FiniteValuationLookup.equalNat r.val t.1
  (e.1,1+t.2+e.2)

def edge (A : StoredOrdinaryDFABuild.Data) (q r : Fin A.count) : Bool × Nat :=
  existsFin d (test A q r)

theorem test_bound (A : StoredOrdinaryDFABuild.Data) (q r : Fin A.count) (i : Fin d) :
    (test A q r i).2 ≤ 2*A.count+d+2 := by
  have ht := StoredDFAAccess.step_bound A q i
  have he := (FiniteValuationLookup.equalNat_bound r.val (StoredDFAAccess.step A q i).1).trans r.isLt
  simp only [test]; omega

theorem edge_bound (A : StoredOrdinaryDFABuild.Data) (q r : Fin A.count) :
    (edge (d := d) A q r).2 ≤ tabBudget d (2*A.count+d+2) :=
  existsFin_bound d _ _ (test_bound A q r)

theorem edge_value (D : FiniteSOARankDecision.InputDFA (Fin d)) (q r : Fin D.count) :
    (edge (d := d) (snapshot D) q r).1 = true ↔ D.automaton.productivityGame.edge q.val r.val = true := by
  rw [DFA.productivityGame_edge_iff]
  simp only [edge,existsFin_value,test,FiniteValuationLookup.equalNat_correct,StoredDFAAccess.step_snapshot]
  simp only [Fin.ext_iff,eq_comm]

structure Data where
  count : Nat
  accepting : List Bool
  edge : List (List Bool)
  deriving BEq

def build (A : StoredOrdinaryDFABuild.Data) : Data × Nat :=
  let e := tab2 A.count A.count (edge (d := d) A)
  let f := CountedFinEnumeration.tabulate A.count (StoredDFAAccess.final A)
  (⟨A.count,f.1,e.1⟩,1+e.2+f.2)

def budget (k d : Nat) := 1+tabBudget k (tabBudget k (tabBudget d (2*k+d+2)))+tabBudget k k

theorem bound (A : StoredOrdinaryDFABuild.Data) : (build (d := d) A).2 ≤ budget A.count d := by
  have he := tab2_bound A.count A.count (tabBudget d (2*A.count+d+2))
    (edge (d := d) A) (edge_bound A)
  have hf := CountedFinEnumeration.tabulate_bound A.count (StoredDFAAccess.final A) A.count
    (StoredDFAAccess.final_bound A)
  simp only [build,budget]
  dsimp only [tabBudget] at *
  omega

def snapshotGame (G : FiniteReachabilityGame) : Data :=
  ⟨G.stateCount,List.ofFn (fun q : Fin G.stateCount => G.accepting q.val),
    List.ofFn (fun q : Fin G.stateCount => List.ofFn (fun r : Fin G.stateCount => G.edge q.val r.val))⟩

theorem value (D : FiniteSOARankDecision.InputDFA (Fin d)) :
    (build (d := d) (snapshot D)).1 = snapshotGame D.automaton.productivityGame := by
  have he (q r : Fin D.count) : (edge (d := d) (snapshot D) q r).1 = D.automaton.productivityGame.edge q.val r.val :=
    Bool.eq_iff_iff.mpr (edge_value D q r)
  have hf (q : Fin D.count) : (StoredDFAAccess.final (snapshot D) q).1 =
      D.automaton.productivityGame.accepting q.val := by
    apply Bool.eq_iff_iff.mpr
    rw [StoredDFAAccess.final_snapshot,DFA.productivityGame_accepting]
  simp only [build,tab2_value,CountedFinEnumeration.tabulate_value,he,hf,snapshotGame]
  rfl
end NSSE.StoredProductivityGraph
