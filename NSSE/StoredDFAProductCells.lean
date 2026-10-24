import NSSE.StoredProductTable

namespace NSSE.StoredDFAProductCells
variable {d : Nat}

structure Valid (A : StoredOrdinaryDFABuild.Data) : Prop where
  start : A.start < A.count
  step : ∀ (q : Fin A.count) (i : Fin d), (StoredDFAAccess.step A q i).1 < A.count

theorem valid_snapshot (A : FiniteSOARankDecision.InputDFA (Fin d)) :
    Valid (d := d) (StoredOrdinaryDFABuild.snapshot A) :=
  ⟨A.automaton.start.isLt,StoredDFAAccess.step_snapshot_lt A⟩

def encode (m x y : Nat) : Nat × Nat :=
  let r := CountedSupportRule.mul m x
  let s := CountedSupportRule.add y r.1
  (s.1,1+r.2+s.2)

theorem encode_value (m x y : Nat) : (encode m x y).1 = y+m*x := by
  simp only [encode,CountedSupportRule.mul_value,CountedSupportRule.add_value]

def encodeBudget (n m : Nat) := 3+n*(m+2)+m

theorem encode_bound (n m x y : Nat) (hx : x<n) (hy : y<m) :
    (encode m x y).2 ≤ encodeBudget n m := by
  have h := Nat.mul_le_mul_right (m+2) (Nat.le_of_lt hx)
  simp only [encode,encodeBudget,CountedSupportRule.mul_cost,CountedSupportRule.add_cost]
  omega

def step (A B : StoredOrdinaryDFABuild.Data) (q : Fin A.count) (r : Fin B.count) (i : Fin d) : Nat × Nat :=
  let a := StoredDFAAccess.step A q i
  let b := StoredDFAAccess.step B r i
  let e := encode B.count a.1 b.1
  (e.1,2+a.2+b.2+e.2)

def stepBudget (n m d : Nat) := 4+n+m+2*d+encodeBudget n m

theorem step_bound (A B : StoredOrdinaryDFABuild.Data) (ha : Valid (d := d) A)
    (hb : Valid (d := d) B) (q : Fin A.count) (r : Fin B.count) (i : Fin d) :
    (step A B q r i).2 ≤ stepBudget A.count B.count d := by
  have h1 := StoredDFAAccess.step_bound A q i
  have h2 := StoredDFAAccess.step_bound B r i
  have h3 := encode_bound A.count B.count _ _ (ha.step q i) (hb.step r i)
  simp only [step,stepBudget]; omega

def final (A B : StoredOrdinaryDFABuild.Data) (f : Bool → Bool → Bool)
    (q : Fin A.count) (r : Fin B.count) : Bool × Nat :=
  let a := StoredDFAAccess.final A q
  let b := StoredDFAAccess.final B r
  (f a.1 b.1,1+a.2+b.2)

theorem final_bound (A B : StoredOrdinaryDFABuild.Data) (f : Bool → Bool → Bool)
    (q : Fin A.count) (r : Fin B.count) : (final A B f q r).2 ≤ 1+A.count+B.count := by
  have h1 := StoredDFAAccess.final_bound A q
  have h2 := StoredDFAAccess.final_bound B r
  simp only [final]; omega

theorem step_value (A B : FiniteSOARankDecision.InputDFA (Fin d))
    (q : Fin A.count) (r : Fin B.count) (i : Fin d) :
    (step (StoredOrdinaryDFABuild.snapshot A) (StoredOrdinaryDFABuild.snapshot B) q r i).1 =
      (finProdFinEquiv (A.automaton.step q i,B.automaton.step r i)).val := by
  simp only [step,encode_value,StoredDFAAccess.step_snapshot]
  rfl

theorem final_value (A B : FiniteSOARankDecision.InputDFA (Fin d)) (f : Bool → Bool → Bool)
    (q : Fin A.count) (r : Fin B.count) :
    (final (StoredOrdinaryDFABuild.snapshot A) (StoredOrdinaryDFABuild.snapshot B) f q r).1 =
      f (decide (A.automaton.accept q)) (decide (B.automaton.accept r)) := by
  simp only [final,StoredDFAAccess.final,StoredOrdinaryDFABuild.snapshot,StoredForwardLookup.get_ofFn]
end NSSE.StoredDFAProductCells
