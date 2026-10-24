import NSSE.StoredQueryForwardInput

namespace NSSE.StoredForwardSubset
open StoredForwardAutomatonBuild StoredForwardLookup StoredForwardFinal
variable {d : Nat}

-- A semantic view of an executable Boolean list.
def denote (k : Nat) (s : List Bool) : SymbolicComplement.Mask k :=
  fun q => (get false s q.val).1

def cell (A : Data) (s : List Bool) (i : Fin d) (r : Fin A.count) : Bool × Nat :=
  existsFin A.count fun q =>
    let b := get false s q.val
    let t := StoredForwardAutomatonAccess.step A q i r
    (b.1 && t.1,1+b.2+t.2)

def advance (A : Data) (s : List Bool) (i : Fin d) : List Bool × Nat :=
  CountedFinEnumeration.tabulate A.count (cell A s i)

theorem cell_value (A : Data) (h : A.start < A.count) (s : List Bool)
    (i : Fin d) (r : Fin A.count) :
    (cell A s i r).1 = true ↔ ∃ q, denote A.count s q = true ∧
      (StoredForwardAutomatonAccess.input A h).step q i r := by
  simp only [cell,existsFin_value,Bool.and_eq_true,denote,StoredForwardAutomatonAccess.input]

theorem cell_bound (A : Data) (s : List Bool) (i : Fin d) (r : Fin A.count) :
    (cell A s i r).2 ≤ StoredForwardTableBuild.tabBudget A.count (3*A.count+d+3) := by
  apply existsFin_bound
  intro q
  have hb := (get_bound false s q.val).trans q.isLt
  have ht := StoredForwardAutomatonAccess.step_bound A q r i
  dsimp only
  omega

theorem advance_value (A : Data) (h : A.start < A.count) (s : List Bool) (i : Fin d) :
    denote A.count (advance A s i).1 =
      (FiniteDFAOperations.maskDFA (ForwardCapAutomaton.pathNFA
        (StoredForwardAutomatonAccess.input A h) ⟨A.start,h⟩
        (StoredForwardAutomatonAccess.input A h).final)).step (denote A.count s) i := by
  funext r
  apply Bool.eq_iff_iff.mpr
  simp only [advance,CountedFinEnumeration.tabulate_value,denote,get_ofFn]
  exact (cell_value A h s i r).trans (by simp only [FiniteDFAOperations.maskDFA,
    ForwardCapAutomaton.ordinary,ForwardCapAutomaton.pathNFA,decide_eq_true_eq]; rfl)

theorem advance_length (A : Data) (s : List Bool) (i : Fin d) :
    (advance A s i).1.length = A.count := by
  simp only [advance,CountedFinEnumeration.tabulate_value,List.length_ofFn]

def advanceBudget (k d : Nat) := StoredForwardTableBuild.tabBudget k
  (StoredForwardTableBuild.tabBudget k (3*k+d+3))

theorem advance_bound (A : Data) (s : List Bool) (i : Fin d) :
    (advance A s i).2 ≤ advanceBudget A.count d :=
  CountedFinEnumeration.tabulate_bound _ _ _ (cell_bound A s i)

def accept (A : Data) (s : List Bool) : Bool × Nat :=
  existsFin A.count fun q =>
    let b := get false s q.val
    let f := StoredForwardAutomatonAccess.final A q
    (b.1 && f.1,1+b.2+f.2)

theorem accept_value (A : Data) (h : A.start < A.count) (s : List Bool) :
    (accept A s).1 = true ↔
      (FiniteDFAOperations.maskDFA (ForwardCapAutomaton.pathNFA
        (StoredForwardAutomatonAccess.input (d := d) A h) ⟨A.start,h⟩
        (StoredForwardAutomatonAccess.input (d := d) A h).final)).accept (denote A.count s) := by
  simp only [accept,existsFin_value,Bool.and_eq_true,denote,
    FiniteDFAOperations.maskDFA,ForwardCapAutomaton.ordinary,ForwardCapAutomaton.pathNFA,
    StoredForwardAutomatonAccess.input]

theorem accept_bound (A : Data) (s : List Bool) :
    (accept A s).2 ≤ StoredForwardTableBuild.tabBudget A.count (2*A.count+1) := by
  apply existsFin_bound
  intro q
  have hb := (get_bound false s q.val).trans q.isLt
  have hf := StoredForwardAutomatonAccess.final_bound A q
  dsimp only
  omega
def initial (k : Nat) (q : Fin k) : List Bool × Nat :=
  CountedFinEnumeration.tabulate k (fun r => StoredForwardPedge.equal r q)

theorem initial_value (k : Nat) (q : Fin k) :
    denote k (initial k q).1 = fun r => decide (r = q) := by
  funext r
  apply Bool.eq_iff_iff.mpr
  simp only [denote,initial,CountedFinEnumeration.tabulate_value,get_ofFn,
    StoredForwardPedge.equal_value,decide_eq_true_eq]

theorem initial_length (k : Nat) (q : Fin k) : (initial k q).1.length = k := by
  simp only [initial,CountedFinEnumeration.tabulate_value,List.length_ofFn]

theorem initial_bound (k : Nat) (q : Fin k) :
    (initial k q).2 ≤ StoredForwardTableBuild.tabBudget k (k+1) :=
  CountedFinEnumeration.tabulate_bound _ _ _ (fun r => StoredForwardPedge.equal_bound r q)
end NSSE.StoredForwardSubset
