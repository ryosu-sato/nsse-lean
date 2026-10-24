import NSSE.StoredRightIdealNFABuild

namespace NSSE.StoredNFASubset
open StoredRightIdealNFABuild StoredForwardLookup
variable {d n : Nat}

-- Reuse step/final storage only; this adapter does not select an NFA start.
def forward (A : Data) : StoredForwardAutomatonBuild.Data :=
  ⟨A.count,0,A.step,A.final,[]⟩

def advance (A : Data) (s : List Bool) (i : Fin d) : List Bool × Nat :=
  let r := StoredForwardSubset.advance (forward A) s i
  (r.1,1+r.2)

def accept (A : Data) (s : List Bool) : Bool × Nat :=
  let r := StoredForwardSubset.accept (forward A) s
  (r.1,1+r.2)

def initial (A : Data) : List Bool × Nat :=
  CountedFinEnumeration.tabulate A.count (fun q => get false A.start q.val)

theorem advance_bound (A : Data) (s : List Bool) (i : Fin d) :
    (advance A s i).2 ≤ 1+StoredForwardSubset.advanceBudget A.count d :=
  Nat.add_le_add_left (StoredForwardSubset.advance_bound (forward A) s i) 1

theorem accept_bound (A : Data) (s : List Bool) :
    (accept A s).2 ≤ 1+StoredForwardTableBuild.tabBudget A.count (2*A.count+1) :=
  Nat.add_le_add_left (StoredForwardSubset.accept_bound (forward A) s) 1

theorem initial_bound (A : Data) :
    (initial A).2 ≤ StoredForwardTableBuild.tabBudget A.count A.count :=
  CountedFinEnumeration.tabulate_bound _ _ _ (fun q => (get_bound false A.start q.val).trans q.isLt)

theorem advance_length (A : Data) (s : List Bool) (i : Fin d) :
    (advance A s i).1.length = A.count := StoredForwardSubset.advance_length (forward A) s i

theorem initial_length (A : Data) : (initial A).1.length = A.count := by
  simp only [initial,CountedFinEnumeration.tabulate_value,List.length_ofFn]

variable (T : NSSE.NFA (Fin d) (Fin n)) [DecidablePred T.start]
  [DecidablePred T.accept] [∀ q i r, Decidable (T.step q i r)]

theorem initial_value : StoredForwardSubset.denote n (initial (snapshot T)).1 =
    (FiniteDFAOperations.maskDFA T).start := by
  funext q
  simp only [initial,CountedFinEnumeration.tabulate_value,StoredForwardSubset.denote,
    snapshot,get_ofFn,FiniteDFAOperations.maskDFA]

theorem advance_value (s : List Bool) (i : Fin d) :
    StoredForwardSubset.denote n (advance (snapshot T) s i).1 =
      (FiniteDFAOperations.maskDFA T).step (StoredForwardSubset.denote n s) i := by
  funext r
  apply Bool.eq_iff_iff.mpr
  simp only [advance,StoredForwardSubset.advance,CountedFinEnumeration.tabulate_value,
    StoredForwardSubset.denote,get_ofFn,StoredForwardSubset.cell,StoredForwardFinal.existsFin_value,
    Bool.and_eq_true,StoredForwardAutomatonAccess.step,forward,snapshot,three_ofFn,
    decide_eq_true_eq,FiniteDFAOperations.maskDFA]

theorem accept_value (s : List Bool) : (accept (snapshot T) s).1 = true ↔
    (FiniteDFAOperations.maskDFA T).accept (StoredForwardSubset.denote n s) := by
  simp only [accept,StoredForwardSubset.accept,StoredForwardFinal.existsFin_value,Bool.and_eq_true,
    StoredForwardAutomatonAccess.final,forward,snapshot,get_ofFn,decide_eq_true_eq,
    FiniteDFAOperations.maskDFA,StoredForwardSubset.denote]
end NSSE.StoredNFASubset
