import NSSE.StoredNFASubset

namespace NSSE.StoredNFAIndexed
open StoredRightIdealNFABuild
variable {d n : Nat}

def step (A : Data) (q : Fin (2^A.count)) (i : Fin d) : Fin (2^A.count) × Nat :=
  let s := StoredIndexedSubset.decode A.count q
  let t := StoredNFASubset.advance A s.1 i
  let r := StoredSubsetIndex.encode A.count t.1 (StoredNFASubset.advance_length A s.1 i)
  (r.1,2+s.2+t.2+r.2)

def initial (A : Data) : Fin (2^A.count) × Nat :=
  let s := StoredNFASubset.initial A
  let r := StoredSubsetIndex.encode A.count s.1 (StoredNFASubset.initial_length A)
  (r.1,1+s.2+r.2)

def accept (A : Data) (q : Fin (2^A.count)) : Bool × Nat :=
  let s := StoredIndexedSubset.decode A.count q
  let r := StoredNFASubset.accept A s.1
  (r.1,1+s.2+r.2)

def stepBudget (n d : Nat) := 4+11*2^n+StoredForwardSubset.advanceBudget n d+StoredSubsetIndex.budget n

def initialBudget (n : Nat) := 1+StoredForwardTableBuild.tabBudget n n+StoredSubsetIndex.budget n

def acceptBudget (n : Nat) := 3+11*2^n+StoredForwardTableBuild.tabBudget n (2*n+1)

theorem step_bound (A : Data) (q : Fin (2^A.count)) (i : Fin d) :
    (step A q i).2 ≤ stepBudget A.count d := by
  have hs := StoredIndexedSubset.decode_bound A.count q
  have ht := StoredNFASubset.advance_bound A (StoredIndexedSubset.decode A.count q).1 i
  have hr := StoredSubsetIndex.encode_bound A.count _ (StoredNFASubset.advance_length A (StoredIndexedSubset.decode A.count q).1 i)
  simp only [step,stepBudget]; omega

theorem initial_bound (A : Data) : (initial A).2 ≤ initialBudget A.count := by
  have hs := StoredNFASubset.initial_bound A
  have hr := StoredSubsetIndex.encode_bound A.count _ (StoredNFASubset.initial_length A)
  simp only [initial,initialBudget]; omega

theorem accept_bound (A : Data) (q : Fin (2^A.count)) : (accept A q).2 ≤ acceptBudget A.count := by
  have hs := StoredIndexedSubset.decode_bound A.count q
  have hr := StoredNFASubset.accept_bound A (StoredIndexedSubset.decode A.count q).1
  simp only [accept,acceptBudget]; omega

variable (T : NSSE.NFA (Fin d) (Fin n)) [DecidablePred T.start]
  [DecidablePred T.accept] [∀ q i r, Decidable (T.step q i r)]

theorem initial_value : (initial (snapshot T)).1.val =
    (FiniteDFAOperations.determinize T).automaton.start.val := by
  simp only [initial,StoredSubsetIndex.original_index,StoredNFASubset.initial_value]
  rfl

theorem step_value (q : Fin (2^n)) (i : Fin d) : (step (snapshot T) q i).1.val =
    ((FiniteDFAOperations.determinize T).automaton.step
      (Fin.cast (StoredIndexedSubset.masks_length n).symm q) i).val := by
  simp only [step,StoredSubsetIndex.original_index,StoredNFASubset.advance_value,StoredIndexedSubset.decode_value]
  rfl

theorem accept_value (q : Fin (2^n)) : (accept (snapshot T) q).1 = true ↔
    (FiniteDFAOperations.determinize T).automaton.accept
      (Fin.cast (StoredIndexedSubset.masks_length n).symm q) := by
  simp only [accept,StoredNFASubset.accept_value]
  change (FiniteDFAOperations.maskDFA T).accept
    (StoredForwardSubset.denote n (StoredIndexedSubset.decode n q).1) ↔ _
  rw [StoredIndexedSubset.decode_value]
  rfl
end NSSE.StoredNFAIndexed
