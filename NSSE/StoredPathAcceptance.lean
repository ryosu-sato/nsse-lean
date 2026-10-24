import NSSE.StoredQueryOrdinaryDFA

namespace NSSE.StoredPathAcceptance
open StoredForwardAutomatonBuild StoredForwardLookup StoredForwardFinal
variable {d : Nat}

-- false selects anchor acceptance; true selects the root P-edge target.
def accept (A : Data) (root : Bool) (q : Fin A.count) (s : List Bool) : Bool × Nat :=
  if root then
    let r := existsFin A.count fun t =>
      let b := get false s t.val
      let p := StoredForwardAutomatonAccess.pedge A t q
      (b.1 && p.1,1+b.2+p.2)
    (r.1,1+r.2)
  else let r := get false s q.val; (r.1,1+r.2)

theorem anchor_value (A : Data) (q : Fin A.count) (s : List Bool) :
    (accept A false q s).1 = true ↔
      ∃ r, StoredForwardSubset.denote A.count s r = true ∧ r=q := by
  simp only [accept,Bool.false_eq_true,↓reduceIte,StoredForwardSubset.denote,exists_eq_right]

theorem root_value (A : Data) (h : A.start<A.count) (q : Fin A.count) (s : List Bool) :
    (accept A true q s).1 = true ↔
      ∃ r, StoredForwardSubset.denote A.count s r = true ∧
        (StoredForwardAutomatonAccess.input (d := d) A h).pedge r q := by
  simp only [accept,↓reduceIte,existsFin_value,Bool.and_eq_true,
    StoredForwardSubset.denote,StoredForwardAutomatonAccess.input]

def budget (k : Nat) := 1+StoredForwardTableBuild.tabBudget k (3*k+2)

theorem bound (A : Data) (root : Bool) (q : Fin A.count) (s : List Bool) :
    (accept A root q s).2 ≤ budget A.count := by
  have hb (t : Fin A.count) := (get_bound false s t.val).trans t.isLt
  have hp (t : Fin A.count) := StoredForwardAutomatonAccess.pedge_bound A t q
  have he := existsFin_bound A.count (3*A.count+2)
    (fun t => let b := get false s t.val
              let p := StoredForwardAutomatonAccess.pedge A t q
              (b.1 && p.1,1+b.2+p.2))
    (fun t => by dsimp only; have h1 := hb t; have h2 := hp t; omega)
  cases root
  · have h := hb q
    simp only [accept,Bool.false_eq_true,↓reduceIte,budget,StoredForwardTableBuild.tabBudget]
    nlinarith
  · simpa only [accept,↓reduceIte,budget] using Nat.add_le_add_left he 1

def indexed (A : Data) (root : Bool) (q : Fin A.count) (s : Fin (2^A.count)) : Bool × Nat :=
  let t := StoredIndexedSubset.decode A.count s
  let r := accept A root q t.1
  (r.1,1+t.2+r.2)

def indexedBudget (k : Nat) := 2+11*2^k+budget k

theorem indexed_bound (A : Data) (root : Bool) (q : Fin A.count) (s : Fin (2^A.count)) :
    (indexed A root q s).2 ≤ indexedBudget A.count := by
  have ht := StoredIndexedSubset.decode_bound A.count s
  have hr := bound A root q (StoredIndexedSubset.decode A.count s).1
  simp only [indexed,indexedBudget]; omega

def original (A : Data) (h : A.start<A.count) (root : Bool) (q : Fin A.count) :
    FiniteSOARankDecision.InputDFA (Fin d) :=
  ForwardCapNormalization.pathDFA (StoredForwardAutomatonAccess.input A h)
    (if root then q else ⟨A.start,h⟩)
    (fun r => if root then (StoredForwardAutomatonAccess.input (d := d) A h).pedge r q else r=q)

theorem indexed_value (A : Data) (h : A.start<A.count) (root : Bool) (q : Fin A.count)
    (s : Fin (2^A.count)) :
    (indexed A root q s).1 = true ↔ (original (d := d) A h root q).automaton.accept
      (Fin.cast (StoredIndexedSubset.masks_length A.count).symm s) := by
  cases root
  · simp only [indexed,anchor_value,StoredIndexedSubset.decode_value]
    rfl
  · simp only [indexed,root_value (d := d) A h,StoredIndexedSubset.decode_value]
    rfl
end NSSE.StoredPathAcceptance
