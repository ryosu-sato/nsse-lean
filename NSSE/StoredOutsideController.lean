import NSSE.StoredOutsideGuards

/-! Actual materialization of one outside-controller firing row of the next
rank, in the unified block language, with counted table reads and label
production.  This is the row side of the next-rank recursion; the candidate
side is `StoredNextCandidate`. -/
namespace NSSE.StoredOutsideController
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
open SymbolicGuardedBlocks SymbolicOutsideController GuardedRowFiring
open StoredEmptyTailCompiler (matrix matrix_read matrix_bound matrixBudget vectorBudget)
variable {k c : Nat} (ns : Fin k → Nat) (i : Fin k)

abbrev Table (ns : Fin k → Nat) (i : Fin k) := StoredOutsideStates.Table (ns i)

def initial (S : Table ns i) (e : Ends (ns i)) (first : Bool) (j : Fin S.count) :
    QF (UnifiedBlockPresentation.Rel ns c) Empty × Nat :=
  let q := StoredOutsideStates.read S j
  let a := StoredOutsideGuards.initial ns (c := c) i q.1
  (⟨a.1,StoredOutsideGuards.initial_qf ns i e first q.1⟩,2+q.2+a.2)
def final (S : Table ns i) (e : Ends (ns i)) (first : Bool) (j : Fin S.count) :
    QF (UnifiedBlockPresentation.Rel ns c) Empty × Nat :=
  let q := StoredOutsideStates.read S j
  let a := StoredOutsideGuards.final ns (c := c) i q.1
  (⟨a.1,StoredOutsideGuards.final_qf ns i e first q.1⟩,2+q.2+a.2)
def data (S : Table ns i) (e : Ends (ns i)) (first : Bool) (j l : Fin S.count) :
    QF (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) × Nat :=
  let q := StoredOutsideStates.read S j
  let r := StoredOutsideStates.read S l
  let a := StoredOutsideGuards.data ns (c := c) i e first q.1 r.1
  (⟨a.1,StoredOutsideGuards.data_qf ns i e first q.1 r.1⟩,3+q.2+r.2+a.2)
def left (S : Table ns i) (e : Ends (ns i)) (first : Bool) (j l : Fin S.count) :
    QF (UnifiedBlockPresentation.Rel ns c) Empty × Nat :=
  let q := StoredOutsideStates.read S j
  let r := StoredOutsideStates.read S l
  let a := StoredOutsideGuards.left ns (c := c) i e q.1 r.1
  (⟨a.1,StoredOutsideGuards.left_qf ns i e first q.1 r.1⟩,3+q.2+r.2+a.2)
def right (S : Table ns i) (e : Ends (ns i)) (first : Bool) (j l : Fin S.count) :
    QF (UnifiedBlockPresentation.Rel ns c) Empty × Nat :=
  let q := StoredOutsideStates.read S j
  let r := StoredOutsideStates.read S l
  let a := StoredOutsideGuards.right ns (c := c) i e q.1 r.1
  (⟨a.1,StoredOutsideGuards.right_qf ns i e first q.1 r.1⟩,3+q.2+r.2+a.2)

def labels (S : Table ns i) (e : Ends (ns i)) (first : Bool) :
    Row (UnifiedBlockPresentation.Rel ns c) Empty S.count × Nat :=
  let a := StoredRelationTuple.tabulate (initial ns i S e first)
  let b := StoredRelationTuple.tabulate (final ns i S e first)
  let d := matrix S.count (data ns i S e first)
  let l := matrix S.count (left ns i S e first)
  let r := matrix S.count (right ns i S e first)
  (⟨a.1,b.1,d.1,l.1,r.1,⟨StoredOutsideGuards.guardAtom ns (c := c) i e first,
      StoredOutsideGuards.guard_qf ns i e first⟩⟩,8+a.2+b.2+d.2+l.2+r.2)

/-- The stored row denotes exactly the transported outside controller, up to
the state-count cast. -/
theorem value (S : Table ns i) (e : Ends (ns i)) (first : Bool) :
    (labels ns i (c := c) S e first).1.original =
      { initial := fun j =>
          (UnifiedBlockPresentation.compileRow ns c i e first).initial (Fin.cast S.count_eq j)
        final := fun j =>
          (UnifiedBlockPresentation.compileRow ns c i e first).final (Fin.cast S.count_eq j)
        data := fun j l =>
          (UnifiedBlockPresentation.compileRow ns c i e first).data
            (Fin.cast S.count_eq j) (Fin.cast S.count_eq l)
        left := fun j l =>
          (UnifiedBlockPresentation.compileRow ns c i e first).left
            (Fin.cast S.count_eq j) (Fin.cast S.count_eq l)
        right := fun j l =>
          (UnifiedBlockPresentation.compileRow ns c i e first).right
            (Fin.cast S.count_eq j) (Fin.cast S.count_eq l)
        guard := (UnifiedBlockPresentation.compileRow ns c i e first).guard } := by
  unfold Row.original labels
  simp only [StoredRelationTuple.tabulate_read,matrix_read,initial,final,data,left,right,
    StoredOutsideGuards.initial_value,StoredOutsideGuards.final_value,
    StoredOutsideGuards.data_value,StoredOutsideGuards.left_value,
    StoredOutsideGuards.right_value,StoredOutsideGuards.guardAtom_value,
    StoredOutsideStates.read_value,UnifiedBlockPresentation.compileRow,
    RowLanguageTransport.mapRow,SymbolicOutsideController.compile]

def vertexCost (n : Nat) := 2+(4*n+2)+StoredOutsideGuards.budget
def edgeCost (n : Nat) := 3+2*(4*n+2)+StoredOutsideGuards.budget
def labelBudget (n : Nat) :=
  8+2*vectorBudget (4*n+2) (vertexCost n)+3*matrixBudget (4*n+2) (edgeCost n)

theorem labels_bound (S : Table ns i) (e : Ends (ns i)) (first : Bool) :
    (labels ns i (c := c) S e first).2 ≤ labelBudget (ns i) := by
  have hi (j : Fin S.count) : (initial ns i (c := c) S e first j).2 ≤ vertexCost (ns i) := by
    have hq := StoredOutsideStates.read_bound S j
    have ha := StoredOutsideGuards.initial_bound ns (c := c) i (StoredOutsideStates.read S j).1
    simp only [initial,vertexCost]; omega
  have hf (j : Fin S.count) : (final ns i (c := c) S e first j).2 ≤ vertexCost (ns i) := by
    have hq := StoredOutsideStates.read_bound S j
    have ha := StoredOutsideGuards.final_bound ns (c := c) i (StoredOutsideStates.read S j).1
    simp only [final,vertexCost]; omega
  have hd (j l : Fin S.count) : (data ns i (c := c) S e first j l).2 ≤ edgeCost (ns i) := by
    have hq := StoredOutsideStates.read_bound S j
    have hr := StoredOutsideStates.read_bound S l
    have ha := StoredOutsideGuards.data_bound ns (c := c) i e first
      (StoredOutsideStates.read S j).1 (StoredOutsideStates.read S l).1
    simp only [data,edgeCost]; omega
  have hl (j l : Fin S.count) : (left ns i (c := c) S e first j l).2 ≤ edgeCost (ns i) := by
    have hq := StoredOutsideStates.read_bound S j
    have hr := StoredOutsideStates.read_bound S l
    have ha := StoredOutsideGuards.left_bound ns (c := c) i e
      (StoredOutsideStates.read S j).1 (StoredOutsideStates.read S l).1
    simp only [left,edgeCost]; omega
  have hr (j l : Fin S.count) : (right ns i (c := c) S e first j l).2 ≤ edgeCost (ns i) := by
    have hq := StoredOutsideStates.read_bound S j
    have hs := StoredOutsideStates.read_bound S l
    have ha := StoredOutsideGuards.right_bound ns (c := c) i e
      (StoredOutsideStates.read S j).1 (StoredOutsideStates.read S l).1
    simp only [right,edgeCost]; omega
  have ha := StoredRelationTuple.tabulate_bound _ _ hi
  have hb := StoredRelationTuple.tabulate_bound _ _ hf
  have hc := matrix_bound S.count (data ns i (c := c) S e first) _ hd
  have hm := matrix_bound S.count (left ns i (c := c) S e first) _ hl
  have hn := matrix_bound S.count (right ns i (c := c) S e first) _ hr
  conv at ha => rhs; rw [StoredOutsideStates.count_value S]
  conv at hb => rhs; rw [StoredOutsideStates.count_value S]
  conv at hc => rhs; rw [StoredOutsideStates.count_value S]
  conv at hm => rhs; rw [StoredOutsideStates.count_value S]
  conv at hn => rhs; rw [StoredOutsideStates.count_value S]
  simp only [labels,labelBudget,vectorBudget] at *; omega

theorem labels_shape (S : Table ns i) (e : Ends (ns i)) (first : Bool) :
    StoredRowTransport.Bounds (labels ns i (c := c) S e first).1 StoredOutsideGuards.sizeBudget 2 := by
  constructor
  · constructor
    · intro q r
      simpa only [labels,matrix_read,data] using (StoredOutsideGuards.data_shape ns i e first
        (StoredOutsideStates.read S q).1 (StoredOutsideStates.read S r).1).1
    · intro q r
      simpa only [labels,matrix_read,left] using (StoredOutsideGuards.left_shape ns i e
        (StoredOutsideStates.read S q).1 (StoredOutsideStates.read S r).1).1
    · intro q r
      simpa only [labels,matrix_read,right] using (StoredOutsideGuards.right_shape ns i e
        (StoredOutsideStates.read S q).1 (StoredOutsideStates.read S r).1).1
    · exact (StoredOutsideGuards.guardAtom_shape ns i e first).1
    · intro q r
      simpa only [labels,matrix_read,data] using (StoredOutsideGuards.data_shape ns i e first
        (StoredOutsideStates.read S q).1 (StoredOutsideStates.read S r).1).2
    · intro q r
      simpa only [labels,matrix_read,left] using (StoredOutsideGuards.left_shape ns i e
        (StoredOutsideStates.read S q).1 (StoredOutsideStates.read S r).1).2
    · intro q r
      simpa only [labels,matrix_read,right] using (StoredOutsideGuards.right_shape ns i e
        (StoredOutsideStates.read S q).1 (StoredOutsideStates.read S r).1).2
    · exact (StoredOutsideGuards.guardAtom_shape ns i e first).2
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,initial] using
      (StoredOutsideGuards.initial_shape ns i (StoredOutsideStates.read S q).1).1
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,final] using
      (StoredOutsideGuards.final_shape ns i (StoredOutsideStates.read S q).1).1
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,initial] using
      (StoredOutsideGuards.initial_shape ns i (StoredOutsideStates.read S q).1).2
  · intro q
    simpa only [labels,StoredRelationTuple.tabulate_read,final] using
      (StoredOutsideGuards.final_shape ns i (StoredOutsideStates.read S q).1).2

structure Result (ns : Fin k → Nat) (c : Nat) (i : Fin k) where
  states : Table ns i
  row : Row (UnifiedBlockPresentation.Rel ns c) Empty states.count

def build (e : Ends (ns i)) (first : Bool) : Result ns c i × Nat :=
  let s := StoredOutsideStates.build (ns i)
  let a := labels ns i (c := c) s.1 e first
  (⟨s.1,a.1⟩,2+s.2+a.2)
def budget (n : Nat) := 2+StoredOutsideStates.budget n+labelBudget n
theorem bound (e : Ends (ns i)) (first : Bool) : (build ns i (c := c) e first).2 ≤ budget (ns i) := by
  have hs := StoredOutsideStates.bound (ns i)
  have ha := labels_bound ns i (c := c) (StoredOutsideStates.build (ns i)).1 e first
  simp only [build,budget]; omega
theorem shape (e : Ends (ns i)) (first : Bool) :
    StoredRowTransport.Bounds (build ns i (c := c) e first).1.row StoredOutsideGuards.sizeBudget 2 :=
  labels_shape ns i _ e first

theorem build_states (e : Ends (ns i)) (first : Bool) :
    (build ns i (c := c) e first).1.states.count = 4*(ns i)+2 :=
  StoredOutsideStates.count_value _

theorem cast_surjective (S : Table ns i) : Function.Surjective (Fin.cast S.count_eq) :=
  fun j => ⟨Fin.cast S.count_eq.symm j,Fin.ext rfl⟩

theorem marked (S : Table ns i) (e : Ends (ns i)) (first : Bool) {D : Type}
    [(UnifiedBlockPresentation.language ns c).Structure D] (v : Empty → D) :
    (labels ns i (c := c) S e first).1.original.markedNFA v =
      SymbolicComplement.pullback
        ((UnifiedBlockPresentation.compileRow ns c i e first).markedNFA v) (Fin.cast S.count_eq) := by
  rw [value]; rfl

/-- Firing of the stored row is firing of the transported controller. -/
theorem fires (S : Table ns i) (e : Ends (ns i)) (first : Bool) {D : Type}
    [(UnifiedBlockPresentation.language ns c).Structure D] (v : Empty → D)
    (seed : D) (body : List D) :
    Fires (labels ns i (c := c) S e first).1.original v seed body ↔
      Fires (UnifiedBlockPresentation.compileRow ns c i e first) v seed body := by
  have hg : (labels ns i (c := c) S e first).1.original.guard =
      (UnifiedBlockPresentation.compileRow ns c i e first).guard := by rw [value]
  unfold Fires FiresAt
  simp only [marked ns i S e first v,
    SymbolicComplement.pullback_accepts _ _ (cast_surjective ns i S),hg]

theorem build_fires (e : Ends (ns i)) (first : Bool) {D : Type}
    [(UnifiedBlockPresentation.language ns c).Structure D] (v : Empty → D)
    (seed : D) (body : List D) :
    Fires (build ns i (c := c) e first).1.row.original v seed body ↔
      Fires (UnifiedBlockPresentation.compileRow ns c i e first) v seed body :=
  fires ns i _ e first v seed body

/-- The stored rows of one source row decide that row's positive firing, in the
shared presented structure of the whole family. -/
theorem positive_fires_iff_stored {L : FirstOrder.Language} {P : Type}
    (rows : (j : Fin k) → SymbolicGuardedBlocks.Row L P (ns j))
    (C : SymbolicGuardedBlocks.Row L P c) (seed last : P) {D : Type} [L.Structure D] (p : P → D)
    (bs : List (List D)) (hNoA : TerminalCutGeometry.NoA (p last) bs) :
    PositiveFires (rows i) p (p seed) (TerminalBorderRank.decodeBlocks (p last) bs) ↔
      letI := UnifiedBlockPresentation.model rows C seed last p
      ∃ e : Ends (ns i), ∃ first : Bool,
        Fires (build ns i (c := c) e first).1.row.original (Empty.elim : Empty → List D)
          (bs.head?.getD []) bs.tail := by
  letI := UnifiedBlockPresentation.model rows C seed last p
  rw [UnifiedBlockPresentation.positive_fires_iff_shared rows C seed last p i bs hNoA]
  exact exists_congr (fun e => exists_congr (fun first =>
    (build_fires ns i (c := c) e first (Empty.elim : Empty → List D) _ _).symm))

theorem budget_cubic (n : Nat) : budget n = 464+1659*n+1841*n^2+576*n^3 := by
  unfold budget labelBudget matrixBudget vectorBudget vertexCost edgeCost
    StoredOutsideGuards.budget StoredOutsideStates.budget StoredOutsideStates.entriesBudget
    StoredForwardTableBuild.tabBudget
  ring

theorem budget_polynomial (n : Nat) : budget n ≤ 614*(n+1)^3 := by
  have he := budget_cubic n
  have hr : 614*(n+1)^3 = 614+1842*n+1842*n^2+614*n^3 := by ring
  have h1 : 576*n^3 ≤ 614*n^3 := Nat.mul_le_mul (by norm_num) (le_refl _)
  have h2 : 1841*n^2 ≤ 1842*n^2 := Nat.mul_le_mul (by norm_num) (le_refl _)
  have h3 : 1659*n ≤ 1842*n := Nat.mul_le_mul (by norm_num) (le_refl _)
  rw [he,hr]; linarith
theorem polynomial (e : Ends (ns i)) (first : Bool) :
    (build ns i (c := c) e first).2 ≤ 614*((ns i)+1)^3 :=
  (bound ns i e first).trans (budget_polynomial (ns i))
end NSSE.StoredOutsideController
