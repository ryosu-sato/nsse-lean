import NSSE.StoredRawTransition

/-! Actual stored initial and final guards of the guarded raw row. -/
namespace NSSE.StoredRawEndpoints
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow StoredRawBackGuards
variable {R : Nat → Type} {P : Type} {n : Nat}

def dataAt (A : Row R P n) (q r : Fin n) (last : P) : Data R P 0 × Nat :=
  let a := readPair A.data q r
  let b := rename (StoredArrayParameterAtoms.seedName last) a.1.formula
  (b.1,1+a.2+b.2)
theorem dataAt_value (A : Row R P n) (q r : Fin n) (last : P) :
    denote (dataAt A q r last).1 = SymbolicGuardedBlocks.dataAt (A.original.data q r) id last := by
  simp only [dataAt,formula_value,StoredArrayParameterAtoms.seedName_value,SymbolicGuardedBlocks.dataAt,Row.original]
def dataBudget (n B K : Nat) := 2+2*n+weight K 1*B
theorem dataAt_bound (A : Row R P n) (q r : Fin n) (last : P) (B K : Nat) (h : Bounds A B K) :
    (dataAt A q r last).2 ≤ dataBudget n B K := by
  have ha := readPair_bound A.data q r
  have hb := rename_bound (StoredArrayParameterAtoms.seedName last) 1 K (StoredArrayParameterAtoms.seedName_bound last)
    (readPair A.data q r).1.formula (h.data_arity q r)
  have hn := h.data q r
  simp only [dataAt,dataBudget]; nlinarith
theorem dataAt_shape (A : Row R P n) (q r : Fin n) (last : P) (B K : Nat) (h : Bounds A B K) :
    nodes (dataAt A q r last).1 ≤ B ∧ arity (dataAt A q r last).1 ≤ K := by
  simp only [dataAt,rename_nodes,rename_arity]
  exact ⟨h.data q r,h.data_arity q r⟩

def initial (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (last : P) (q : StoredRawTransition.State n) : Data R P 0 × Nat :=
  if q.1 then (.falsum,2) else
    let a := dataAt A q.2.1 e.leftEnd last
    let b := dataAt A q.2.2 e.rightEnd last
    (StoredArrayEquality.conj a.1 b.1,7+a.2+b.2)
theorem initial_value (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (last : P) (q : StoredRawTransition.State n) :
    denote (initial A e last q).1 = A.original.initialGuard e last q := by
  obtain ⟨b,q1,q2⟩ := q
  cases b <;> simp only [initial,Bool.false_eq_true,↓reduceIte,StoredArrayEquality.conj,denote,dataAt_value,
    SymbolicGuardedBlocks.Row.initialGuard]
  all_goals rfl
def initialBudget (n B K : Nat) := 7+2*dataBudget n B K
theorem initial_bound (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (last : P) (q : StoredRawTransition.State n)
    (B K : Nat) (h : Bounds A B K) : (initial A e last q).2 ≤ initialBudget n B K := by
  have ha := dataAt_bound A q.2.1 e.leftEnd last B K h
  have hb := dataAt_bound A q.2.2 e.rightEnd last B K h
  dsimp only [initial]
  split <;> unfold initialBudget <;> omega
theorem initial_shape (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (last : P) (q : StoredRawTransition.State n)
    (B K : Nat) (h : Bounds A B K) : nodes (initial A e last q).1 ≤ 5+2*B ∧ arity (initial A e last q).1 ≤ K := by
  have ha := dataAt_shape A q.2.1 e.leftEnd last B K h
  have hb := dataAt_shape A q.2.2 e.rightEnd last B K h
  dsimp only [initial]
  split
  · exact ⟨by simp only [nodes]; omega,Nat.zero_le K⟩
  · constructor
    · simp only [StoredArrayEquality.conj,nodes]; omega
    · exact StoredRunTable.conj_arity_le _ _ K ha.2 hb.2

def guardName (x y : P) : P ⊕ Fin 2 → P × Nat
  | .inl p => (p,1)
  | .inr i => (if i.val=0 then x else y,2)
theorem guardName_value (x y : P) (z : P ⊕ Fin 2) : (guardName x y z).1 = Sum.elim id ![x,y] z := by
  cases z with
  | inl p => rfl
  | inr i => fin_cases i <;> rfl
theorem guardName_bound (x y : P) (z : P ⊕ Fin 2) : (guardName x y z).2 ≤ 2 := by
  cases z with
  | inl p => exact (by decide : 1 ≤ 2)
  | inr i => exact Nat.le_refl 2

def final (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) (q : StoredRawTransition.State n) : Data R P 0 × Nat :=
  if q.1 then
    let a := FiniteValuationLookup.equalNat q.2.1.val e.leftStart.val
    let b := FiniteValuationLookup.equalNat q.2.2.val e.rightStart.val
    let f := StoredRelationalReachability.literal (a.1 && b.1)
    (f.1,5+a.2+b.2+f.2)
  else
    let a := readPair A.left e.leftStart q.2.1
    let b := readPair A.right e.rightStart q.2.2
    let c := rename (guardName (if first then seed else last) last) A.guard.formula
    (StoredArrayEquality.conj a.1.formula (StoredArrayEquality.conj b.1.formula c.1),13+a.2+b.2+c.2)
theorem final_value (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) (q : StoredRawTransition.State n) :
    denote (final A e seed last first q).1 = A.original.finalGuard e seed last first q := by
  obtain ⟨b,q1,q2⟩ := q
  cases b
  · simp only [final,Bool.false_eq_true,↓reduceIte,StoredArrayEquality.conj,denote,formula_value,guardName_value,
      SymbolicGuardedBlocks.Row.finalGuard,SymbolicGuardedBlocks.guardAt,SymbolicGuardedBlocks.fallback,Row.original]
    rfl
  · simp only [final,↓reduceIte,equal_value,literal_value,Bool.and_eq_true,decide_eq_true_eq,
      SymbolicGuardedBlocks.Row.finalGuard,Prod.mk.injEq]
def finalBudget (n B K : Nat) := 23+4*n+weight K 2*B
theorem final_bound (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) (q : StoredRawTransition.State n)
    (B K : Nat) (h : Bounds A B K) : (final A e seed last first q).2 ≤ finalBudget n B K := by
  dsimp only [final]
  split
  · have ha := FiniteValuationLookup.equalNat_bound q.2.1.val e.leftStart.val
    have hb := FiniteValuationLookup.equalNat_bound q.2.2.val e.rightStart.val
    have hf := (StoredRelationalReachability.literal_shape (R := R) (P := P)
      ((FiniteValuationLookup.equalNat q.2.1.val e.leftStart.val).1 &&
       (FiniteValuationLookup.equalNat q.2.2.val e.rightStart.val).1)).1
    have hq := q.2.1.isLt
    have hr := q.2.2.isLt
    unfold finalBudget; omega
  · have ha := readPair_bound A.left e.leftStart q.2.1
    have hb := readPair_bound A.right e.rightStart q.2.2
    have hc := rename_bound (guardName (if first then seed else last) last) 2 K (guardName_bound _ _)
      A.guard.formula h.guard_arity
    have hn := h.guard
    unfold finalBudget; nlinarith
theorem final_shape (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) (q : StoredRawTransition.State n)
    (B K : Nat) (h : Bounds A B K) : nodes (final A e seed last first q).1 ≤ 10+3*B ∧ arity (final A e seed last first q).1 ≤ K := by
  dsimp only [final]
  split
  · have hf := (StoredRelationalReachability.literal_shape (R := R) (P := P)
      ((FiniteValuationLookup.equalNat q.2.1.val e.leftStart.val).1 &&
       (FiniteValuationLookup.equalNat q.2.2.val e.rightStart.val).1)).2
    dsimp only
    exact ⟨by omega,by rw [hf.2]; exact Nat.zero_le K⟩
  · constructor
    · have ha := h.left e.leftStart q.2.1
      have hb := h.right e.rightStart q.2.2
      have hc := h.guard
      simp only [StoredArrayEquality.conj,nodes,rename_nodes]; omega
    · apply StoredRunTable.conj_arity_le _ _ K (h.left_arity e.leftStart q.2.1)
      apply StoredRunTable.conj_arity_le _ _ K (h.right_arity e.rightStart q.2.2)
      rw [rename_arity]; exact h.guard_arity

theorem initial_qf (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (last : P) (q : StoredRawTransition.State n) :
    (denote (initial A e last q).1).IsQF := by
  rw [initial_value]
  unfold SymbolicGuardedBlocks.Row.initialGuard
  split
  · exact BoundedFormula.isQF_bot
  · exact (ExactReachabilityTable.relabel_qf _ (A.qfree.data _ _) _).inf
      (ExactReachabilityTable.relabel_qf _ (A.qfree.data _ _) _)
theorem final_qf (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) (q : StoredRawTransition.State n) :
    (denote (final A e seed last first q).1).IsQF := by
  rw [final_value]
  unfold SymbolicGuardedBlocks.Row.finalGuard
  split
  · split
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot
  · exact (A.qfree.left _ _).inf ((A.qfree.right _ _).inf (ExactReachabilityTable.relabel_qf _ A.qfree.guard _))

def initialLabel (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (last : P) (q : StoredRawTransition.State n) : QF R P × Nat :=
  let a := initial A e last q
  (⟨a.1,initial_qf A e last q⟩,1+a.2)
def finalLabel (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) (q : StoredRawTransition.State n) : QF R P × Nat :=
  let a := final A e seed last first q
  (⟨a.1,final_qf A e seed last first q⟩,1+a.2)
theorem initialLabel_bound (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (last : P) (q : StoredRawTransition.State n)
    (B K : Nat) (h : Bounds A B K) : StoredRunTable.LabelBound (initialLabel A e last q) (1+initialBudget n B K) (5+2*B) K := by
  have hc := initial_bound A e last q B K h
  have hs := initial_shape A e last q B K h
  exact ⟨by simp only [initialLabel]; omega,hs.1,hs.2⟩
theorem finalLabel_bound (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) (q : StoredRawTransition.State n)
    (B K : Nat) (h : Bounds A B K) : StoredRunTable.LabelBound (finalLabel A e seed last first q) (1+finalBudget n B K) (10+3*B) K := by
  have hc := final_bound A e seed last first q B K h
  have hs := final_shape A e seed last first q B K h
  exact ⟨by simp only [finalLabel]; omega,hs.1,hs.2⟩
end NSSE.StoredRawEndpoints
