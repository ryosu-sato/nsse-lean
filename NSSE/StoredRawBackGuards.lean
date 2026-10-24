import NSSE.StoredTwoTapeSlot

/-! Actual stored backward and shared guarded-row transition formulas. -/
namespace NSSE.StoredRawBackGuards
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow ConvolutionShapes
variable {R : Nat → Type} {P : Type} {n : Nat}
abbrev Params (P : Type) (s : Shape 2) := P ⊕ Fin (tapes (mask s)).length

structure Bounds (A : Row R P n) (B K : Nat) : Prop where
  data : ∀ q r, nodes (readPair A.data q r).1.formula ≤ B
  left : ∀ q r, nodes (readPair A.left q r).1.formula ≤ B
  right : ∀ q r, nodes (readPair A.right q r).1.formula ≤ B
  guard : nodes A.guard.formula ≤ B
  data_arity : ∀ q r, arity (readPair A.data q r).1.formula ≤ K
  left_arity : ∀ q r, arity (readPair A.left q r).1.formula ≤ K
  right_arity : ∀ q r, arity (readPair A.right q r).1.formula ≤ K
  guard_arity : arity A.guard.formula ≤ K

def oneName {k : Nat} (x : P ⊕ Fin k) : P ⊕ Fin 1 → (P ⊕ Fin k) × Nat
  | .inl p => (.inl p,1)
  | .inr _ => (x,1)
theorem oneName_value {k : Nat} (x : P ⊕ Fin k) (y : P ⊕ Fin 1) :
    (oneName x y).1 = Sum.elim Sum.inl (fun _ => x) y := by cases y <;> rfl
theorem oneName_bound {k : Nat} (x : P ⊕ Fin k) (y : P ⊕ Fin 1) : (oneName x y).2 ≤ 1 := by cases y <;> rfl

theorem equal_value (q r : Fin n) : (FiniteValuationLookup.equalNat q.val r.val).1 = decide (q=r) := by
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteValuationLookup.equalNat_correct,decide_eq_true_eq,Fin.ext_iff]
theorem literal_value (b : Bool) :
    denote (StoredRelationalReachability.literal (R := R) (P := P) b).1 = if b then ⊤ else ⊥ := by cases b <;> rfl

def back (A : Row R P n) (s : Shape 2) (q r : Fin n) (i : Fin 2) : Data R (Params P s) 0 × Nat :=
  let m := StoredTwoTapeShape.read s i
  if h : m.1 = true then
    let x := StoredTwoTapeSlot.slot s i ((StoredTwoTapeShape.read_value s i).symm.trans h)
    let f := readPair A.data r q
    let g := rename (oneName (P := P) (.inr x.1)) f.1.formula
    (g.1,4+m.2+x.2+f.2+g.2)
  else
    let e := FiniteValuationLookup.equalNat r.val q.val
    let f := StoredRelationalReachability.literal e.1
    (f.1,3+m.2+e.2+f.2)
theorem back_value (A : Row R P n) (s : Shape 2) (q r : Fin n) (i : Fin 2) :
    denote (back A s q r i).1 = A.original.backGuard s q r i := by
  simp only [back,StoredTwoTapeShape.read_value]
  split
  · rename_i h
    simp only [formula_value,oneName_value,StoredTwoTapeSlot.value,SymbolicGuardedBlocks.Row.backGuard,
      h,↓reduceDIte,SymbolicGuardedBlocks.dataAt,Row.original]
  · rename_i h
    simp only [equal_value,literal_value,SymbolicGuardedBlocks.Row.backGuard,h,Bool.false_eq_true,↓reduceDIte,decide_eq_true_eq]
def backBudget (n B K : Nat) := 24+2*n+weight K 1*B
theorem back_bound (A : Row R P n) (s : Shape 2) (q r : Fin n) (i : Fin 2) (B K : Nat) (h : Bounds A B K) :
    (back A s q r i).2 ≤ backBudget n B K := by
  have hm := StoredTwoTapeShape.read_bound s i
  dsimp only [back]
  split
  · rename_i hi
    have hx := StoredTwoTapeSlot.bound s i ((StoredTwoTapeShape.read_value s i).symm.trans hi)
    have hf := readPair_bound A.data r q
    have hg := rename_bound (oneName (P := P) (.inr (StoredTwoTapeSlot.slot s i ((StoredTwoTapeShape.read_value s i).symm.trans hi)).1))
      1 K (oneName_bound _) (readPair A.data r q).1.formula (h.data_arity r q)
    have hn := h.data r q
    unfold backBudget; nlinarith
  · have he := FiniteValuationLookup.equalNat_bound r.val q.val
    have hf := (StoredRelationalReachability.literal_shape (R := R) (P := Params P s)
      (FiniteValuationLookup.equalNat r.val q.val).1).1
    have hr := r.isLt
    unfold backBudget; omega
theorem back_shape (A : Row R P n) (s : Shape 2) (q r : Fin n) (i : Fin 2) (B K : Nat) (h : Bounds A B K) :
    nodes (back A s q r i).1 ≤ B+3 ∧ arity (back A s q r i).1 ≤ K := by
  dsimp only [back]
  split
  · simp only [rename_nodes,rename_arity]
    exact ⟨by have hn := h.data r q; omega,h.data_arity r q⟩
  · have hf := (StoredRelationalReachability.literal_shape (R := R) (P := Params P s)
      (FiniteValuationLookup.equalNat r.val q.val).1).2
    dsimp only
    exact ⟨by omega,by rw [hf.2]; exact Nat.zero_le K⟩
theorem back_qf (A : Row R P n) (s : Shape 2) (q r : Fin n) (i : Fin 2) : (denote (back A s q r i).1).IsQF := by
  rw [back_value]
  exact ExactGuardedRunFormula.backGuard_qf A.original A.qfree.toRowQF s q r i

def pair (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) : Data R (Params P s) 0 × Nat :=
  let a := back A s q.1 r.1 0
  let b := back A s q.2 r.2 1
  (StoredArrayEquality.conj a.1 b.1,7+a.2+b.2)
theorem pair_value (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) :
    denote (pair A s q r).1 = A.original.pairBackGuard s q r := by
  simp only [pair,StoredArrayEquality.conj,denote,back_value,SymbolicGuardedBlocks.Row.pairBackGuard]
  rfl
def pairBudget (n B K : Nat) := 7+2*backBudget n B K
theorem pair_bound (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (B K : Nat) (h : Bounds A B K) :
    (pair A s q r).2 ≤ pairBudget n B K := by
  have ha := back_bound A s q.1 r.1 0 B K h
  have hb := back_bound A s q.2 r.2 1 B K h
  simp only [pair,pairBudget]; omega
theorem pair_shape (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (B K : Nat) (h : Bounds A B K) :
    nodes (pair A s q r).1 ≤ 11+2*B ∧ arity (pair A s q r).1 ≤ K := by
  have ha := back_shape A s q.1 r.1 0 B K h
  have hb := back_shape A s q.2 r.2 1 B K h
  constructor
  · simp only [pair,StoredArrayEquality.conj,nodes]; omega
  · exact StoredRunTable.conj_arity_le _ _ K ha.2 hb.2

def shared (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) : Data R (Params P s) 0 × Nat :=
  let a := StoredTwoTapeShape.read s 0
  let b := StoredTwoTapeShape.read s 1
  if h : a.1 = true ∧ b.1 = true then
    let i := StoredTwoTapeSlot.slot s 0 ((StoredTwoTapeShape.read_value s 0).symm.trans h.1)
    let j := StoredTwoTapeSlot.slot s 1 ((StoredTwoTapeShape.read_value s 1).symm.trans h.2)
    let p := pair A s q r
    (StoredArrayEquality.conj (.equal (.inl (.inr i.1)) (.inl (.inr j.1))) p.1,12+a.2+b.2+i.2+j.2+p.2)
  else (.falsum,3+a.2+b.2)
theorem shared_value (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) :
    denote (shared A s q r).1 = A.original.sharedGuard s q r := by
  simp only [shared,StoredTwoTapeShape.read_value]
  split
  · rename_i h
    simp only [StoredArrayEquality.conj,denote,StoredTwoTapeSlot.value,pair_value,
      SymbolicGuardedBlocks.Row.sharedGuard,h,↓reduceIte,WordEqualityAutomaton.equalityGuard,h.1,h.2,↓reduceDIte]
    rfl
  · rename_i h
    simp only [denote,SymbolicGuardedBlocks.Row.sharedGuard,h,↓reduceIte]
    rfl
def sharedBudget (n B K : Nat) := 44+pairBudget n B K
theorem shared_bound (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (B K : Nat) (h : Bounds A B K) :
    (shared A s q r).2 ≤ sharedBudget n B K := by
  have ha := StoredTwoTapeShape.read_bound s 0
  have hb := StoredTwoTapeShape.read_bound s 1
  dsimp only [shared]
  split
  · rename_i hs
    have hi := StoredTwoTapeSlot.bound s 0 ((StoredTwoTapeShape.read_value s 0).symm.trans hs.1)
    have hj := StoredTwoTapeSlot.bound s 1 ((StoredTwoTapeShape.read_value s 1).symm.trans hs.2)
    have hp := pair_bound A s q r B K h
    unfold sharedBudget; omega
  · unfold sharedBudget; omega
theorem shared_shape (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) (B K : Nat) (h : Bounds A B K) :
    nodes (shared A s q r).1 ≤ 17+2*B ∧ arity (shared A s q r).1 ≤ K := by
  dsimp only [shared]
  split
  · have hp := pair_shape A s q r B K h
    constructor
    · simp only [StoredArrayEquality.conj,nodes]; omega
    · exact StoredRunTable.conj_arity_le _ _ K (Nat.zero_le K) hp.2
  · exact ⟨by simp only [nodes]; omega,Nat.zero_le K⟩
theorem shared_qf (A : Row R P n) (s : Shape 2) (q r : Fin n × Fin n) :
    (denote (shared A s q r).1).IsQF := by
  rw [shared_value]
  exact ExactGuardedRunFormula.sharedGuard_qf A.original A.qfree.toRowQF s q r
end NSSE.StoredRawBackGuards
