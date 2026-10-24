import NSSE.SkipEmptyColumns

/-! # Column shapes selected by scalar presence flags

The syntax constructor enumerates only the 2^k local masks at one position,
not combinations of lengths across all word variables.
-/

namespace NSSE.DynamicColumnSelection

open FirstOrder FirstOrder.Language SymbolicAutomata ConvolutionShapes
open ExactReachabilityTable SymbolicReachability ExactReachabilitySize

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n k : Nat}

def flag (one x : P) : L.Formula P := (Term.var x).equal (Term.var one)

@[simp] theorem realize_flag {D : Type*} [L.Structure D] (p : P → D) (one x : P) :
    (flag (L := L) one x).Realize p ↔ p x = p one := by simp [flag]

def select (flags : Fin k → P) (one : P) (s : Shape k) : L.Formula P :=
  every k (fun i => signed (mask s i) (flag one (flags i)))

noncomputable def chosenMask {D : Type*} (p : P → D) (flags : Fin k → P) (one : P) : Mask k :=
  fun i => @decide (p (flags i) = p one) (Classical.propDecidable _)

noncomputable def column {D : Type*} (p : P → D) (flags letters : Fin k → P) (one : P) : Sparse D k :=
  ⟨code (chosenMask p flags one), fun j => p (letters (tape (mask (code (chosenMask p flags one))) j))⟩

theorem select_mask {D : Type*} [L.Structure D] (p : P → D)
    (flags : Fin k → P) (one : P) (s : Shape k) :
    (select (L := L) flags one s).Realize p ↔ mask s = chosenMask p flags one := by
  classical
  simp only [select, realize_every, realize_signed, realize_flag, funext_iff]
  apply forall_congr'
  intro i
  cases h : mask s i <;> simp [chosenMask, h]

theorem select_shape {D : Type*} [L.Structure D] (p : P → D)
    (flags letters : Fin k → P) (one : P) (s : Shape k) :
    (select (L := L) flags one s).Realize p ↔ s = (column p flags letters one).1 := by
  rw [select_mask]
  change mask s = chosenMask p flags one ↔ s = code (chosenMask p flags one)
  constructor
  · intro h
    calc
      s = code (mask s) := (code_mask s).symm
      _ = code (chosenMask p flags one) := congrArg code h
  · rintro rfl
    exact mask_code _

theorem dense_column {D : Type*} (p : P → D) (flags letters : Fin k → P) (one : P) (i : Fin k) :
    toDense (column p flags letters one) i =
      @ite (Option D) (p (flags i) = p one) (Classical.propDecidable _) (some (p (letters i))) none := by
  classical
  simp [toDense, column, expand, chosenMask]

def step (A : WordAutomaton L P n k) (flags letters : Fin k → P) (one : P) (q r : Fin n) :
    L.Formula P :=
  any (SymbolicComplement.masks k).length (fun s => select flags one s ⊓
    (A.step s q r).relabel (Sum.elim id (fun j => letters (tape (mask s) j))))

theorem step_correct (A : WordAutomaton L P n k) (flags letters : Fin k → P) (one : P)
    {D : Type*} [L.Structure D] (p : P → D) (q r : Fin n) :
    (step A flags letters one q r).Realize p ↔
      (A.dataInterpret p).step q (column p flags letters one) r := by
  simp only [step, realize_any, Formula.realize_inf, select_shape p flags letters one]
  simp only [exists_eq_left, Formula.realize_relabel]
  change (A.step _ q r).Realize _ ↔ (A.step _ q r).Realize _
  have he : p ∘ Sum.elim id (fun j => letters (tape (mask (column p flags letters one).1) j)) =
      Sum.elim p (column p flags letters one).2 := by
    funext i
    cases i <;> rfl
  rw [he]

theorem select_qf (flags : Fin k → P) (one : P) (s : Shape k) :
    (select (L := L) flags one s).IsQF := by
  apply every_qf
  intro i
  exact signed_qf _ _ (BoundedFormula.IsAtomic.isQF (.equal _ _))

theorem step_qf (A : WordAutomaton L P n k) (flags letters : Fin k → P) (one : P)
    (hs : ∀ s q r, (A.step s q r).IsQF) (q r : Fin n) :
    (step A flags letters one q r).IsQF := by
  apply any_qf
  intro s
  exact (select_qf flags one s).inf (relabel_qf _ (hs s q r) _)

theorem nodes_select (flags : Fin k → P) (one : P) (s : Shape k) :
    nodes (select (L := L) flags one s) ≤ 3+8*k := by
  rw [select, nodes_every]
  have h (i : Fin k) : nodes (signed (mask s i) (flag (L := L) one (flags i))) ≤ 3 :=
    nodes_signed_le _ _
  calc
    _ ≤ 3 + ∑ _i : Fin k, 8 := Nat.add_le_add_left
      (Finset.sum_le_sum (fun i _ => by have hh := h i; omega)) 3
    _ = _ := by simp [Nat.mul_comm]

theorem nodes_step {G : Nat} (A : WordAutomaton L P n k) (flags letters : Fin k → P) (one : P)
    (hs : ∀ s q r, nodes (A.step s q r) ≤ G) (q r : Fin n) :
    nodes (step A flags letters one q r) ≤ 1+(SymbolicComplement.masks k).length*(11+8*k+G) := by
  have hbody (s : Shape k) : nodes (select (L := L) flags one s ⊓
      (A.step s q r).relabel (Sum.elim id (fun j => letters (tape (mask s) j)))) ≤ 8+8*k+G := by
    simp only [nodes_inf, nodes_relabel]
    have h₁ := nodes_select (L := L) flags one s
    have h₂ := hs s q r
    omega
  simpa only [show 3+(8+8*k+G) = 11+8*k+G by omega] using
    ExactGuardedRunSize.nodes_any_le _ (8+8*k+G) _ hbody

end NSSE.DynamicColumnSelection
