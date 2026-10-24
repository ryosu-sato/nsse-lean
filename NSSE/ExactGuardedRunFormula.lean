import NSSE.ExactColumnRunFormula

/-! # Signed H formulas from the actual 2*n*n-state raw automaton -/

namespace NSSE.ExactGuardedRunFormula

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ConvolutionShapes
open GuardedBlockRelation ExactReachabilityTable

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n : Nat}

def denseWord {D : Type*} (p : P → D) (columns : Nat → Sparse P 2) (T : Nat) :
    List (CanonicalConvolution.Column D 2) :=
  (ExactColumnRunFormula.inputWord p columns T).map toDense

def compile (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    (columns : Nat → Sparse P 2) (one : P) (T : Nat) (positive : Bool) : L.Formula P :=
  ExactColumnRunFormula.compile (R.raw e seed last first) columns one T positive

theorem compile_automaton (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    (columns : Nat → Sparse P 2) (zero one : P) (T : Nat) (positive : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one) :
    (compile R e seed last first columns one T positive).Realize p ↔
      ((R.semantics e seed last first p).automaton.Accepts (denseWord p columns T) ↔ positive = true) := by
  rw [compile, ExactColumnRunFormula.compile_noSilent _ columns zero one T positive p h01
    (by intro q r; simp [Row.raw]), R.raw_correct]
  rfl

/-- Correctness for canonical column inputs, including unequal and empty tapes. -/
theorem compile_literalH (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    (columns : Nat → Sparse P 2) (zero one : P) (T : Nat) (positive : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one)
    (hc : CanonicalConvolution.Canonical (denseWord p columns T)) :
    (compile R e seed last first columns one T positive).Realize p ↔
      (R.LiteralH e seed last first p
        ((CanonicalConvolution.decode (denseWord p columns T) 0).reverse)
        ((CanonicalConvolution.decode (denseWord p columns T) 1).reverse) ↔ positive = true) := by
  rw [compile_automaton R e seed last first columns zero one T positive p h01,
    (R.semantics e seed last first p).accepts_correct _ hc,
    ← R.H_iff_literal, R.H_iff_core]
  simp only [List.reverse_reverse]

/-- The concrete table uses the actual raw state count, before any padding monitor. -/
theorem table_variables (T : Nat) : (T+1)*(states n).length = (T+1)*(2*n*n) := by
  rw [length_states]

structure RowQF (R : Row L P n) : Prop where
  data : ∀ q r, (R.data q r).IsQF
  left : ∀ q r, (R.left q r).IsQF
  right : ∀ q r, (R.right q r).IsQF
  guard : R.guard.IsQF

theorem backGuard_qf (R : Row L P n) (h : RowQF R) (s : Shape 2)
    (q r : Fin n) (i : Fin 2) : (R.backGuard s q r i).IsQF := by
  unfold Row.backGuard
  split
  · exact relabel_qf _ (h.data r q) _
  · split
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot

theorem pairBackGuard_qf (R : Row L P n) (h : RowQF R) (s : Shape 2)
    (q r : PairState (Fin n)) : (R.pairBackGuard s q r).IsQF :=
  (backGuard_qf R h s _ _ _).inf (backGuard_qf R h s _ _ _)

theorem equalityGuard_qf (s : Shape 2) :
    (WordEqualityAutomaton.equalityGuard (L := L) (P := P) 0 1 s).IsQF := by
  unfold WordEqualityAutomaton.equalityGuard
  split
  · split
    · exact BoundedFormula.IsAtomic.isQF (.equal _ _)
    · exact BoundedFormula.isQF_bot
  · split
    · exact BoundedFormula.isQF_bot
    · exact BoundedFormula.IsQF.top

theorem sharedGuard_qf (R : Row L P n) (h : RowQF R) (s : Shape 2)
    (q r : PairState (Fin n)) : (R.sharedGuard s q r).IsQF := by
  unfold Row.sharedGuard
  split
  · exact (equalityGuard_qf s).inf (pairBackGuard_qf R h s q r)
  · exact BoundedFormula.isQF_bot

theorem switchGuard_qf (R : Row L P n) (h : RowQF R) (s : Shape 2)
    (q r : PairState (Fin n)) (seed last : P) (first : Bool) :
    (R.switchGuard s q r seed last first).IsQF := by
  apply BoundedFormula.IsQF.inf
  · exact relabel_qf _ h.guard _
  · apply any_qf
    intro z
    apply any_qf
    intro z'
    exact (relabel_qf _ (h.left _ _) _).inf
      ((relabel_qf _ (h.right _ _) _).inf (pairBackGuard_qf R h s _ _))

theorem raw_initial_qf (R : Row L P n) (h : RowQF R) (e : Ends n) (seed last : P) (first : Bool)
    (q : Fin (states n).length) : ((R.raw e seed last first).initial q).IsQF := by
  change (R.initialGuard e last (stateAt n q)).IsQF
  unfold Row.initialGuard
  split
  · exact BoundedFormula.isQF_bot
  · exact (relabel_qf _ (h.data _ _) _).inf (relabel_qf _ (h.data _ _) _)

theorem raw_final_qf (R : Row L P n) (h : RowQF R) (e : Ends n) (seed last : P) (first : Bool)
    (q : Fin (states n).length) : ((R.raw e seed last first).final q).IsQF := by
  change (R.finalGuard e seed last first (stateAt n q)).IsQF
  unfold Row.finalGuard
  split
  · split
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot
  · exact (h.left _ _).inf ((h.right _ _).inf (relabel_qf _ h.guard _))

theorem raw_step_qf (R : Row L P n) (h : RowQF R) (e : Ends n) (seed last : P) (first : Bool)
    (s : Shape 2) (q r : Fin (states n).length) : ((R.raw e seed last first).step s q r).IsQF := by
  change (R.stepGuard s seed last first (stateAt n q) (stateAt n r)).IsQF
  unfold Row.stepGuard
  split
  · exact sharedGuard_qf R h s _ _
  · exact switchGuard_qf R h s _ _ seed last first
  · exact pairBackGuard_qf R h s _ _
  · exact BoundedFormula.isQF_bot

theorem compile_matrix_qf (R : Row L P n) (h : RowQF R) (e : Ends n) (seed last : P) (first : Bool)
    (columns : Nat → Sparse P 2) (one : P) (T : Nat) (positive : Bool) :
    (matrix (R.raw e seed last first).initial
      (ExactColumnRunFormula.steps (R.raw e seed last first) columns) one T ⊓
      signed positive (output (R.raw e seed last first).final one T)).IsQF :=
  ExactColumnRunFormula.compile_matrix_qf _ _ _ _ _
    (raw_initial_qf R h e seed last first) (raw_final_qf R h e seed last first)
    (raw_step_qf R h e seed last first)

end NSSE.ExactGuardedRunFormula
