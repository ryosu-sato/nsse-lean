import NSSE.DynamicColumnSelection

/-! # Exact signed runs with valuation-dependent column shapes and empty padding -/

namespace NSSE.DynamicColumnRunFormula

open FirstOrder FirstOrder.Language SymbolicAutomata SymbolicGuardedBlocks ConvolutionShapes
open ExactReachabilityTable GuardedBlockRelation

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n k : Nat}

noncomputable def inputWord {D : Type*} (p : P → D) (flags letters : Nat → Fin k → P)
    (one : P) (T : Nat) : List (Sparse D k) :=
  List.ofFn (fun t : Fin T => DynamicColumnSelection.column p (flags t) (letters t) one)

theorem inputWord_succ {D : Type*} (p : P → D) (flags letters : Nat → Fin k → P) (one : P) (T : Nat) :
    inputWord p flags letters one (T+1) = inputWord p flags letters one T ++
      [DynamicColumnSelection.column p (flags T) (letters T) one] := by
  unfold inputWord
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

def steps (A : WordAutomaton L P n k) (flags letters : Nat → Fin k → P) (one : P)
    (t : Nat) (q r : Fin n) : L.Formula P := DynamicColumnSelection.step A (flags t) (letters t) one q r

theorem reachable_runs (A : WordAutomaton L P n k) (flags letters : Nat → Fin k → P) (one : P)
    {D : Type*} [L.Structure D] (p : P → D) (T : Nat) (q : Fin n) :
    reachable A.initial (steps A flags letters one) p T q ↔
      ∃ s, (A.dataInterpret p).start s ∧ (A.dataInterpret p).Runs s (inputWord p flags letters one T) q := by
  induction T generalizing q with
  | zero => simp [reachable, inputWord, runs_nil_iff, Automaton.dataInterpret]
  | succ T ih =>
    simp only [reachable, ih, steps, DynamicColumnSelection.step_correct, inputWord_succ,
      runs_append_singleton]
    constructor
    · rintro ⟨r, ⟨s, hs, hr⟩, ht⟩
      exact ⟨s, hs, r, hr, ht⟩
    · rintro ⟨s, hs, r, hr, ht⟩
      exact ⟨r, ⟨s, hs, hr⟩, ht⟩

def compile (A : WordAutomaton L P n k) (flags letters : Nat → Fin k → P)
    (one : P) (T : Nat) (positive : Bool) : L.Formula P :=
  ExactReachabilityTable.compile A.initial A.final (steps A flags letters one) one T positive

theorem compile_correct (A : WordAutomaton L P n k) (flags letters : Nat → Fin k → P)
    (zero one : P) (T : Nat) (positive : Bool) {D : Type*} [L.Structure D]
    (p : P → D) (h01 : p zero ≠ p one) :
    (compile A flags letters one T positive).Realize p ↔
      ((A.dataInterpret p).Accepts (inputWord p flags letters one T) ↔ positive = true) := by
  rw [compile, ExactReachabilityTable.compile_correct _ _ _ zero one T positive p h01]
  refine iff_congr ?_ Iff.rfl
  simp only [reachable_runs, NSSE.NFA.Accepts]
  constructor
  · rintro ⟨q, ⟨s, hs, hr⟩, hf⟩
    exact ⟨s, q, hs, hr, hf⟩
  · rintro ⟨s, q, hs, hr, hf⟩
    exact ⟨q, ⟨s, hs, hr⟩, hf⟩

def compileH (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    (flags letters : Nat → Fin 2 → P) (one : P) (T : Nat) (positive : Bool) : L.Formula P :=
  compile (SkipEmptyColumns.automaton (R.raw e seed last first)) flags letters one T positive

theorem compileH_literal (R : Row L P n) (e : Ends n) (seed last : P) (first : Bool)
    (flags letters : Nat → Fin 2 → P) (zero one : P) (T : Nat) (positive : Bool)
    {D : Type*} [L.Structure D] (p : P → D) (h01 : p zero ≠ p one)
    (hc : CanonicalConvolution.Canonical
      (((inputWord p flags letters one T).map toDense).filter CanonicalConvolution.present)) :
    (compileH R e seed last first flags letters one T positive).Realize p ↔
      (R.LiteralH e seed last first p
        (CanonicalConvolution.decode ((inputWord p flags letters one T).map toDense) 0).reverse
        (CanonicalConvolution.decode ((inputWord p flags letters one T).map toDense) 1).reverse ↔
        positive = true) := by
  rw [compileH, compile_correct _ flags letters zero one T positive p h01,
    SkipEmptyColumns.data_accepts,
    ← (R.raw e seed last first).accepts_iff_data_of_noSilent p (by intro q r; simp [Row.raw]),
    R.raw_correct, SkipEmptyColumns.filter_dense,
    (R.semantics e seed last first p).accepts_correct _ hc,
    ← R.H_iff_literal, R.H_iff_core]
  simp only [List.reverse_reverse]
  rw [SkipEmptyColumns.decode_filter]

theorem compile_matrix_qf (A : WordAutomaton L P n k) (flags letters : Nat → Fin k → P)
    (one : P) (T : Nat) (positive : Bool)
    (hi : ∀ q, (A.initial q).IsQF) (hf : ∀ q, (A.final q).IsQF)
    (hs : ∀ s q r, (A.step s q r).IsQF) :
    (matrix A.initial (steps A flags letters one) one T ⊓ signed positive (output A.final one T)).IsQF :=
  ExactReachabilityTable.compile_matrix_qf _ _ _ _ _ _ hi hf
    (fun t _ q r => DynamicColumnSelection.step_qf A (flags t) (letters t) one hs q r)

theorem nodes_compile_le {G : Nat} (A : WordAutomaton L P n k) (flags letters : Nat → Fin k → P)
    (one : P) (T : Nat) (positive : Bool)
    (hi : ∀ q, ExactReachabilitySize.nodes (A.initial q) ≤ G)
    (hf : ∀ q, ExactReachabilitySize.nodes (A.final q) ≤ G)
    (hs : ∀ s q r, ExactReachabilitySize.nodes (A.step s q r) ≤ G) :
    let H := G+1+(SymbolicComplement.masks k).length*(11+8*k+G)
    ExactReachabilitySize.nodes (compile A flags letters one T positive) ≤
      19+n*(14+2*H)+T*(8+n*(16+2*n*(9+H)))+n*(9+H)+5*((T+1)*n) := by
  apply ExactReachabilitySize.nodes_compile_le
  · intro q
    have hh := hi q
    omega
  · intro q
    have hh := hf q
    omega
  · intro t _ q r
    have hh := DynamicColumnSelection.nodes_step A (flags t) (letters t) one hs q r
    exact Nat.le_trans hh (by omega)

theorem compileH_matrix_qf (R : Row L P n) (h : ExactGuardedRunFormula.RowQF R)
    (e : Ends n) (seed last : P) (first : Bool) (flags letters : Nat → Fin 2 → P)
    (one : P) (T : Nat) (positive : Bool) :
    let A := SkipEmptyColumns.automaton (R.raw e seed last first)
    (matrix A.initial (steps A flags letters one) one T ⊓ signed positive (output A.final one T)).IsQF := by
  apply compile_matrix_qf
  · exact ExactGuardedRunFormula.raw_initial_qf R h e seed last first
  · exact ExactGuardedRunFormula.raw_final_qf R h e seed last first
  · exact SkipEmptyColumns.step_qf _ (ExactGuardedRunFormula.raw_step_qf R h e seed last first)

theorem nodes_compileH_le {B : Nat} (R : Row L P n) (h : ExactGuardedRunSize.RowSize R B)
    (e : Ends n) (seed last : P) (first : Bool) (flags letters : Nat → Fin 2 → P)
    (one : P) (T : Nat) (positive : Bool) :
    let N := 2*n*n
    let H := 109+5*ExactGuardedRunSize.guardBound n B
    ExactReachabilitySize.nodes (compileH R e seed last first flags letters one T positive) ≤
      19+N*(14+2*H)+T*(8+N*(16+2*N*(9+H)))+N*(9+H)+5*((T+1)*N) := by
  have hG : 3 ≤ ExactGuardedRunSize.guardBound n B := by
    unfold ExactGuardedRunSize.guardBound
    omega
  have hh := nodes_compile_le (SkipEmptyColumns.automaton (R.raw e seed last first)) flags letters one T positive
    (ExactGuardedRunSize.raw_initial_le R h e seed last first)
    (ExactGuardedRunSize.raw_final_le R h e seed last first)
    (SkipEmptyColumns.step_nodes_le _ (ExactGuardedRunSize.raw_step_le R h e seed last first) hG)
  have hn (G : Nat) : G+1+2^2*(11+8*2+G) = 109+5*G := by omega
  simpa only [length_states, SymbolicComplement.length_masks, hn] using hh

end NSSE.DynamicColumnRunFormula
