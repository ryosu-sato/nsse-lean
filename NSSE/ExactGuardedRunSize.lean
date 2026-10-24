import NSSE.ExactGuardedRunFormula

/-! # Polynomial guard and table size for the actual H construction -/

namespace NSSE.ExactGuardedRunSize

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ConvolutionShapes
open GuardedBlockRelation ExactReachabilitySize ExactReachabilityTable SymbolicReachability

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n B : Nat}

structure RowSize (R : Row L P n) (B : Nat) : Prop where
  data : ∀ q r, nodes (R.data q r) ≤ B
  left : ∀ q r, nodes (R.left q r) ≤ B
  right : ∀ q r, nodes (R.right q r) ≤ B
  guard : nodes R.guard ≤ B

def guardBound (n B : Nat) : Nat := 40+6*B+n*(4+n*(24+4*B))

theorem nodes_any_le {Q : Type*} (m b : Nat) (f : Fin m → L.Formula Q)
    (h : ∀ i, nodes (f i) ≤ b) : nodes (any m f) ≤ 1+m*(3+b) := by
  rw [nodes_any]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _i : Fin m, (3+b) := Finset.sum_le_sum (fun i _ => Nat.add_le_add_left (h i) 3)
    _ = _ := by simp

theorem backGuard_le (R : Row L P n) (h : RowSize R B) (s : Shape 2)
    (q r : Fin n) (i : Fin 2) : nodes (R.backGuard s q r i) ≤ B+3 := by
  unfold Row.backGuard
  split
  · simp only [dataAt, nodes_relabel]
    have hh := h.data r q
    omega
  · split <;> simp [nodes, BoundedFormula.not]

theorem pairBackGuard_le (R : Row L P n) (h : RowSize R B) (s : Shape 2)
    (q r : PairState (Fin n)) : nodes (R.pairBackGuard s q r) ≤ 11+2*B := by
  rw [Row.pairBackGuard, nodes_inf]
  have h₀ := backGuard_le R h s q.1 r.1 0
  have h₁ := backGuard_le R h s q.2 r.2 1
  omega

theorem equalityGuard_le (s : Shape 2) :
    nodes (WordEqualityAutomaton.equalityGuard (L := L) (P := P) 0 1 s) ≤ 3 := by
  unfold WordEqualityAutomaton.equalityGuard
  split <;> split
  all_goals first | exact (by decide : 1 ≤ 3) | exact Nat.le_refl 3

theorem sharedGuard_le (R : Row L P n) (h : RowSize R B) (s : Shape 2)
    (q r : PairState (Fin n)) : nodes (R.sharedGuard s q r) ≤ 19+2*B := by
  unfold Row.sharedGuard
  split
  · rw [nodes_inf]
    have h₀ := equalityGuard_le (L := L) (P := P) s
    have h₁ := pairBackGuard_le R h s q r
    omega
  · change 1 ≤ _
    omega

theorem switchGuard_le (R : Row L P n) (h : RowSize R B) (s : Shape 2)
    (q r : PairState (Fin n)) (seed last : P) (first : Bool) :
    nodes (R.switchGuard s q r seed last first) ≤ 6+B+n*(4+n*(24+4*B)) := by
  unfold Row.switchGuard
  rw [nodes_inf]
  have hbody (z z' : Fin n) :
      nodes ((R.left z q.1).relabel (Sum.inl : P → P ⊕ Fin (arity 2 s)) ⊓
        ((R.right z' q.2).relabel Sum.inl ⊓ R.pairBackGuard s (z,z') r)) ≤ 21+4*B := by
    simp only [nodes_inf, nodes_relabel]
    have hl := h.left z q.1
    have hr := h.right z' q.2
    have hp := pairBackGuard_le R h s (z,z') r
    omega
  have hi (z : Fin n) := nodes_any_le n (21+4*B) _ (hbody z)
  have ho := nodes_any_le n (1+n*(3+(21+4*B))) _ hi
  simp only [guardAt, nodes_relabel]
  have hg := h.guard
  simp only [show 3+(21+4*B) = 24+4*B by omega,
    show 3+(1+n*(24+4*B)) = 4+n*(24+4*B) by omega] at ho
  omega

theorem raw_initial_le (R : Row L P n) (h : RowSize R B) (e : Ends n) (seed last : P) (first : Bool)
    (q : Fin (states n).length) : nodes ((R.raw e seed last first).initial q) ≤ guardBound n B := by
  change nodes (R.initialGuard e last (stateAt n q)) ≤ _
  unfold Row.initialGuard
  split
  · change 1 ≤ _
    unfold guardBound
    omega
  · simp only [nodes_inf, dataAt, nodes_relabel]
    have hl := h.data (stateAt n q).2.1 e.leftEnd
    have hr := h.data (stateAt n q).2.2 e.rightEnd
    unfold guardBound
    omega

theorem raw_final_le (R : Row L P n) (h : RowSize R B) (e : Ends n) (seed last : P) (first : Bool)
    (q : Fin (states n).length) : nodes ((R.raw e seed last first).final q) ≤ guardBound n B := by
  change nodes (R.finalGuard e seed last first (stateAt n q)) ≤ _
  unfold Row.finalGuard
  split
  · split
    · change 3 ≤ _
      unfold guardBound
      omega
    · change 1 ≤ _
      unfold guardBound
      omega
  · simp only [nodes_inf, guardAt, nodes_relabel]
    have hl := h.left e.leftStart (stateAt n q).2.1
    have hr := h.right e.rightStart (stateAt n q).2.2
    have hg := h.guard
    unfold guardBound
    omega

theorem raw_step_le (R : Row L P n) (h : RowSize R B) (e : Ends n) (seed last : P) (first : Bool)
    (s : Shape 2) (q r : Fin (states n).length) : nodes ((R.raw e seed last first).step s q r) ≤ guardBound n B := by
  change nodes (R.stepGuard s seed last first (stateAt n q) (stateAt n r)) ≤ _
  unfold Row.stepGuard
  split
  · have hh := sharedGuard_le R h s (stateAt n q).2 (stateAt n r).2
    unfold guardBound
    omega
  · have hh := switchGuard_le R h s (stateAt n q).2 (stateAt n r).2 seed last first
    unfold guardBound
    omega
  · have hh := pairBackGuard_le R h s (stateAt n q).2 (stateAt n r).2
    unfold guardBound
    omega
  · change 1 ≤ _
    unfold guardBound
    omega

theorem nodes_compile_le (R : Row L P n) (h : RowSize R B) (e : Ends n) (seed last : P) (first : Bool)
    (columns : Nat → Sparse P 2) (one : P) (T : Nat) (positive : Bool) :
    let N := 2*n*n
    let G := guardBound n B
    nodes (ExactGuardedRunFormula.compile R e seed last first columns one T positive) ≤
      19+N*(14+2*G)+T*(8+N*(16+2*N*(9+G)))+N*(9+G)+5*((T+1)*N) := by
  have hh := ExactColumnRunFormula.nodes_compile_le (R.raw e seed last first) columns one T positive
    (raw_initial_le R h e seed last first) (raw_final_le R h e seed last first)
    (raw_step_le R h e seed last first)
  simpa only [length_states] using hh

end NSSE.ExactGuardedRunSize
