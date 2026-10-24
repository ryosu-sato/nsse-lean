import NSSE.ExistentialScalarPrenexSize
import Mathlib.Tactic.GCongr

/-! # One uniform polynomial node bound for every actual signed array atom -/

namespace NSSE.UniformArrayAtomBound

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks ExactReachabilitySize
open ExactGuardedRunSize FiniteWordCoordinates

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n B : Nat}

structure RowBudget (R : Row L P n) (B : Nat) : Prop extends RowSize R B where
  states : n ≤ B
  initial : ∀ s, nodes (R.initial s) ≤ B
  final : ∀ s, nodes (R.final s) ≤ B

def table (N G T : Nat) :=
  19+N*(14+2*G)+T*(8+N*(16+2*N*(9+G)))+N*(9+G)+5*((T+1)*N)

def atomBound (B T : Nat) :=
  5+24*T + (3+B*(8+2*B)) + (B+2) + table (2*B*B) (109+5*guardBound B (B+3)) T

theorem table_mono {N N' G G' T T' : Nat} (hN : N ≤ N') (hG : G ≤ G') (hT : T ≤ T') :
    table N G T ≤ table N' G' T' := by unfold table; gcongr

theorem guardBound_mono {n n' B B' : Nat} (hn : n ≤ n') (hB : B ≤ B') :
    guardBound n B ≤ guardBound n' B' := by unfold guardBound; gcongr

theorem atomBound_mono {B B' T T' : Nat} (hB : B ≤ B') (hT : T ≤ T') :
    atomBound B T ≤ atomBound B' T' := by
  unfold atomBound
  gcongr
  apply table_mono
  · gcongr
  · apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    exact guardBound_mono hB (by omega)
  · exact hT

theorem rowSize_weaken (R : Row L P n) (h : RowSize R B) : RowSize R (B+3) where
  data s t := Nat.le_trans (h.data s t) (by omega)
  left s t := Nat.le_trans (h.left s t) (by omega)
  right s t := Nat.le_trans (h.right s t) (by omega)
  guard := Nat.le_trans h.guard (by omega)

theorem identity_size (R : Row L P n) (h : RowSize R B) :
    RowSize (BlockRelationPresentation.identityMarkers R) (B+3) := by
  constructor
  · intro s t
    exact Nat.le_trans (h.data s t) (by omega)
  · intro s t
    change nodes (if s = t then (⊤ : L.Formula P) else ⊥) ≤ B+3
    split <;> simp [nodes, BoundedFormula.not]
  · intro s t
    change nodes (if s = t then (⊤ : L.Formula P) else ⊥) ≤ B+3
    split <;> simp [nodes, BoundedFormula.not]
  · change 3 ≤ B+3
    omega

theorem guarded_le (R : Row L P n) (hn : n ≤ B) (h : RowSize R (B+3))
    (e : Ends n) (seed last : P) (first : Bool) (zero one : P)
    (q T : Nat) (args : Fin 2 → Fin q) (positive : Bool) :
    nodes (FiniteArrayHFormula.compile R e seed last first zero one q T args positive) ≤ atomBound B T := by
  have hh := FiniteArrayHFormula.nodes_compile_le R h e seed last first zero one q T args positive
  change nodes _ ≤ table (2*n*n) (109+5*guardBound n (B+3)) T at hh
  have ht : table (2*n*n) (109+5*guardBound n (B+3)) T ≤ table (2*B*B) (109+5*guardBound B (B+3)) T := by
    apply table_mono
    · gcongr
    · exact Nat.add_le_add_left (Nat.mul_le_mul_left 5 (guardBound_mono hn le_rfl)) 109
    · rfl
  unfold atomBound
  omega

theorem initial_le (R : Row L P n) (h : RowBudget R B) (seed : P) (s : Fin n) :
    nodes (BlockRelationPresentation.initialFormula R seed s) ≤ 1+B*(8+2*B) := by
  have hb (z : Fin n) : nodes (R.initial z ⊓ dataAt (R.data z s) id seed) ≤ 5+2*B := by
    simp only [nodes_inf, dataAt, nodes_relabel]
    have hi := h.initial z
    have hd := h.data z s
    omega
  have hh := nodes_any_le n (5+2*B) _ hb
  change nodes (BlockRelationPresentation.initialFormula R seed s) ≤ _ at hh
  calc
    _ ≤ 1+n*(3+(5+2*B)) := hh
    _ ≤ 1+B*(8+2*B) := by
      rw [show 3+(5+2*B) = 8+2*B by omega]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h.states) 1

theorem block_le (R : Row L P n) (h : RowBudget R B) (seed last zero one : P) (q T : Nat)
    {a : Nat} (r : BlockRelationPresentation.Rel n a) (args : Fin a → Fin q) (positive : Bool) :
    nodes (FiniteArrayBlockFormula.compile R seed last zero one q T r args positive) ≤ atomBound B T := by
  cases r with
  | block s t =>
    exact guarded_le (BlockRelationPresentation.identityMarkers R) h.states (identity_size R h.toRowSize)
      ⟨s,t,s,t⟩ last last false zero one q T (fun _ => args 0) positive
  | guarded e first => exact guarded_le R h.states (rowSize_weaken R h.toRowSize) e seed last first zero one q T args positive
  | initial s =>
    have hs := nodes_signed_le positive ((BlockRelationPresentation.initialFormula R seed s).relabel
      (Sum.inl : P → Params P q T))
    rw [nodes_relabel] at hs
    have hi := initial_le R h seed s
    change nodes (ExactReachabilityTable.signed positive _) ≤ _
    unfold atomBound
    omega
  | final s =>
    have hs := nodes_signed_le positive ((R.final s).relabel (Sum.inl : P → Params P q T))
    rw [nodes_relabel] at hs
    have hf := h.final s
    change nodes (ExactReachabilityTable.signed positive _) ≤ _
    unfold atomBound
    omega

theorem absence_le (last zero one : P) (q T : Nat) (i : Fin q) (positive : Bool) :
    nodes (FiniteArrayAbsenceFormula.compile (L := L) last zero one q T i positive) ≤ atomBound B T := by
  have h := nodes_signed_le positive (FiniteArrayAbsenceFormula.matrix (L := L) last zero one q T i)
  rw [FiniteArrayAbsenceFormula.nodes_matrix] at h
  unfold FiniteArrayAbsenceFormula.compile atomBound
  omega

theorem equality_le (zero one : P) (q T : Nat) (i j : Fin q) (positive : Bool) :
    nodes (FiniteArrayEqualityFormula.compile (L := L) zero one q T i j positive) ≤ atomBound B T := by
  have h := nodes_signed_le positive (FiniteArrayEqualityFormula.matrix (L := L) zero one q T i j)
  rw [FiniteArrayEqualityFormula.nodes_matrix] at h
  unfold FiniteArrayEqualityFormula.compile atomBound
  omega

theorem relation_le {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowBudget (rows i) B) (hc : RowBudget C B) (seed last zero one : P) (q T : Nat)
    {a : Nat} (r : UnifiedBlockPresentation.Rel ns c a) (args : Fin a → Fin q) (positive : Bool) :
    nodes (FiniteArrayRelationCompiler.compile rows C seed last zero one q T r args positive) ≤ atomBound B T := by
  cases r with
  | row i r => exact block_le (rows i) (hr i) seed last zero one q T r args positive
  | candidate r => exact block_le C hc seed last zero one q T r args positive
  | noA => exact absence_le last zero one q T (args 0) positive

end NSSE.UniformArrayAtomBound
