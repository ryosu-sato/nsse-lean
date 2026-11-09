import NSSE.MultiConstructorTailPeriod

/-! The unconditional reset-selector trace is the second component of the
actual compiled branch walk. Before the first empty row it is the raw trace. -/
namespace NSSE.MultiConstructorSelectorTrace
open MultiConstructorConstraints MultiConstructorRawTrace MultiConstructorUnifiedWords
open MultiConstructorUnifiedPrefix MultiConstructorSelectorHead
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def run (phi : Constraints arity n) (reset s : Row n) (w : List (Fin D)) : Row n :=
  w.foldl (fun t i => next phi reset t i.val) s

def trace (phi : Constraints arity n) (x y : Fin n) (reset : Row n)
    (w : List (Fin D)) (k : Nat) : Row n := run phi reset (initial phi x y) (w.take k)

theorem trace_succ (phi : Constraints arity n) (x y : Fin n) (reset : Row n)
    (w : List (Fin D)) (k : Nat) (hk : k < w.length) :
    trace phi x y reset w (k+1) = next phi reset (trace phi x y reset w k) w[k].val := by
  simp only [trace,run,List.take_succ_eq_append_getElem hk,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem walk_selector (C : MultiConstructorBranch.Parameters arity n)
    (s : MultiConstructorBranch.State n) (w : List (Fin D)) :
    (MultiConstructorBranchLocal.walk C s w).2 = run C.input C.reset s.2 w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih (MultiConstructorBranch.successor C s a.val)

theorem before_empty (phi : Constraints arity n) (x y : Fin n) (reset : Row n)
    (w : List (Fin D)) (J : Nat) (hJn : J ≤ w.length)
    (hbefore : ∀ k, k < J → row phi x y w k ≠ (∅,∅)) (k : Nat) (hk : k < J) :
    trace phi x y reset w k = row phi x y w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < w.length := by omega
    rw [trace_succ phi x y reset w k hkn,ih (by omega)]
    have hn : step phi (row phi x y w k) w[k].val ≠ (∅,∅) := by
      rw [← row_succ phi x y w k hkn]
      exact hbefore (k+1) hk
    rw [next_raw phi reset _ _ hn]
    exact (row_succ phi x y w k hkn).symm

theorem at_empty (phi : Constraints arity n) (x y : Fin n) (reset : Row n)
    (w : List (Fin D)) (J : Nat) (hJ : 0 < J) (hJn : J ≤ w.length)
    (hbefore : ∀ k, k < J → row phi x y w k ≠ (∅,∅))
    (he : row phi x y w J = (∅,∅)) : trace phi x y reset w J = reset := by
  have hpred : J-1 < w.length := by omega
  have hj : J-1+1 = J := by omega
  have ht := trace_succ phi x y reset w (J-1) hpred
  rw [hj,before_empty phi x y reset w J hJn hbefore (J-1) (by omega)] at ht
  rw [ht]
  apply next_reset
  rw [← row_succ phi x y w (J-1) hpred,hj]
  exact he

end NSSE.MultiConstructorSelectorTrace
