import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! Explicit finite inspection for deterministic orbits, used for the
state/phase and pair-state/phase drivers of the P0 periodic-tail proof.
The bounds are cardinalities, not supplied eventual-periodicity promises. -/
namespace NSSE.P0FiniteOrbit
variable {Q : Type*} [Fintype Q]

theorem collision (f : Q → Q) (x : Q) :
    ∃ i j : Nat, i < j ∧ j ≤ Fintype.card Q ∧ f^[i] x = f^[j] x := by
  obtain ⟨i,j,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card Q+1) => f^[i.val] x) (by simp)
  have hij : i.val ≠ j.val := fun h => hne (Fin.ext h)
  by_cases hlt : i.val < j.val
  · exact ⟨i.val,j.val,hlt,by omega,he⟩
  · exact ⟨j.val,i.val,by omega,by omega,he.symm⟩

/-- Every visited state occurs within the first card(Q) positions. -/
theorem representative (f : Q → Q) (x : Q) (k : Nat) :
    ∃ i, i < Fintype.card Q ∧ i ≤ k ∧ f^[i] x = f^[k] x := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < Fintype.card Q
    · exact ⟨k,hk,by omega,rfl⟩
    · obtain ⟨i,j,hij,hj,he⟩ := collision f x
      have hjk : j ≤ k := by omega
      have hsmall : k-j+i < k := by omega
      have he' : f^[k-j+i] x = f^[k] x := by
        calc
          f^[k-j+i] x = f^[k-j] (f^[i] x) := Function.iterate_add_apply f _ _ x
          _ = f^[k-j] (f^[j] x) := congrArg (f^[k-j]) he
          _ = f^[k-j+j] x := (Function.iterate_add_apply f _ _ x).symm
          _ = f^[k] x := by rw [Nat.sub_add_cancel hjk]
      obtain ⟨l,hl,hlk,hle⟩ := ih (k-j+i) hsmall
      exact ⟨l,hl,by omega,hle.trans he'⟩

theorem invariant_iff_prefix (f : Q → Q) (x : Q) (P : Q → Prop) :
    (∀ k, P (f^[k] x)) ↔ ∀ k, k < Fintype.card Q → P (f^[k] x) := by
  constructor
  · exact fun h k _ => h k
  · intro h k
    obtain ⟨i,hi,_,he⟩ := representative f x k
    rw [← he]
    exact h i hi

theorem first_failure_lt_card (f : Q → Q) (x : Q) (P : Q → Prop) (k : Nat)
    (hk : ¬ P (f^[k] x)) (hfirst : ∀ i, i < k → P (f^[i] x)) :
    k < Fintype.card Q := by
  obtain ⟨i,hi,hik,he⟩ := representative f x k
  have hik' : i = k := by
    by_contra hne
    have hp := hfirst i (by omega)
    exact hk (he ▸ hp)
  omega

end NSSE.P0FiniteOrbit
