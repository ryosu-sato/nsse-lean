import NSSE.ExplicitCapTerminal

/-! State bounds for the actual original-cap G/R preprocessing. -/

namespace NSSE.ExplicitCapFrontEndSize

open FiniteSOARankDecision FiniteDFAOperations FiniteDFAConcat FiniteCapFrontEnd
open DirectRankStateTower

variable {α : Type}

theorem concat_count (A B : InputDFA α) : (concat A B).count = 2^(A.count+B.count) := by
  change (SymbolicComplement.masks (states A.count B.count).length).length = _
  rw [SymbolicComplement.length_masks]
  simp [states]

theorem union_count (A B : InputDFA α) : (union A B).count = A.count*B.count := rfl

theorem unions_exp (as : List (InputDFA α)) (f : InputDFA α → Nat)
    (h : ∀ A ∈ as, A.count ≤ 2^(f A)) :
    (unions as).count ≤ 2^((as.map f).sum) := by
  induction as with
  | nil => exact Nat.le_refl 1
  | cons A as ih =>
    have ht := ih (fun B hb => h B (by simp [hb]))
    have ha := h A (by simp)
    simpa only [unions, union_count, List.map_cons, List.sum_cons] using mul_exp ha ht

theorem mapped_unions_exp {β : Type*} (as : List β) (g : β → InputDFA α) (f : β → Nat)
    (h : ∀ a ∈ as, (g a).count ≤ 2^(f a)) :
    (unions (as.map g)).count ≤ 2^((as.map f).sum) := by
  induction as with
  | nil => exact Nat.le_refl 1
  | cons a as ih =>
    have ht := ih (fun b hb => h b (by simp [hb]))
    have ha := h a (by simp)
    simpa only [List.map_cons, unions, union_count, List.sum_cons] using mul_exp ha ht

theorem G_count (E : Input α) : (G E).count ≤ 2^((E.routes.map (fun A => A.count+1)).sum) := by
  apply mapped_unions_exp E.routes rightIdeal (fun A => A.count+1)
  intro A _
  rw [rightIdeal, concat_count]
  exact Nat.le_refl _

theorem filter_sum_le {β : Type*} (as : List β) (p : β → Bool) (f : β → Nat) :
    ((as.filter p).map f).sum ≤ (as.map f).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    cases hp : p a <;> simp [List.filter_cons, hp] <;> omega

variable [Fintype α] [DecidableEq α]

theorem componentRegular_count (c : Component α) :
    (componentRegular c).count ≤ 2^(2*c.left.count+c.right.count) := by
  change c.left.count*(concat c.left (prefixClosure c.right)).count ≤ _
  rw [concat_count]
  have h := mul_exp (self_le_exp c.left.count)
    (Nat.le_refl (2^(c.left.count+c.right.count)))
  rw [show c.left.count+(c.left.count+c.right.count) = 2*c.left.count+c.right.count by omega] at h
  exact h

theorem R_count (E : Input α) :
    (R E).count ≤ 2^((E.rows.map (fun c => 2*c.left.count+c.right.count)).sum) := by
  have h := mapped_unions_exp (prepared E).rows componentRegular
    (fun c => 2*c.left.count+c.right.count) (fun c _ => componentRegular_count c)
  apply h.trans
  apply exp_mono
  exact filter_sum_le E.rows (fun c => nonempty c.right) _

end NSSE.ExplicitCapFrontEndSize
