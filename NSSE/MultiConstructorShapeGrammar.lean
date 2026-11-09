import NSSE.MultiConstructorShapeHead

/-! Actual finite unfolding of the two-sided shape grammar. The head join
makes same-fuel refinement monotonic on every state. Completeness of the
input-only quadratic cutoff is proved separately. -/
namespace NSSE.MultiConstructorShapeGrammar
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorShapeTokens
open MultiConstructorShapeHead MultiConstructorFiniteTrees
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def unfold (phi : Constraints arity n) : Nat → State n → Tree arity
  | 0, _ => .bot
  | k+1, s => match head phi s with
    | .bot => .bot
    | .top => .top
    | .node h => .node h (fun i => unfold phi k (next phi s i.val))

theorem monotone (phi : Constraints arity n) (k : Nat) (s t : State n) (hst : Refines s t) :
    unfold phi k s ≤ unfold phi k t := by
  induction k generalizing s t with
  | zero => exact le_rfl
  | succ k ih =>
    have hh := MultiConstructorShapeHead.monotone phi s t hst
    cases hhs : head phi s with
    | bot => simp only [unfold,hhs]; exact bot_le
    | top =>
      have hht : head phi t = .top := le_antisymm le_top (by simpa only [hhs] using hh)
      simpa only [unfold,hhs,hht] using (le_rfl : (⊤ : Tree arity) ≤ ⊤)
    | node h =>
      cases hht : head phi t with
      | bot =>
        rw [hhs,hht] at hh
        exact False.elim (MultiConstructorTrees.Label.node_not_le_bot h hh)
      | top => simp only [unfold,hht]; exact le_top
      | node g =>
        rw [hhs,hht] at hh
        have he : h = g := (MultiConstructorTrees.Label.node_le_node h g).mp hh
        subst g
        simp only [unfold,hhs,hht]
        exact (node_le_node h _ _).mpr (fun i => ih _ _ (next_refines phi s t hst i.val))

theorem height_le (phi : Constraints arity n) (k : Nat) (s : State n) : height (unfold phi k s) ≤ k := by
  induction k generalizing s with
  | zero => exact le_rfl
  | succ k ih =>
    cases he : head phi s with
    | bot => simp [unfold,he,height]
    | top => simp [unfold,he,height]
    | node h =>
      simp only [unfold,he,height]
      exact Nat.add_le_add_right (Finset.sup_le (fun i _ => ih (next phi s i.val))) 1

def model (phi : Constraints arity n) (x : Fin n) : Tree arity := unfold phi (n*n+1) (initial phi x)

theorem model_height (phi : Constraints arity n) (x : Fin n) : height (model phi x) ≤ n*n+1 := height_le phi _ _

end NSSE.MultiConstructorShapeGrammar
