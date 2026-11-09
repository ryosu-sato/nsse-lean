import NSSE.MultiVarianceShapeHead
import NSSE.MultiVarianceFiniteTrees

/-! Executable finite unfolding of the signed two-sided shape grammar.
Refinement reverses at each negative argument of the CURRENT head; the
comparison is always the original signed order on embedded finite trees. -/
namespace NSSE.MultiVarianceShapeGrammar
open MultiConstructorConstraints (Constraints)
open MultiVarianceEncoding MultiVarianceModelTokens MultiVarianceShapeHead MultiVarianceFiniteTrees
open MultiConstructorFiniteTrees (height)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def unfold (phi : Constraints arity n) : Nat → State n → Value arity
  | 0, _ => .bot
  | k+1, S => match head phi S with
    | .bot => .bot
    | .top => .top
    | .node h => .node h (fun i => unfold phi k (move pol phi S h i))

theorem monotone (phi : Constraints arity n) (k : Nat) (S T : State n) (hst : Refines S T) :
    embed pol (unfold pol phi k S)≤embed pol (unfold pol phi k T) := by
  induction k generalizing S T with
  | zero => exact le_rfl
  | succ k ih =>
    have hh := MultiVarianceShapeHead.monotone phi S T hst
    cases hhs : head phi S with
    | bot => simp only [unfold,hhs,embed_bot]; exact bot_le
    | top =>
      have hht : head phi T=.top := le_antisymm le_top (by simpa only [hhs] using hh)
      simp only [unfold,hhs,hht,embed_top]
      exact le_rfl
    | node h =>
      cases hht : head phi T with
      | bot =>
        rw [hhs,hht] at hh
        exact False.elim (MultiConstructorTrees.Label.node_not_le_bot h hh)
      | top => simp only [unfold,hht,embed_top]; exact le_top
      | node g =>
        rw [hhs,hht] at hh
        have he : h=g := (MultiConstructorTrees.Label.node_le_node h g).mp hh
        subst g
        simp only [unfold,hhs,hht,embed_node,MultiVarianceTrees.node_le_node]
        intro i
        have hc := move_refines pol phi S T hst h i
        cases hp : pol h i <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at hc ⊢
        · exact ih _ _ hc
        · exact ih _ _ hc

theorem height_le (phi : Constraints arity n) (k : Nat) (S : State n) :
    height (unfold pol phi k S)≤k := by
  induction k generalizing S with
  | zero => exact le_rfl
  | succ k ih =>
    cases he : head phi S with
    | bot => simp [unfold,he,height]
    | top => simp [unfold,he,height]
    | node h =>
      simp only [unfold,he,height]
      exact Nat.add_le_add_right (Finset.sup_le (fun i _ => ih (move pol phi S h i))) 1

def model (phi : Constraints arity n) (x : Fin n) : Value arity := unfold pol phi (n*n+1) (start pol phi x)

theorem model_height (phi : Constraints arity n) (x : Fin n) : height (model pol phi x)≤n*n+1 :=
  height_le pol phi _ _

end NSSE.MultiVarianceShapeGrammar
