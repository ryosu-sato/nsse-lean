import NSSE.MultiVarianceTrees
import NSSE.MultiConstructorGraph

/-! Actual finite or infinite labelled graphs, in the ORIGINAL signed order.
The graph does not carry independent positive and negative values. Its raw
unfolding is wrapped by `MultiVarianceTrees.Tree`, and the simulation rule
reverses the relation exactly at the selected head's negative arguments. -/
namespace NSSE.MultiVarianceGraph
open MultiVarianceEncoding
open MultiConstructorTrees (Label)
open MultiConstructorGraph (Graph)
variable {H Q : Type*} {arity : H → Nat} (pol : Polarity arity)

def unfold (G : Graph arity Q) (q : Q) : MultiVarianceTrees.Tree pol :=
  ⟨MultiConstructorGraph.unfold G q⟩

@[simp] theorem root (G : Graph arity Q) (q : Q) :
    (unfold pol G q).raw.label [] = G.head q := rfl

theorem bot (G : Graph arity Q) (q : Q) (hq : G.head q = .bot) :
    unfold pol G q = ⊥ := by
  apply MultiVarianceTrees.Tree.ext
  exact MultiConstructorGraph.bot G q hq

theorem top (G : Graph arity Q) (q : Q) (hq : G.head q = .top) :
    unfold pol G q = ⊤ := by
  apply MultiVarianceTrees.Tree.ext
  exact MultiConstructorGraph.top G q hq

theorem node (G : Graph arity Q) (q : Q) (h : H) (hq : G.head q = .node h) :
    unfold pol G q = MultiVarianceTrees.node h
      (fun i => unfold pol G (G.next q i.val)) := by
  apply MultiVarianceTrees.Tree.ext
  exact MultiConstructorGraph.node G q h hq

/-- A signed graph simulation in which reversing the two states is meaningful. -/
theorem simulation (G : Graph arity Q) (rel : Q → Q → Prop)
    (heads : ∀ q r, rel q r → G.head q ≤ G.head r)
    (children : ∀ q r, rel q r → ∀ h, G.head q = .node h → G.head r = .node h →
      ∀ i : Fin (arity h), if pol h i then rel (G.next r i.val) (G.next q i.val)
        else rel (G.next q i.val) (G.next r i.val))
    (q r : Q) (hqr : rel q r) : unfold pol G q ≤ unfold pol G r := by
  apply MultiVarianceTrees.coinduction
    (fun a b => ∃ q r, rel q r ∧ a = unfold pol G q ∧ b = unfold pol G r)
    ?_ _ _ ⟨q,r,hqr,rfl,rfl⟩
  rintro a b ⟨q,r,hrel,rfl,rfl⟩
  have hh := heads q r hrel
  cases hq : G.head q with
  | bot => exact Or.inl (bot pol G q hq)
  | top =>
    have hr : G.head r = .top := by
      rw [hq] at hh
      exact le_antisymm le_top hh
    exact Or.inr (Or.inl (top pol G r hr))
  | node h =>
    cases hr : G.head r with
    | bot => exact False.elim (Label.node_not_le_bot h (by rwa [hq,hr] at hh))
    | top => exact Or.inr (Or.inl (top pol G r hr))
    | node k =>
      have he : h = k := (Label.node_le_node h k).mp (by rwa [hq,hr] at hh)
      subst k
      refine Or.inr (Or.inr ⟨h,_,_,node pol G q h hq,node pol G r h hr,?_⟩)
      intro i
      have hc := children q r hrel h hq hr i
      cases hp : pol h i <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at hc ⊢
      · exact ⟨_,_,hc,rfl,rfl⟩
      · exact ⟨_,_,hc,rfl,rfl⟩

theorem le_node (G : Graph arity Q) (q : Q) (h : H)
    (t : Fin (arity h) → MultiVarianceTrees.Tree pol)
    (hh : G.head q ≤ .node h)
    (hc : ∀ i, if pol h i then t i ≤ unfold pol G (G.next q i.val)
      else unfold pol G (G.next q i.val) ≤ t i) :
    unfold pol G q ≤ MultiVarianceTrees.node h t := by
  cases hq : G.head q with
  | bot => rw [bot pol G q hq]; exact bot_le
  | top => exact False.elim (Label.top_not_le_node h (by rwa [hq] at hh))
  | node k =>
    have he : k = h := (Label.node_le_node k h).mp (by rwa [hq] at hh)
    subst k
    rw [node pol G q h hq,MultiVarianceTrees.node_le_node]
    exact hc

theorem node_le (G : Graph arity Q) (q : Q) (h : H)
    (t : Fin (arity h) → MultiVarianceTrees.Tree pol)
    (hh : .node h ≤ G.head q)
    (hc : ∀ i, if pol h i then unfold pol G (G.next q i.val) ≤ t i
      else t i ≤ unfold pol G (G.next q i.val)) :
    MultiVarianceTrees.node h t ≤ unfold pol G q := by
  cases hq : G.head q with
  | bot => exact False.elim (Label.node_not_le_bot h (by rwa [hq] at hh))
  | top => rw [top pol G q hq]; exact le_top
  | node k =>
    have he : h = k := (Label.node_le_node h k).mp (by rwa [hq] at hh)
    subst k
    rw [node pol G q h hq,MultiVarianceTrees.node_le_node]
    exact hc

end NSSE.MultiVarianceGraph
