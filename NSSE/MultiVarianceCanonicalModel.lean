import NSSE.MultiVarianceModelHead
import NSSE.MultiVarianceGraph
import NSSE.MultiVarianceClasses

/-! A concrete regular model of every clash-free original signed flat system.
This proves SAT sufficiency; it does not assume or construct a least original
valuation. The two-set refinement is a relation on graph states only. -/
namespace NSSE.MultiVarianceCanonicalModel
open MultiConstructorConstraints (Bound Constraints)
open MultiVarianceConstraints MultiVarianceEncoding MultiVarianceModelTokens
open MultiConstructorTrees (Label)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity) (phi : Constraints arity n)

def graph : MultiConstructorGraph.Graph arity (State n) where
  head S := MultiVarianceModelHead.head phi S.1
  next S j := match MultiVarianceModelHead.head phi S.1 with
    | .node h => if hj : j < arity h then move pol phi S h ⟨j,hj⟩ else S
    | _ => S

def tree (S : State n) : MultiVarianceTrees.Tree pol :=
  MultiVarianceGraph.unfold pol (graph pol phi) S

def model (x : Fin n) : MultiVarianceTrees.Tree pol := tree pol phi (start pol phi x)

theorem graph_next (S : State n) (h : H) (i : Fin (arity h))
    (hh : (graph pol phi).head S = .node h) :
    (graph pol phi).next S i.val = move pol phi S h i := by
  change MultiVarianceModelHead.head phi S.1 = .node h at hh
  simp only [graph,hh,i.isLt,dif_pos]

theorem tree_mono (S T : State n) (hst : Refines S T) : tree pol phi S ≤ tree pol phi T := by
  apply MultiVarianceGraph.simulation pol (graph pol phi) Refines ?_ ?_ S T hst
  · intro A B hab
    exact MultiVarianceModelHead.head_mono phi A.1 B.1 hab.1
  · intro A B hab h ha hb i
    rw [graph_next pol phi A h i ha,graph_next pol phi B h i hb]
    exact move_refines pol phi A B hab h i

theorem own_down (bounds : List (Bound arity n)) (S : Tokens n)
    (a : Bound arity n) (ha : a ∈ bounds) (hp : a.parent ∈ S) (i : Fin (arity a.head)) :
    down pol phi (a.children i) ⊆ children pol phi bounds S a.head i.val false := by
  intro v hv
  exact (mem_children pol phi bounds S a.head i.val false v).mpr
    ⟨a,ha,hp,rfl,i,rfl,(mem_down pol phi (a.children i) v).mp hv⟩

theorem own_up (bounds : List (Bound arity n)) (S : Tokens n)
    (a : Bound arity n) (ha : a ∈ bounds) (hp : a.parent ∈ S) (i : Fin (arity a.head)) :
    up pol phi (a.children i) ⊆ children pol phi bounds S a.head i.val true := by
  intro v hv
  exact (mem_children pol phi bounds S a.head i.val true v).mpr
    ⟨a,ha,hp,rfl,i,rfl,(mem_up pol phi (a.children i) v).mp hv⟩

theorem lower_move (a : Bound arity n) (ha : a ∈ phi.lower) (i : Fin (arity a.head)) :
    if pol a.head i then
      Refines (move pol phi (start pol phi a.parent) a.head i) (start pol phi (a.children i))
    else Refines (start pol phi (a.children i)) (move pol phi (start pol phi a.parent) a.head i) := by
  rcases a with ⟨p,h,cs⟩
  cases hp : pol h i <;> simp only [move,start,hp,Bool.false_eq_true,if_false,if_true,Refines]
  · constructor
    · exact own_down pol phi phi.lower (down pol phi p) ⟨p,h,cs⟩ ha (down_self pol phi p) i
    · intro v hv
      obtain ⟨q,ds,hb,hq,hdv⟩ :=
        (mem_children_typed pol phi phi.upper (up pol phi p) h i true v).mp hv
      have hd : Support pol phi (cs i) (ds i) :=
        .decompCov ha hb ((mem_up pol phi p q).mp hq) i hp
      exact (mem_up pol phi (cs i) v).mpr (hd.trans hdv)
  · constructor
    · intro v hv
      obtain ⟨q,ds,hb,hq,hvd⟩ :=
        (mem_children_typed pol phi phi.upper (up pol phi p) h i false v).mp hv
      have hd : Support pol phi (ds i) (cs i) :=
        .decompCon ha hb ((mem_up pol phi p q).mp hq) i hp
      exact (mem_down pol phi (cs i) v).mpr (hvd.trans hd)
    · exact own_up pol phi phi.lower (down pol phi p) ⟨p,h,cs⟩ ha (down_self pol phi p) i

theorem upper_move (b : Bound arity n) (hb : b ∈ phi.upper) (i : Fin (arity b.head)) :
    if pol b.head i then
      Refines (start pol phi (b.children i)) (move pol phi (start pol phi b.parent) b.head i)
    else Refines (move pol phi (start pol phi b.parent) b.head i) (start pol phi (b.children i)) := by
  rcases b with ⟨p,h,ds⟩
  cases hp : pol h i <;> simp only [move,start,hp,Bool.false_eq_true,if_false,if_true,Refines]
  · constructor
    · intro v hv
      obtain ⟨q,cs,ha,hq,hvc⟩ :=
        (mem_children_typed pol phi phi.lower (down pol phi p) h i false v).mp hv
      have hd : Support pol phi (cs i) (ds i) :=
        .decompCov ha hb ((mem_down pol phi p q).mp hq) i hp
      exact (mem_down pol phi (ds i) v).mpr (hvc.trans hd)
    · exact own_up pol phi phi.upper (up pol phi p) ⟨p,h,ds⟩ hb (up_self pol phi p) i
  · constructor
    · exact own_down pol phi phi.upper (up pol phi p) ⟨p,h,ds⟩ hb (up_self pol phi p) i
    · intro v hv
      obtain ⟨q,cs,ha,hq,hcv⟩ :=
        (mem_children_typed pol phi phi.lower (down pol phi p) h i true v).mp hv
      have hd : Support pol phi (ds i) (cs i) :=
        .decompCon ha hb ((mem_down pol phi p q).mp hq) i hp
      exact (mem_up pol phi (ds i) v).mpr (hd.trans hcv)

theorem lower_satisfied (a : Bound arity n) (ha : a ∈ phi.lower) :
    MultiVarianceTrees.node a.head (fun i => model pol phi (a.children i)) ≤ model pol phi a.parent := by
  have hh : .node a.head ≤ (graph pol phi).head (start pol phi a.parent) :=
    MultiVarianceModelHead.pin_below phi _ a ha (down_self pol phi a.parent)
  cases hq : (graph pol phi).head (start pol phi a.parent) with
  | bot => exact False.elim (Label.node_not_le_bot a.head (by rwa [hq] at hh))
  | top =>
    change _ ≤ MultiVarianceGraph.unfold pol (graph pol phi) (start pol phi a.parent)
    rw [MultiVarianceGraph.top pol (graph pol phi) _ hq]
    exact le_top
  | node k =>
    have he : a.head = k := (Label.node_le_node a.head k).mp (by rwa [hq] at hh)
    subst k
    change _ ≤ MultiVarianceGraph.unfold pol (graph pol phi) (start pol phi a.parent)
    rw [MultiVarianceGraph.node pol (graph pol phi) _ a.head hq,MultiVarianceTrees.node_le_node]
    intro i
    rw [graph_next pol phi _ a.head i hq]
    have hc := lower_move pol phi a ha i
    cases hp : pol a.head i <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at hc ⊢
    · exact tree_mono pol phi _ _ hc
    · exact tree_mono pol phi _ _ hc

theorem upper_satisfied (hn : ¬LabelClash pol phi) (b : Bound arity n) (hb : b ∈ phi.upper) :
    model pol phi b.parent ≤ MultiVarianceTrees.node b.head (fun i => model pol phi (b.children i)) := by
  have hh : (graph pol phi).head (start pol phi b.parent) ≤ .node b.head :=
    MultiVarianceModelHead.below_upper phi pol hn _ b hb
      (fun v hv => (mem_down pol phi b.parent v).mp hv)
  cases hq : (graph pol phi).head (start pol phi b.parent) with
  | bot =>
    change MultiVarianceGraph.unfold pol (graph pol phi) (start pol phi b.parent) ≤ _
    rw [MultiVarianceGraph.bot pol (graph pol phi) _ hq]
    exact bot_le
  | top => exact False.elim (Label.top_not_le_node b.head (by rwa [hq] at hh))
  | node k =>
    have he : k = b.head := (Label.node_le_node k b.head).mp (by rwa [hq] at hh)
    subst k
    change MultiVarianceGraph.unfold pol (graph pol phi) (start pol phi b.parent) ≤ _
    rw [MultiVarianceGraph.node pol (graph pol phi) _ b.head hq,MultiVarianceTrees.node_le_node]
    intro i
    rw [graph_next pol phi _ b.head i hq]
    have hc := upper_move pol phi b hb i
    cases hp : pol b.head i <;> simp only [hp,Bool.false_eq_true,if_false,if_true] at hc ⊢
    · exact tree_mono pol phi _ _ hc
    · exact tree_mono pol phi _ _ hc

theorem bot_satisfied (hn : ¬LabelClash pol phi) (x : Fin n) (hx : x ∈ phi.bot) :
    model pol phi x = ⊥ := by
  apply MultiVarianceGraph.bot pol (graph pol phi) (start pol phi x)
  exact MultiVarianceModelHead.at_bottom phi pol hn _ x hx
    (fun v hv => (mem_down pol phi x v).mp hv)

theorem top_satisfied (x : Fin n) (hx : x ∈ phi.top) : model pol phi x = ⊤ := by
  apply MultiVarianceGraph.top pol (graph pol phi) (start pol phi x)
  exact MultiVarianceModelHead.head_top phi _ ⟨x,hx,down_self pol phi x⟩

theorem satisfies (hn : ¬LabelClash pol phi) : Satisfies phi (model pol phi) :=
  ⟨upper_satisfied pol phi hn,lower_satisfied pol phi,
    bot_satisfied pol phi hn,top_satisfied pol phi⟩

theorem satisfiable_iff : Satisfiable pol phi ↔ ¬LabelClash pol phi :=
  ⟨fun ⟨rho,hs⟩ => no_label_clash phi rho hs,fun hn => ⟨model pol phi,satisfies pol phi hn⟩⟩

/-- Each value is an unfolding of the SAME explicit graph with 4^n states. -/
theorem regular (x : Fin n) : MultiConstructorRegularTrees.Regular (model pol phi x).raw :=
  ⟨State n,inferInstance,graph pol phi,start pol phi x,rfl⟩

theorem model_state_count : Fintype.card (State n) = 4^n := MultiVarianceModelTokens.card_states

end NSSE.MultiVarianceCanonicalModel
