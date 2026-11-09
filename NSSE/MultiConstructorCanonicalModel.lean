import NSSE.MultiConstructorLowerHead
import NSSE.MultiConstructorGraph

/-! A computable finite graph gives an actual arbitrary-tree model of
every clash-free original input. Its states are lower-token subsets. -/
namespace NSSE.MultiConstructorCanonicalModel
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorTrees
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def graph (phi : Constraints arity n) : MultiConstructorGraph.Graph arity (Tokens n) :=
  ⟨MultiConstructorLowerHead.head phi,lowerNext phi⟩

def tree (phi : Constraints arity n) (S : Tokens n) : Tree arity := MultiConstructorGraph.unfold (graph phi) S

def model (phi : Constraints arity n) (x : Fin n) : Tree arity := tree phi (down phi {x})

theorem tree_mono (phi : Constraints arity n) (S T : Tokens n) (hst : S ⊆ T) : tree phi S ≤ tree phi T := by
  exact MultiConstructorGraph.simulation (graph phi) (graph phi) (fun S T => S ⊆ T)
    (MultiConstructorLowerHead.head_mono phi)
    (fun S T hst _ _ _ i => MultiConstructorLowerHead.next_mono phi S T hst i.val) S T hst

theorem down_bound (phi : Constraints arity n) (x v : Fin n) (hv : v ∈ down phi {x}) : Support phi v x := by
  obtain ⟨t,ht,hvt⟩ := (mem_down phi {x} v).mp hv
  exact (Finset.mem_singleton.mp ht) ▸ hvt

theorem down_self (phi : Constraints arity n) (x : Fin n) : x ∈ down phi {x} :=
  (mem_down phi {x} x).mpr ⟨x,Finset.mem_singleton_self x,.refl x⟩

theorem next_below_upper (phi : Constraints arity n) (hn : ¬LabelClash phi) (S : Tokens n)
    (b : Bound arity n) (hb : b ∈ phi.upper) (hs : ∀ v ∈ S, Support phi v b.parent)
    (i : Fin (arity b.head)) : lowerNext phi S i.val ⊆ down phi {b.children i} := by
  intro v hv
  obtain ⟨a,ha,⟨t,ht,hat⟩,j,hji,hvj⟩ := (mem_lowerNext phi S i.val v).mp hv
  have hab : Support phi a.parent b.parent := hat.trans (hs t ht)
  have he : a.head = b.head := by
    by_contra hne
    exact hn (Or.inr (Or.inr (Or.inr ⟨a,ha,b,hb,hab,hne⟩)))
  rcases a with ⟨p,h,cs⟩
  dsimp only at he
  subst h
  have hji' : j = i := Fin.ext hji
  subst j
  exact (mem_down phi {b.children i} v).mpr
    ⟨b.children i,Finset.mem_singleton_self _,hvj.trans (.decomp ha hb hab i)⟩

theorem lower_child_below_next (phi : Constraints arity n) (a : Bound arity n) (ha : a ∈ phi.lower)
    (i : Fin (arity a.head)) : down phi {a.children i} ⊆ lowerNext phi (down phi {a.parent}) i.val := by
  intro v hv
  exact (mem_lowerNext phi (down phi {a.parent}) i.val v).mpr
    ⟨a,ha,⟨a.parent,down_self phi a.parent,.refl a.parent⟩,i,rfl,down_bound phi (a.children i) v hv⟩

theorem upper_satisfied (phi : Constraints arity n) (hn : ¬LabelClash phi)
    (b : Bound arity n) (hb : b ∈ phi.upper) :
    model phi b.parent ≤ MultiConstructorTrees.Tree.node b.head (fun i => model phi (b.children i)) := by
  apply MultiConstructorGraph.le_node (graph phi) (down phi {b.parent}) b.head
  · exact MultiConstructorLowerHead.below_upper phi hn _ b hb (down_bound phi b.parent)
  · intro i
    exact tree_mono phi _ _ (next_below_upper phi hn _ b hb (down_bound phi b.parent) i)

theorem lower_satisfied (phi : Constraints arity n) (a : Bound arity n) (ha : a ∈ phi.lower) :
    MultiConstructorTrees.Tree.node a.head (fun i => model phi (a.children i)) ≤ model phi a.parent := by
  apply MultiConstructorGraph.node_le (graph phi) (down phi {a.parent}) a.head
  · exact MultiConstructorLowerHead.pin_below phi _ a.head
      ((mem_lowerPins phi _ a.head).mpr ⟨a,ha,⟨a.parent,down_self phi a.parent,.refl a.parent⟩,rfl⟩)
  · intro i
    exact tree_mono phi _ _ (lower_child_below_next phi a ha i)

theorem bot_satisfied (phi : Constraints arity n) (hn : ¬LabelClash phi) (x : Fin n) (hx : x ∈ phi.bot) :
    model phi x = ⊥ :=
  MultiConstructorGraph.bot (graph phi) (down phi {x})
    (MultiConstructorLowerHead.at_bottom phi hn _ x hx (down_bound phi x))

theorem top_satisfied (phi : Constraints arity n) (x : Fin n) (hx : x ∈ phi.top) : model phi x = ⊤ :=
  MultiConstructorGraph.top (graph phi) (down phi {x})
    (MultiConstructorLowerHead.head_top phi _ ⟨x,hx,x,down_self phi x,.refl x⟩)

theorem satisfies (phi : Constraints arity n) (hn : ¬LabelClash phi) : Satisfies allAlgebra phi (model phi) :=
  ⟨upper_satisfied phi hn,lower_satisfied phi,bot_satisfied phi hn,top_satisfied phi⟩

theorem satisfiable_iff (phi : Constraints arity n) : Satisfiable allAlgebra phi ↔ ¬LabelClash phi :=
  ⟨fun ⟨rho,hs⟩ => no_label_clash allAlgebra phi rho hs,fun hn => ⟨model phi,satisfies phi hn⟩⟩

theorem card_states : Fintype.card (Tokens n) = 2^n := by
  simp only [Tokens,Fintype.card_finset,Fintype.card_fin]

end NSSE.MultiConstructorCanonicalModel
