import NSSE.MultiConstructorTrees

/-! Finite trees over the same varying-arity signature, and their faithful
embedding into the arbitrary-tree model. Nullary heads are allowed. -/
namespace NSSE.MultiConstructorFiniteTrees
open MultiConstructorTrees (Label)

inductive Tree {H : Type*} (arity : H → Nat)
  | bot
  | top
  | node (head : H) (children : Fin (arity head) → Tree arity)

variable {H : Type*} {arity : H → Nat}

inductive Below : Tree arity → Tree arity → Prop
  | bot (t) : Below .bot t
  | top (t) : Below t .top
  | node {h} {a b : Fin (arity h) → Tree arity}
      (children : ∀ i, Below (a i) (b i)) : Below (.node h a) (.node h b)

theorem below_refl (a : Tree arity) : Below a a := by
  induction a with
  | bot => exact .bot _
  | top => exact .top _
  | node h a ih => exact .node ih

theorem below_trans {a b c : Tree arity} (hab : Below a b) (hbc : Below b c) :
    Below a c := by
  induction hab generalizing c with
  | bot b => exact .bot _
  | top a => cases hbc; exact .top _
  | node hab ih =>
    cases hbc with
    | top _ => exact .top _
    | node hbc => exact .node (fun i => ih i (hbc i))

theorem below_antisymm {a b : Tree arity} (hab : Below a b) (hba : Below b a) :
    a = b := by
  induction hab with
  | bot b => cases hba; rfl
  | top a => cases hba; rfl
  | node hab ih =>
    cases hba with
    | node hba =>
      congr 1
      exact funext (fun i => ih i (hba i))

instance : PartialOrder (Tree arity) where
  le := Below
  le_refl := below_refl
  le_trans _ _ _ := below_trans
  le_antisymm _ _ := below_antisymm

instance : OrderBot (Tree arity) where
  bot := .bot
  bot_le := Below.bot

instance : OrderTop (Tree arity) where
  top := .top
  le_top := Below.top

@[simp] theorem node_le_node (h : H) (a b : Fin (arity h) → Tree arity) :
    Tree.node h a ≤ Tree.node h b ↔ ∀ i, a i ≤ b i := by
  constructor
  · intro h; cases h with | node h => exact h
  · exact Below.node

theorem node_head_eq {h k : H} {a : Fin (arity h) → Tree arity}
    {b : Fin (arity k) → Tree arity} (hab : Tree.node h a ≤ Tree.node k b) :
    h = k := by
  cases hab
  rfl

theorem node_not_le_bot (h : H) (a : Fin (arity h) → Tree arity) :
    ¬ Tree.node h a ≤ ⊥ := by intro h; cases h

theorem top_not_le_node (h : H) (a : Fin (arity h) → Tree arity) :
    ¬ ⊤ ≤ Tree.node h a := by intro h; cases h

def embed : Tree arity → MultiConstructorTrees.Tree arity
  | .bot => ⊥
  | .top => ⊤
  | .node h a => MultiConstructorTrees.Tree.node h (fun i => embed (a i))

theorem embed_mono {a b : Tree arity} (hab : a ≤ b) : embed a ≤ embed b := by
  induction hab with
  | bot _ => exact bot_le
  | top _ => exact le_top
  | node h ih => exact (MultiConstructorTrees.Tree.node_le_node _ _ _).mpr ih

theorem le_of_embed_le {a b : Tree arity} (hab : embed a ≤ embed b) : a ≤ b := by
  induction a generalizing b with
  | bot => exact bot_le
  | top =>
    cases b with
    | bot =>
      have bad : Label.Below (.top : Label H) .bot := hab []
      simp [Label.Below] at bad
    | top => exact le_rfl
    | node h b => exact False.elim (MultiConstructorTrees.Tree.top_not_le_node h _ hab)
  | node h a ih =>
    cases b with
    | bot => exact False.elim (MultiConstructorTrees.Tree.node_not_le_bot h _ hab)
    | top => exact le_top
    | node k b =>
      have hk := MultiConstructorTrees.Tree.node_head_eq hab
      subst k
      exact Below.node (fun i => ih i ((MultiConstructorTrees.Tree.node_le_node h _ _).mp hab i))

@[simp] theorem embed_le_embed (a b : Tree arity) : embed a ≤ embed b ↔ a ≤ b :=
  ⟨le_of_embed_le,embed_mono⟩

theorem embed_injective : Function.Injective (embed (arity := arity)) := by
  intro a b hab
  exact le_antisymm (le_of_embed_le (le_of_eq hab)) (le_of_embed_le (le_of_eq hab.symm))

def height : Tree arity → Nat
  | .bot => 0
  | .top => 0
  | .node _ a => Finset.univ.sup (fun i => height (a i)) + 1

theorem child_height_lt (h : H) (a : Fin (arity h) → Tree arity) (i : Fin (arity h)) :
    height (a i) < height (.node h a) :=
  Nat.lt_succ_of_le (Finset.le_sup (f := fun i => height (a i)) (Finset.mem_univ i))

theorem no_self_node (h : H) (hp : 0 < arity h) (t : Tree arity) :
    t ≠ .node h (fun _ => t) := by
  intro he
  have hh := child_height_lt h (fun _ => t) ⟨0,hp⟩
  rw [← he] at hh
  exact Nat.lt_irrefl _ hh

end NSSE.MultiConstructorFiniteTrees
