import NSSE.MultiConstructorTrees

/-! An actual constructor-labelled graph unfolds to the original tree
semantics, with arity stops and extreme-label absorption enforced. -/
namespace NSSE.MultiConstructorGraph
open MultiConstructorTrees
variable {H Q : Type*} {arity : H → Nat}

structure Graph (arity : H → Nat) (Q : Type*) where
  head : Q → Label H
  next : Q → Nat → Q

instance stopsDecision (e : Label H) (i : Nat) : Decidable (Label.Stops arity e i) := by
  cases e <;> dsimp only [Label.Stops] <;> infer_instance

def read (G : Graph arity Q) (q : Q) : List Nat → Label H
  | [] => G.head q
  | i :: w => if @decide (Label.Stops arity (G.head q) i) (stopsDecision _ _) then
      G.head q else read G (G.next q i) w

theorem read_stop (G : Graph arity Q) (q : Q) (i : Nat) (w : List Nat)
    (hs : Label.Stops arity (G.head q) i) : read G q (i::w) = G.head q := by
  simp only [read,decide_eq_true hs,if_true]

theorem read_move (G : Graph arity Q) (q : Q) (i : Nat) (w : List Nat)
    (hs : ¬Label.Stops arity (G.head q) i) : read G q (i::w) = read G (G.next q i) w := by
  simp only [read,decide_eq_false hs,Bool.false_eq_true,if_false]

theorem read_absorbs (G : Graph arity Q) (q : Q) (p : List Nat) (i : Nat) (w : List Nat)
    (hs : Label.Stops arity (read G q p) i) : read G q (p++i::w) = read G q p := by
  induction p generalizing q with
  | nil => exact read_stop G q i w hs
  | cons j p ih =>
    by_cases hj : Label.Stops arity (G.head q) j
    · simp only [List.cons_append,read_stop G q j _ hj]
    · simp only [List.cons_append,read_move G q j _ hj] at hs ⊢
      exact ih (G.next q j) hs

def unfold (G : Graph arity Q) (q : Q) : Tree arity :=
  ⟨read G q,read_absorbs G q⟩

@[simp] theorem root (G : Graph arity Q) (q : Q) : (unfold G q).label [] = G.head q := rfl

theorem bot (G : Graph arity Q) (q : Q) (hq : G.head q = .bot) : unfold G q = ⊥ :=
  MultiConstructorTrees.Tree.eq_bot_of_root _ hq

theorem top (G : Graph arity Q) (q : Q) (hq : G.head q = .top) : unfold G q = ⊤ :=
  MultiConstructorTrees.Tree.eq_top_of_root _ hq

theorem node (G : Graph arity Q) (q : Q) (h : H) (hq : G.head q = .node h) :
    unfold G q = MultiConstructorTrees.Tree.node h (fun i => unfold G (G.next q i.val)) := by
  apply MultiConstructorTrees.Tree.ext
  intro w
  cases w with
  | nil => exact hq
  | cons i w =>
    by_cases hi : i < arity h
    · change read G q (i::w) = _
      rw [read_move G q i w (by simpa only [hq,Label.Stops] using Nat.not_le.mpr hi)]
      simp only [MultiConstructorTrees.Tree.node,hi,dif_pos]
      rfl
    · change read G q (i::w) = _
      rw [read_stop G q i w (by simpa only [hq,Label.Stops] using Nat.le_of_not_gt hi),hq]
      simp [MultiConstructorTrees.Tree.node,hi]

theorem simulation {R : Type*} (G : Graph arity Q) (F : Graph arity R)
    (rel : Q → R → Prop)
    (heads : ∀ q r, rel q r → G.head q ≤ F.head r)
    (children : ∀ q r, rel q r → ∀ h, G.head q = .node h → F.head r = .node h →
      ∀ i : Fin (arity h), rel (G.next q i.val) (F.next r i.val))
    (q : Q) (r : R) (hqr : rel q r) : unfold G q ≤ unfold F r := by
  apply MultiConstructorTrees.Tree.coinduction (fun a b => ∃ q r, rel q r ∧ a = unfold G q ∧ b = unfold F r) ?_ _ _
    ⟨q,r,hqr,rfl,rfl⟩
  rintro a b ⟨q,r,hrel,rfl,rfl⟩
  have hh := heads q r hrel
  cases hq : G.head q with
  | bot => exact Or.inl (bot G q hq)
  | top =>
    have hr : F.head r = .top := by
      rw [hq] at hh
      exact le_antisymm le_top hh
    exact Or.inr (Or.inl (top F r hr))
  | node h =>
    cases hr : F.head r with
    | bot => exact False.elim (Label.node_not_le_bot h (by rwa [hq,hr] at hh))
    | top => exact Or.inr (Or.inl (top F r hr))
    | node k =>
      have he : h = k := (Label.node_le_node h k).mp (by rwa [hq,hr] at hh)
      subst k
      exact Or.inr (Or.inr ⟨h,_,_,node G q h hq,node F r h hr,
        fun i => ⟨_,_,children q r hrel h hq hr i,rfl,rfl⟩⟩)

theorem le_node (G : Graph arity Q) (q : Q) (h : H) (t : Fin (arity h) → Tree arity)
    (hh : G.head q ≤ .node h) (hc : ∀ i, unfold G (G.next q i.val) ≤ t i) :
    unfold G q ≤ MultiConstructorTrees.Tree.node h t := by
  cases hq : G.head q with
  | bot => rw [bot G q hq]; exact bot_le
  | top => exact False.elim (Label.top_not_le_node h (by rwa [hq] at hh))
  | node k =>
    have he : k = h := (Label.node_le_node k h).mp (by rwa [hq] at hh)
    subst k
    rw [node G q h hq,MultiConstructorTrees.Tree.node_le_node]
    exact hc

theorem node_le (G : Graph arity Q) (q : Q) (h : H) (t : Fin (arity h) → Tree arity)
    (hh : .node h ≤ G.head q) (hc : ∀ i, t i ≤ unfold G (G.next q i.val)) :
    MultiConstructorTrees.Tree.node h t ≤ unfold G q := by
  cases hq : G.head q with
  | bot => exact False.elim (Label.node_not_le_bot h (by rwa [hq] at hh))
  | top => rw [top G q hq]; exact le_top
  | node k =>
    have he : h = k := (Label.node_le_node h k).mp (by rwa [hq] at hh)
    subst k
    rw [node G q h hq,MultiConstructorTrees.Tree.node_le_node]
    exact hc

end NSSE.MultiConstructorGraph
