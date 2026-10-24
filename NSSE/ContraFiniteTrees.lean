import NSSE.ContraTrees

/-! # Finite contravariant trees: structural order and embedding into raw trees

Inductive finite trees `⊥ | ⊤ | f(t₁,…,t_d)` with the STRUCTURAL contravariant
order (an inductive relation), proved to be a partial order by an order embedding
`toC` into the raw trees of `NSSE.ContraTrees` with their original coinductive order.
-/

namespace NSSE.ContraFiniteTrees

open AbsorbingSubtypeTrees ContraTrees

variable {d : Nat}

/-- Finite trees for polarity `POL` (the polarity only selects the order). -/
inductive FTree {d : Nat} (POL : Polarity d) : Type
  | bot : FTree POL
  | top : FTree POL
  | node (children : Fin d → FTree POL) : FTree POL

variable {POL : Polarity d}

/-- The structural non-structural-subtyping order on finite trees. -/
inductive Below (POL : Polarity d) : FTree POL → FTree POL → Prop
  | bot (t : FTree POL) : Below POL .bot t
  | top (t : FTree POL) : Below POL t .top
  | node {a b : Fin d → FTree POL}
      (hcov : ∀ i, POL i = false → Below POL (a i) (b i))
      (hcon : ∀ i, POL i = true → Below POL (b i) (a i)) : Below POL (.node a) (.node b)

/-- The embedding of finite trees into raw trees. -/
def toC : FTree POL → CTree POL
  | .bot => ⊥
  | .top => ⊤
  | .node c => CTree.node (fun i => toC (c i))

@[simp] theorem toC_bot : toC (.bot : FTree POL) = ⊥ := rfl
@[simp] theorem toC_top : toC (.top : FTree POL) = ⊤ := rfl
@[simp] theorem toC_node (c : Fin d → FTree POL) :
    toC (.node c) = CTree.node (fun i => toC (c i)) := rfl

theorem toC_mono {a b : FTree POL} (h : Below POL a b) : toC a ≤ toC b := by
  induction h with
  | bot t => exact bot_le
  | top t => exact le_top
  | node _ _ ihcov ihcon =>
      exact (CTree.node_le_node _ _).mpr (fun i => ⟨ihcon i, ihcov i⟩)

private theorem below_of_toC (a : FTree POL) : ∀ b : FTree POL,
    (toC a ≤ toC b → Below POL a b) ∧ (toC b ≤ toC a → Below POL b a) := by
  induction a with
  | bot =>
      intro b
      refine ⟨fun _ => .bot b, fun h => ?_⟩
      cases b with
      | bot => exact .bot _
      | top => exact absurd h not_top_le_bot
      | node e => exact absurd h (not_node_le_bot _)
  | top =>
      intro b
      refine ⟨fun h => ?_, fun _ => .top b⟩
      cases b with
      | bot => exact absurd h not_top_le_bot
      | top => exact .top _
      | node e => exact absurd h (not_top_le_node _)
  | node c ih =>
      intro b
      constructor
      · intro h
        cases b with
        | bot => exact absurd h (not_node_le_bot _)
        | top => exact .top _
        | node e =>
            have h' := (CTree.node_le_node _ _).mp h
            exact .node (fun i hp => (ih i (e i)).1 ((h' i).2 hp))
              (fun i hp => (ih i (e i)).2 ((h' i).1 hp))
      · intro h
        cases b with
        | bot => exact .bot _
        | top => exact absurd h (not_top_le_node _)
        | node e =>
            have h' := (CTree.node_le_node _ _).mp h
            exact .node (fun i hp => (ih i (e i)).2 ((h' i).2 hp))
              (fun i hp => (ih i (e i)).1 ((h' i).1 hp))

/-- The structural order agrees with the original order of the image. -/
theorem below_iff (a b : FTree POL) : Below POL a b ↔ toC a ≤ toC b :=
  ⟨toC_mono, (below_of_toC a b).1⟩

theorem toC_injective : Function.Injective (toC : FTree POL → CTree POL) := by
  intro a
  induction a with
  | bot =>
      intro b h
      cases b with
      | bot => rfl
      | top => exact absurd h bot_ne_top
      | node e => exact absurd h.symm (node_ne_bot _)
  | top =>
      intro b h
      cases b with
      | bot => exact absurd h.symm bot_ne_top
      | top => rfl
      | node e => exact absurd h.symm (node_ne_top _)
  | node c ih =>
      intro b h
      cases b with
      | bot => exact absurd h (node_ne_bot _)
      | top => exact absurd h (node_ne_top _)
      | node e =>
          have he := CTree.node_injective h
          congr 1
          funext i
          exact ih i (congrFun he i)

instance : PartialOrder (FTree POL) where
  le := Below POL
  le_refl a := (below_iff a a).mpr le_rfl
  le_trans a b c h₁ h₂ :=
    (below_iff a c).mpr (((below_iff a b).mp h₁).trans ((below_iff b c).mp h₂))
  le_antisymm a b h₁ h₂ :=
    toC_injective (le_antisymm ((below_iff a b).mp h₁) ((below_iff b a).mp h₂))

instance : OrderBot (FTree POL) where
  bot := .bot
  bot_le := Below.bot

instance : OrderTop (FTree POL) where
  top := .top
  le_top := Below.top

@[simp] theorem bot_eq : (FTree.bot : FTree POL) = ⊥ := rfl
@[simp] theorem top_eq : (FTree.top : FTree POL) = ⊤ := rfl

theorem le_iff_below (a b : FTree POL) : a ≤ b ↔ Below POL a b := Iff.rfl

theorem toC_le_iff (a b : FTree POL) : toC a ≤ toC b ↔ a ≤ b := (below_iff a b).symm

/-- `toC` as an order embedding into raw trees with the original order. -/
def toCEmb (POL : Polarity d) : FTree POL ↪o CTree POL :=
  OrderEmbedding.ofMapLEIff toC toC_le_iff

@[simp] theorem toCEmb_apply (a : FTree POL) : toCEmb POL a = toC a := rfl

/-- The contravariant constructor law on finite trees. -/
theorem FTree.node_le_node (a b : Fin d → FTree POL) :
    FTree.node a ≤ FTree.node b ↔ ∀ i, (POL i = true → b i ≤ a i) ∧ (POL i = false → a i ≤ b i) := by
  rw [← toC_le_iff, toC_node, toC_node, CTree.node_le_node]
  simp only [toC_le_iff]

/-! ## Height: finite trees exclude self-referential solutions -/

def height : FTree POL → Nat
  | .bot => 0
  | .top => 0
  | .node c => (Finset.univ.sup (fun i => height (c i))) + 1

theorem child_height_lt (c : Fin d → FTree POL) (i : Fin d) :
    height (c i) < height (.node c) := by
  change height (c i) < (Finset.univ.sup (fun j => height (c j))) + 1
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun j => height (c j)) (Finset.mem_univ i))

theorem no_self_node (hd : 0 < d) (t : FTree POL) : t ≠ FTree.node (fun _ => t) := by
  intro he
  have h := child_height_lt (fun _ : Fin d => t) ⟨0, hd⟩
  rw [← he] at h
  exact Nat.lt_irrefl _ h

end NSSE.ContraFiniteTrees
