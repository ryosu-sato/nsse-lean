import NSSE.MultiVarianceEncoding

/-! The original mixed-variance structural order for several constructors.
The carrier is unrestricted. The order is presented through the proved
encoding, and is proved to be the greatest structural simulation. -/
namespace NSSE.MultiVarianceTrees
open MultiVarianceEncoding
variable {H : Type*} {arity : H → Nat}

@[ext] structure Tree (pol : Polarity arity) where
  raw : MultiConstructorTrees.Tree arity

variable {pol : Polarity arity}

def encoded (t : Tree pol) : MultiConstructorTrees.Tree arity := encodeAt pol false t.raw

theorem encoded_injective : Function.Injective (encoded (pol := pol)) := by
  intro a b he
  exact Tree.ext ((encode_injective pol false) he)

instance : PartialOrder (Tree pol) := PartialOrder.lift encoded encoded_injective

def bot : Tree pol := ⟨⊥⟩
def top : Tree pol := ⟨⊤⟩
def node (h : H) (c : Fin (arity h) → Tree pol) : Tree pol :=
  ⟨MultiConstructorTrees.Tree.node h (fun i => (c i).raw)⟩

@[simp] theorem encoded_bot : encoded (bot : Tree pol) = ⊥ := encode_bot pol false
@[simp] theorem encoded_top : encoded (top : Tree pol) = ⊤ := encode_top pol false

instance : OrderBot (Tree pol) where
  bot := bot
  bot_le t := by change encoded bot ≤ encoded t; rw [encoded_bot]; exact bot_le

instance : OrderTop (Tree pol) where
  top := top
  le_top t := by change encoded t ≤ encoded top; rw [encoded_top]; exact le_top

theorem encoded_node (h : H) (c : Fin (arity h) → Tree pol) :
    encoded (node h c) = MultiConstructorTrees.Tree.node h
      (fun i => encodeAt pol (pol h i) (c i).raw) := by
  simpa only [Bool.false_xor] using encode_node pol false h (fun i => (c i).raw)

theorem encoded_node_variance (h : H) (c : Fin (arity h) → Tree pol) :
    encoded (node h c) = MultiConstructorTrees.Tree.node h
      (fun i => if pol h i then dual (encoded (c i)) else encoded (c i)) := by
  rw [encoded_node]
  congr 1
  funext i
  cases hp : pol h i
  · rfl
  · exact encode_flip pol false (c i).raw

theorem node_le_node (h : H) (a b : Fin (arity h) → Tree pol) :
    node h a ≤ node h b ↔ ∀ i, if pol h i then b i ≤ a i else a i ≤ b i := by
  change encoded (node h a) ≤ encoded (node h b) ↔ _
  rw [encoded_node,encoded_node,MultiConstructorTrees.Tree.node_le_node]
  apply forall_congr'
  intro i
  cases hp : pol h i
  · rfl
  · exact negative_le pol _ _

theorem node_head_eq {h k : H} {a : Fin (arity h) → Tree pol} {b : Fin (arity k) → Tree pol}
    (hab : node h a ≤ node k b) : h = k := by
  change encoded (node h a) ≤ encoded (node k b) at hab
  rw [encoded_node,encoded_node] at hab
  exact MultiConstructorTrees.Tree.node_head_eq hab

theorem node_not_le_bot (h : H) (a : Fin (arity h) → Tree pol) : ¬node h a ≤ ⊥ := by
  change ¬encoded (node h a) ≤ encoded bot
  rw [encoded_node,encoded_bot]
  exact MultiConstructorTrees.Tree.node_not_le_bot h _

theorem top_not_le_node (h : H) (a : Fin (arity h) → Tree pol) : ¬(⊤ : Tree pol) ≤ node h a := by
  change ¬encoded top ≤ encoded (node h a)
  rw [encoded_top,encoded_node]
  exact MultiConstructorTrees.Tree.top_not_le_node h _

theorem top_not_le_bot : ¬(⊤ : Tree pol) ≤ ⊥ := by
  change ¬encoded top ≤ encoded bot
  rw [encoded_top,encoded_bot]
  intro hh
  have hb := hh []
  cases hb with
  | inl h => cases h
  | inr h => rcases h with h | h <;> cases h

theorem root_cases (t : Tree pol) : t = ⊥ ∨ t = ⊤ ∨ ∃ h c, t = node h c := by
  rcases MultiConstructorTrees.Tree.root_cases t.raw with hb | ht | ⟨h,c,hc⟩
  · exact Or.inl (Tree.ext hb)
  · exact Or.inr (Or.inl (Tree.ext ht))
  · exact Or.inr (Or.inr ⟨h,fun i => ⟨c i⟩,Tree.ext hc⟩)

theorem le_unfold (a b : Tree pol) :
    a ≤ b ↔ a = ⊥ ∨ b = ⊤ ∨ ∃ h ca cb, a = node h ca ∧ b = node h cb ∧
      ∀ i, if pol h i then cb i ≤ ca i else ca i ≤ cb i := by
  constructor
  · intro hab
    rcases root_cases a with rfl | rfl | ⟨h,ca,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (le_antisymm le_top hab))
    · rcases root_cases b with rfl | rfl | ⟨k,cb,rfl⟩
      · exact False.elim (node_not_le_bot h ca hab)
      · exact Or.inr (Or.inl rfl)
      · have hk := node_head_eq hab
        subst k
        exact Or.inr (Or.inr ⟨h,ca,cb,rfl,rfl,(node_le_node h ca cb).mp hab⟩)
  · rintro (rfl | rfl | ⟨h,ca,cb,rfl,rfl,hc⟩)
    · exact bot_le
    · exact le_top
    · exact (node_le_node h ca cb).mpr hc

theorem coinduction (R : Tree pol → Tree pol → Prop)
    (step : ∀ a b, R a b → a = ⊥ ∨ b = ⊤ ∨ ∃ h ca cb,
      a = node h ca ∧ b = node h cb ∧ ∀ i, if pol h i then R (cb i) (ca i) else R (ca i) (cb i))
    (a b : Tree pol) (hab : R a b) : a ≤ b := by
  change ∀ w, (encoded a).label w ≤ (encoded b).label w
  intro w
  induction w generalizing a b with
  | nil =>
    rcases step a b hab with rfl | rfl | ⟨h,ca,cb,rfl,rfl,_⟩
    · change (encoded bot).label [] ≤ _
      rw [encoded_bot]; exact bot_le
    · change _ ≤ (encoded top).label []
      rw [encoded_top]; exact le_top
    · rw [encoded_node,encoded_node]
      exact le_rfl
  | cons j w ih =>
    rcases step a b hab with rfl | rfl | ⟨h,ca,cb,rfl,rfl,hc⟩
    · change (encoded bot).label (j::w) ≤ _
      rw [encoded_bot]; exact bot_le
    · change _ ≤ (encoded top).label (j::w)
      rw [encoded_top]; exact le_top
    · rw [encoded_node,encoded_node]
      by_cases hj : j < arity h
      · simp only [MultiConstructorTrees.Tree.node,hj,dif_pos]
        have hh := hc ⟨j,hj⟩
        cases hp : pol h ⟨j,hj⟩
        · simp only [hp,Bool.false_eq_true,if_false] at hh ⊢
          exact ih (ca ⟨j,hj⟩) (cb ⟨j,hj⟩) hh
        · simp only [hp,if_true] at hh ⊢
          rw [show true = !false from rfl,encode_flip_label,encode_flip_label]
          exact (swap_le_swap _ _).mpr (ih (cb ⟨j,hj⟩) (ca ⟨j,hj⟩) hh)
      · simp only [MultiConstructorTrees.Tree.node,hj,dif_neg]
        exact le_rfl

def IsSimulation (R : Tree pol → Tree pol → Prop) : Prop :=
  ∀ a b, R a b → a = ⊥ ∨ b = ⊤ ∨ ∃ h ca cb, a = node h ca ∧ b = node h cb ∧
    ∀ i, if pol h i then R (cb i) (ca i) else R (ca i) (cb i)

theorem le_iff_simulation (a b : Tree pol) :
    a ≤ b ↔ ∃ R : Tree pol → Tree pol → Prop, IsSimulation R ∧ R a b := by
  constructor
  · intro hab
    exact ⟨(· ≤ ·),fun x y h => (le_unfold x y).mp h,hab⟩
  · rintro ⟨R,hs,hr⟩
    exact coinduction R hs a b hr

end NSSE.MultiVarianceTrees
