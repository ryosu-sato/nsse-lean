import NSSE.AbsorbingSubtypeTrees
import Mathlib.Order.Hom.Basic

/-! # Contravariant one-constructor trees: original order and the polarity encoding

Stage S1 of the contravariant extension (notes v1361-v1366, Claude note v163).

One constructor `f` of arity `d` with an ARBITRARY polarity vector
`POL : Fin d → Bool` (`true` = contravariant position).

* Raw trees are absorbing label functions (the carrier
  `AbsorbingSubtypeTrees.Tree d`, labels `0 = ⊥ < 1 = f < 2 = ⊤`), wrapped as
  `CTree POL` so that the covariant pointwise order of the carrier is NOT
  silently inherited.
* The ORIGINAL non-structural contravariant order is DEFINED coinductively, as
  existence of a simulation (`IsSim`, `Le`): a relation `R` with `R s t`, such
  that `R a b` implies `a = ⊥`, or `b = ⊤`, or both are `f`-nodes and the children
  are related covariantly at covariant positions and with swapped arguments at
  contravariant ones. No height, regularity or finiteness premise is used.
* `plabel` is the polarity-aware path label of note v1362 §1; the encoding lemma
  `le_iff_plabel` (v1362 Lemma 1) is PROVED, not assumed, and packaged as the order
  isomorphism `E : CTree POL ≃o Tree d` onto the carrier with its pointwise order.
-/

namespace NSSE.ContraTrees

open AbsorbingSubtypeTrees

variable {d : Nat}

/-! ## Polarity -/

/-- A polarity (variance) vector: `POL i = true` iff position `i` is contravariant. -/
abbrev Polarity (d : Nat) := Fin d → Bool

/-- The polarity of a path: the parity of its contravariant steps (`true` = odd). -/
def pathPol (POL : Polarity d) : List (Fin d) → Bool
  | [] => false
  | i :: p => xor (POL i) (pathPol POL p)

@[simp] theorem pathPol_nil (POL : Polarity d) : pathPol POL [] = false := rfl

@[simp] theorem pathPol_cons (POL : Polarity d) (i : Fin d) (p : List (Fin d)) :
    pathPol POL (i :: p) = xor (POL i) (pathPol POL p) := rfl

theorem pathPol_append (POL : Polarity d) (p q : List (Fin d)) :
    pathPol POL (p ++ q) = xor (pathPol POL p) (pathPol POL q) := by
  induction p with
  | nil => simp
  | cons i p ih => simp [ih, Bool.xor_assoc]

/-! ## Label swap -/

/-- Exchange `⊥` and `⊤`, fix `f`. -/
def swap (a : Label) : Label := ⟨2 - a.val, by omega⟩

@[simp] theorem swap_zero : swap 0 = 2 := rfl
@[simp] theorem swap_one : swap 1 = 1 := rfl
@[simp] theorem swap_two : swap 2 = 0 := rfl

@[simp] theorem swap_swap (a : Label) : swap (swap a) = a := by
  fin_cases a <;> rfl

@[simp] theorem swap_le_swap (a b : Label) : swap a ≤ swap b ↔ b ≤ a := by
  fin_cases a <;> fin_cases b <;> decide

@[simp] theorem swap_eq_one (a : Label) : swap a = 1 ↔ a = 1 := by
  fin_cases a <;> decide

theorem swap_injective : Function.Injective swap := fun a b h => by
  simpa using congrArg swap h

/-- Swap iff the sign is `true` (odd). -/
def sgn (σ : Bool) (a : Label) : Label := if σ then swap a else a

@[simp] theorem sgn_false (a : Label) : sgn false a = a := rfl
@[simp] theorem sgn_true (a : Label) : sgn true a = swap a := rfl
@[simp] theorem sgn_one (σ : Bool) : sgn σ 1 = 1 := by cases σ <;> rfl
@[simp] theorem sgn_sgn (σ : Bool) (a : Label) : sgn σ (sgn σ a) = a := by cases σ <;> simp

theorem sgn_xor (σ τ : Bool) (a : Label) : sgn (xor σ τ) a = sgn σ (sgn τ a) := by
  cases σ <;> cases τ <;> simp

@[simp] theorem sgn_eq_one (σ : Bool) (a : Label) : sgn σ a = 1 ↔ a = 1 := by
  cases σ <;> simp

theorem label_le_two (a : Label) : a ≤ 2 := by fin_cases a <;> decide
theorem label_zero_le (a : Label) : 0 ≤ a := by fin_cases a <;> decide

theorem label_le_cases {a b : Label} (h : a ≤ b) : a = 0 ∨ b = 2 ∨ (a = 1 ∧ b = 1) := by
  fin_cases a <;> fin_cases b <;> simp_all

/-! ## Duality on the covariant carrier -/

/-- Swap every label of a (covariantly ordered) carrier tree. -/
def dual (t : Tree d) : Tree d where
  label w := swap (t.label w)
  absorbs p q h := by
    have h' : t.label p ≠ 1 := fun he => h (by rw [he]; rfl)
    rw [t.absorbs p q h']

@[simp] theorem dual_label (t : Tree d) (w : List (Fin d)) : (dual t).label w = swap (t.label w) :=
  rfl

@[simp] theorem dual_dual (t : Tree d) : dual (dual t) = t := by ext w; simp

theorem dual_injective : Function.Injective (dual : Tree d → Tree d) := fun a b h => by
  simpa using congrArg dual h

/-- `dual` is order reversing (and reflects the order). -/
@[simp] theorem dual_le_dual (a b : Tree d) : dual a ≤ dual b ↔ b ≤ a := by
  constructor
  · intro h w; simpa using h w
  · intro h w; simpa using h w

@[simp] theorem dual_bot : dual (⊥ : Tree d) = ⊤ := by ext w; rfl
@[simp] theorem dual_top : dual (⊤ : Tree d) = ⊥ := by ext w; rfl

theorem dual_node (c : Fin d → Tree d) : dual (node c) = node (fun i => dual (c i)) := by
  ext w; cases w <;> rfl

theorem dual_project (t : Tree d) (p : List (Fin d)) : dual (project t p) = project (dual t) p := by
  ext w; rfl

/-- `dual` as an order isomorphism onto the order dual. -/
def dualIso : Tree d ≃o (Tree d)ᵒᵈ where
  toFun t := OrderDual.toDual (dual t)
  invFun t := dual (OrderDual.ofDual t)
  left_inv t := dual_dual t
  right_inv t := dual_dual (OrderDual.ofDual t)
  map_rel_iff' {a b} := by
    change dual b ≤ dual a ↔ a ≤ b
    exact dual_le_dual b a

/-- `dual` applied iff the sign is `true`. -/
def dualIf (σ : Bool) (t : Tree d) : Tree d := if σ then dual t else t

@[simp] theorem dualIf_false (t : Tree d) : dualIf false t = t := rfl
@[simp] theorem dualIf_true (t : Tree d) : dualIf true t = dual t := rfl
@[simp] theorem dualIf_label (σ : Bool) (t : Tree d) (w : List (Fin d)) :
    (dualIf σ t).label w = sgn σ (t.label w) := by cases σ <;> rfl
@[simp] theorem dualIf_dualIf (σ : Bool) (t : Tree d) : dualIf σ (dualIf σ t) = t := by
  cases σ <;> simp

theorem dualIf_xor (σ τ : Bool) (t : Tree d) : dualIf (xor σ τ) t = dualIf σ (dualIf τ t) := by
  cases σ <;> cases τ <;> simp

/-! ## Raw contravariant trees -/

/-- Raw (possibly infinite) trees for polarity `POL`. The wrapper keeps the
covariant pointwise order of the carrier from being used as the order. -/
@[ext] structure CTree (POL : Polarity d) where
  raw : Tree d

variable {POL : Polarity d}

namespace CTree

/-- Root label: `0 = ⊥`, `1 = f`, `2 = ⊤`. -/
def root (t : CTree POL) : Label := t.raw.label []

/-- The `i`-th child (meaningful when the root is `f`). -/
def child (t : CTree POL) (i : Fin d) : CTree POL := ⟨project t.raw [i]⟩

def node (a : Fin d → CTree POL) : CTree POL := ⟨AbsorbingSubtypeTrees.node (fun i => (a i).raw)⟩

def botT : CTree POL := ⟨⊥⟩
def topT : CTree POL := ⟨⊤⟩

@[simp] theorem root_node (a : Fin d → CTree POL) : (node a).root = 1 := rfl
@[simp] theorem root_botT : (botT : CTree POL).root = 0 := rfl
@[simp] theorem root_topT : (topT : CTree POL).root = 2 := rfl

@[simp] theorem child_node (a : Fin d → CTree POL) (i : Fin d) : (node a).child i = a i := by
  apply CTree.ext
  change project (AbsorbingSubtypeTrees.node (fun j => (a j).raw)) (i :: []) = (a i).raw
  rw [project_node, project_nil]

theorem node_injective : Function.Injective (node : (Fin d → CTree POL) → CTree POL) :=
  fun a b h => funext fun i => by rw [← child_node a i, ← child_node b i, h]

theorem eq_node_of_root (t : CTree POL) (h : t.root = 1) : t = node (fun i => t.child i) := by
  apply CTree.ext
  exact node_of_root t.raw h

theorem eq_botT_of_root (t : CTree POL) (h : t.root = 0) : t = botT :=
  CTree.ext (eq_bot_of_root t.raw h)

theorem eq_topT_of_root (t : CTree POL) (h : t.root = 2) : t = topT :=
  CTree.ext (eq_top_of_root t.raw h)

theorem root_cases (t : CTree POL) : t = botT ∨ (∃ a, t = node a) ∨ t = topT := by
  rcases label_cases t.root with h | h | h
  · exact Or.inl (eq_botT_of_root t h)
  · exact Or.inr (Or.inl ⟨_, eq_node_of_root t h⟩)
  · exact Or.inr (Or.inr (eq_topT_of_root t h))

end CTree

/-! ## The original order, defined coinductively -/

/-- `R` is a simulation for the non-structural contravariant order. -/
def IsSim (POL : Polarity d) (R : CTree POL → CTree POL → Prop) : Prop :=
  ∀ a b, R a b → a.root = 0 ∨ b.root = 2 ∨
    (a.root = 1 ∧ b.root = 1 ∧
      ∀ i, if POL i = true then R (b.child i) (a.child i) else R (a.child i) (b.child i))

/-- The ORIGINAL order: the union of all simulations (greatest fixpoint). -/
def Le (s t : CTree POL) : Prop := ∃ R, IsSim POL R ∧ R s t

theorem le_of_isSim {R : CTree POL → CTree POL → Prop} (hR : IsSim POL R) {s t : CTree POL}
    (h : R s t) : Le s t := ⟨R, hR, h⟩

/-- `Le` is itself a simulation, hence the greatest one. -/
theorem isSim_le : IsSim POL (Le (POL := POL)) := by
  rintro a b ⟨R, hR, h⟩
  rcases hR a b h with h0 | h2 | ⟨ha, hb, hc⟩
  · exact Or.inl h0
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ⟨ha, hb, fun i => ?_⟩)
    have hci := hc i
    split_ifs at hci ⊢
    · exact ⟨R, hR, hci⟩
    · exact ⟨R, hR, hci⟩

/-! ## Polarity-aware path labels (v1362 §1) -/

/-- `plabel POL σ t p`: descend `p`; at a leaf reached at prefix `q` return the
leaf label swapped iff `σ xor pathPol q` is odd; at a node when `p` is exhausted
return `f`. The sign `σ` is the polarity in force at the root. -/
def plabel (POL : Polarity d) : Bool → Tree d → List (Fin d) → Label
  | σ, t, [] => sgn σ (t.label [])
  | σ, t, i :: q =>
      if t.label [] = 1 then plabel POL (xor σ (POL i)) (project t [i]) q
      else sgn σ (t.label [])

@[simp] theorem plabel_nil (σ : Bool) (t : Tree d) : plabel POL σ t [] = sgn σ (t.label []) := rfl

theorem plabel_cons_node (σ : Bool) (t : Tree d) (h : t.label [] = 1) (i : Fin d)
    (q : List (Fin d)) :
    plabel POL σ t (i :: q) = plabel POL (xor σ (POL i)) (project t [i]) q := by
  simp [plabel, h]

theorem plabel_leaf (σ : Bool) (t : Tree d) (h : t.label [] ≠ 1) (p : List (Fin d)) :
    plabel POL σ t p = sgn σ (t.label []) := by
  cases p with
  | nil => rfl
  | cons i q => simp [plabel, h]

/-- The sign only applies a final swap. -/
theorem plabel_eq_sgn (σ : Bool) (t : Tree d) (p : List (Fin d)) :
    plabel POL σ t p = sgn σ (plabel POL false t p) := by
  induction p generalizing σ t with
  | nil => simp
  | cons i q ih =>
      by_cases h : t.label [] = 1
      · rw [plabel_cons_node _ _ h, plabel_cons_node _ _ h, ih, ih (xor false (POL i))]
        simp [sgn_xor]
      · rw [plabel_leaf _ _ h, plabel_leaf _ _ h]; rfl

/-- `plabel` sees exactly the same node/leaf shape as the raw tree. -/
theorem plabel_eq_one_iff (σ : Bool) (t : Tree d) (p : List (Fin d)) :
    plabel POL σ t p = 1 ↔ t.label p = 1 := by
  induction p generalizing σ t with
  | nil => simp
  | cons i q ih =>
      by_cases h : t.label [] = 1
      · rw [plabel_cons_node _ _ h, ih]; rfl
      · rw [plabel_leaf _ _ h, sgn_eq_one]
        have he := t.absorbs [] (i :: q) h
        simp only [List.nil_append] at he
        rw [he]

theorem plabel_absorbs (σ : Bool) (t : Tree d) (p q : List (Fin d)) (h : plabel POL σ t p ≠ 1) :
    plabel POL σ t (p ++ q) = plabel POL σ t p := by
  induction p generalizing σ t with
  | nil =>
      have h' : t.label [] ≠ 1 := fun he => h (by simp [he])
      rw [List.nil_append, plabel_leaf _ _ h']; rfl
  | cons i p ih =>
      by_cases ht : t.label [] = 1
      · rw [List.cons_append, plabel_cons_node _ _ ht, plabel_cons_node _ _ ht]
        rw [plabel_cons_node _ _ ht] at h
        exact ih _ _ h
      · rw [List.cons_append, plabel_leaf _ _ ht, plabel_leaf _ _ ht]

/-- The descriptive form of v1362 §1: along a path of `f`-nodes, the label at
`p` is the raw label swapped iff `σ xor pathPol p` is odd. -/
theorem plabel_of_nodes (σ : Bool) (t : Tree d) (p : List (Fin d))
    (h : ∀ k < p.length, t.label (p.take k) = 1) :
    plabel POL σ t p = sgn (xor σ (pathPol POL p)) (t.label p) := by
  induction p generalizing σ t with
  | nil => simp
  | cons i q ih =>
      have h0 : t.label [] = 1 := by simpa using h 0 (by simp)
      rw [plabel_cons_node _ _ h0, ih]
      · simp [Bool.xor_assoc]
      · intro k hk
        have := h (k + 1) (by simp; omega)
        simpa using this

/-- Reading below a path of `f`-nodes: the label at `p ++ q` is the label of the
subtree at `p`, read with the sign shifted by `pathPol p` (v1362: `plabel_σ(t, pq) =
plabel_{σ·pol(p)}(P_p t, q)`). -/
theorem plabel_append_of_nodes (σ : Bool) (t : Tree d) (p q : List (Fin d))
    (h : ∀ k < p.length, t.label (p.take k) = 1) :
    plabel POL σ t (p ++ q) = plabel POL (xor σ (pathPol POL p)) (project t p) q := by
  induction p generalizing σ t with
  | nil => simp
  | cons i p ih =>
      have h0 : t.label [] = 1 := by simpa using h 0 (by simp)
      rw [List.cons_append, plabel_cons_node _ _ h0, ih]
      · rw [project_append, pathPol_cons, Bool.xor_assoc]; rfl
      · intro k hk
        have := h (k + 1) (by simp; omega)
        simpa using this

@[simp] theorem plabel_bot (σ : Bool) (p : List (Fin d)) :
    plabel POL σ (⊥ : Tree d) p = sgn σ 0 :=
  plabel_leaf σ ⊥ (by rw [bot_label]; decide) p

@[simp] theorem plabel_top (σ : Bool) (p : List (Fin d)) :
    plabel POL σ (⊤ : Tree d) p = sgn σ 2 :=
  plabel_leaf σ ⊤ (by rw [top_label]; decide) p

/-! ## The encoding as a map on the carrier -/

/-- Signed encoding of a raw tree as a covariant carrier tree. -/
def encS (POL : Polarity d) (σ : Bool) (t : Tree d) : Tree d where
  label := plabel POL σ t
  absorbs p q h := plabel_absorbs σ t p q h

@[simp] theorem encS_label (σ : Bool) (t : Tree d) (w : List (Fin d)) :
    (encS POL σ t).label w = plabel POL σ t w := rfl

theorem encS_eq_dualIf (σ : Bool) (t : Tree d) : encS POL σ t = dualIf σ (encS POL false t) := by
  ext w; simp [plabel_eq_sgn σ t w]

theorem project_encS (σ : Bool) (t : Tree d) (h : t.label [] = 1) (i : Fin d) :
    project (encS POL σ t) [i] = encS POL (xor σ (POL i)) (project t [i]) := by
  apply tree_ext; intro w
  exact plabel_cons_node σ t h i w

/-- The signed encoding is an involution: the decoding is the same map. -/
theorem encS_encS (σ : Bool) (t : Tree d) : encS POL σ (encS POL σ t) = t := by
  apply tree_ext; intro p
  simp only [encS_label]
  induction p generalizing σ t with
  | nil => simp
  | cons i q ih =>
      by_cases h : t.label [] = 1
      · have h' : (encS POL σ t).label [] = 1 := by simp [h]
        rw [plabel_cons_node _ _ h', project_encS _ _ h]
        exact ih _ _
      · have h' : (encS POL σ t).label [] ≠ 1 := by simpa using h
        rw [plabel_leaf _ _ h']
        have he := t.absorbs [] (i :: q) h
        simp only [List.nil_append] at he
        simp [he]

/-! ## The encoding lemma (v1362 Lemma 1) -/

private theorem plabel_le_of_sim {R : CTree POL → CTree POL → Prop} (hR : IsSim POL R)
    (p : List (Fin d)) : ∀ (σ : Bool) (s t : CTree POL),
    (if σ = true then R t s else R s t) → plabel POL σ s.raw p ≤ plabel POL σ t.raw p := by
  induction p with
  | nil =>
      intro σ s t h
      cases σ
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        rcases hR s t h with h0 | h2 | ⟨h1, h1', _⟩
        · simp only [plabel_nil, sgn_false]
          rw [show s.raw.label [] = 0 from h0]; exact label_zero_le _
        · simp only [plabel_nil, sgn_false]
          rw [show t.raw.label [] = 2 from h2]; exact label_le_two _
        · simp only [plabel_nil, sgn_false]
          rw [show s.raw.label [] = 1 from h1, show t.raw.label [] = 1 from h1']
      · simp only [↓reduceIte] at h
        rcases hR t s h with h0 | h2 | ⟨h1, h1', _⟩
        · simp only [plabel_nil, sgn_true]
          rw [show t.raw.label [] = 0 from h0]; exact label_le_two _
        · simp only [plabel_nil, sgn_true]
          rw [show s.raw.label [] = 2 from h2]; exact label_zero_le _
        · simp only [plabel_nil, sgn_true]
          rw [show s.raw.label [] = 1 from h1', show t.raw.label [] = 1 from h1]
  | cons i q ih =>
      intro σ s t h
      cases σ
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        rcases hR s t h with h0 | h2 | ⟨h1, h1', hc⟩
        · rw [plabel_leaf _ _ (by rw [show s.raw.label [] = 0 from h0]; decide)]
          rw [show s.raw.label [] = 0 from h0]; exact label_zero_le _
        · rw [plabel_leaf _ t.raw (by rw [show t.raw.label [] = 2 from h2]; decide)]
          rw [show t.raw.label [] = 2 from h2]; exact label_le_two _
        · rw [plabel_cons_node _ _ h1, plabel_cons_node _ _ h1']
          apply ih (xor false (POL i)) (s.child i) (t.child i)
          have hci := hc i
          cases hp : POL i <;> simp_all
      · simp only [↓reduceIte] at h
        rcases hR t s h with h0 | h2 | ⟨h1, h1', hc⟩
        · rw [plabel_leaf _ t.raw (by rw [show t.raw.label [] = 0 from h0]; decide)]
          rw [show t.raw.label [] = 0 from h0]; exact label_le_two _
        · rw [plabel_leaf _ s.raw (by rw [show s.raw.label [] = 2 from h2]; decide)]
          rw [show s.raw.label [] = 2 from h2]; exact label_zero_le _
        · rw [plabel_cons_node _ _ h1', plabel_cons_node _ _ h1]
          apply ih (xor true (POL i)) (s.child i) (t.child i)
          have hci := hc i
          cases hp : POL i <;> simp_all

private theorem isSim_plabel :
    IsSim POL (fun s t => ∀ p, plabel POL false s.raw p ≤ plabel POL false t.raw p) := by
  intro a b h
  have h0 := h []
  simp only [plabel_nil, sgn_false] at h0
  rcases label_le_cases h0 with ha | hb | ⟨ha, hb⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · refine Or.inr (Or.inr ⟨ha, hb, fun i => ?_⟩)
    have hi : ∀ q, plabel POL (POL i) (a.child i).raw q ≤ plabel POL (POL i) (b.child i).raw q := by
      intro q
      have := h (i :: q)
      rw [plabel_cons_node _ _ ha, plabel_cons_node _ _ hb] at this
      simpa using this
    split_ifs with hp
    · intro q
      have := hi q
      rw [plabel_eq_sgn (POL i), plabel_eq_sgn (POL i) (b.child i).raw, hp] at this
      simpa using this
    · intro q
      simpa [show POL i = false by simpa using hp] using hi q

/-- **Encoding lemma (v1362 Lemma 1).** The original (coinductive) order is the
pointwise order of polarity-aware path labels. -/
theorem le_iff_plabel (s t : CTree POL) :
    Le s t ↔ ∀ p, plabel POL false s.raw p ≤ plabel POL false t.raw p := by
  constructor
  · rintro ⟨R, hR, h⟩ p
    exact plabel_le_of_sim hR p false s t (by simpa using h)
  · intro h
    exact le_of_isSim isSim_plabel h

/-! ## Order structure -/

instance : LE (CTree POL) := ⟨Le⟩

theorem le_def (s t : CTree POL) : s ≤ t ↔ Le s t := Iff.rfl

/-- The unsigned encoding of a raw tree. -/
def enc (POL : Polarity d) (t : CTree POL) : Tree d := encS POL false t.raw

theorem le_iff_enc (s t : CTree POL) : s ≤ t ↔ enc POL s ≤ enc POL t :=
  le_iff_plabel s t

theorem enc_injective : Function.Injective (enc POL) := fun s t h => by
  apply CTree.ext
  rw [← encS_encS (POL := POL) false s.raw, ← encS_encS (POL := POL) false t.raw]
  exact congrArg (encS POL false) h

instance : PartialOrder (CTree POL) where
  le := Le
  le_refl s := (le_iff_enc s s).mpr le_rfl
  le_trans a b c h₁ h₂ := (le_iff_enc a c).mpr (((le_iff_enc a b).mp h₁).trans ((le_iff_enc b c).mp h₂))
  le_antisymm a b h₁ h₂ :=
    enc_injective (le_antisymm ((le_iff_enc a b).mp h₁) ((le_iff_enc b a).mp h₂))

theorem enc_botT : enc POL CTree.botT = ⊥ := by
  apply tree_ext; intro w; show plabel POL false ⊥ w = 0; simp
theorem enc_topT : enc POL CTree.topT = ⊤ := by
  apply tree_ext; intro w; show plabel POL false ⊤ w = 2; simp

instance : OrderBot (CTree POL) where
  bot := CTree.botT
  bot_le t := (le_iff_enc _ t).mpr (by rw [enc_botT]; exact bot_le)

instance : OrderTop (CTree POL) where
  top := CTree.topT
  le_top t := (le_iff_enc t _).mpr (by rw [enc_topT]; exact le_top)

@[simp] theorem botT_eq : (CTree.botT : CTree POL) = ⊥ := rfl
@[simp] theorem topT_eq : (CTree.topT : CTree POL) = ⊤ := rfl
@[simp] theorem root_bot : (⊥ : CTree POL).root = 0 := rfl
@[simp] theorem root_top : (⊤ : CTree POL).root = 2 := rfl
@[simp] theorem raw_bot : (⊥ : CTree POL).raw = ⊥ := rfl
@[simp] theorem raw_top : (⊤ : CTree POL).raw = ⊤ := rfl

theorem root_mono {s t : CTree POL} (h : s ≤ t) : s.root ≤ t.root := by
  simpa using (le_iff_plabel s t).mp h []

theorem root_cases (t : CTree POL) : t = ⊥ ∨ (∃ a, t = CTree.node a) ∨ t = ⊤ :=
  CTree.root_cases t

theorem eq_bot_iff_root (t : CTree POL) : t = ⊥ ↔ t.root = 0 :=
  ⟨fun h => h ▸ rfl, CTree.eq_botT_of_root t⟩

theorem eq_top_iff_root (t : CTree POL) : t = ⊤ ↔ t.root = 2 :=
  ⟨fun h => h ▸ rfl, CTree.eq_topT_of_root t⟩

theorem node_ne_bot (a : Fin d → CTree POL) : CTree.node a ≠ ⊥ := fun h => by
  have := congrArg CTree.root h; simp at this

theorem node_ne_top (a : Fin d → CTree POL) : CTree.node a ≠ ⊤ := fun h => by
  have := congrArg CTree.root h; simp at this

theorem bot_ne_top : (⊥ : CTree POL) ≠ ⊤ := fun h => by
  have := congrArg CTree.root h; simp at this

theorem not_node_le_bot (a : Fin d → CTree POL) : ¬ CTree.node a ≤ ⊥ := fun h => by
  have := root_mono h; simp at this

theorem not_top_le_node (a : Fin d → CTree POL) : ¬ (⊤ : CTree POL) ≤ CTree.node a := fun h => by
  have := root_mono h; simp at this

theorem not_top_le_bot : ¬ (⊤ : CTree POL) ≤ ⊥ := fun h => by
  have := root_mono h; simp at this

/-! ## The order isomorphism `E` -/

/-- **The encoding `E`**: an order isomorphism from raw contravariant trees with the
original order onto the covariant carrier with its pointwise order. -/
def E (POL : Polarity d) : CTree POL ≃o Tree d where
  toFun := enc POL
  invFun u := ⟨encS POL false u⟩
  left_inv t := CTree.ext (encS_encS false t.raw)
  right_inv u := encS_encS false u
  map_rel_iff' {s t} := (le_iff_enc s t).symm

theorem E_apply (t : CTree POL) : E POL t = encS POL false t.raw := rfl

@[simp] theorem E_label (t : CTree POL) (w : List (Fin d)) :
    (E POL t).label w = plabel POL false t.raw w := rfl

@[simp] theorem E_symm_raw (u : Tree d) : ((E POL).symm u).raw = encS POL false u := rfl

theorem E_le_iff (s t : CTree POL) : E POL s ≤ E POL t ↔ s ≤ t := (E POL).le_iff_le

@[simp] theorem E_bot : E POL ⊥ = ⊥ := enc_botT
@[simp] theorem E_top : E POL ⊤ = ⊤ := enc_topT

@[simp] theorem E_root (t : CTree POL) : (E POL t).label [] = t.root := rfl

/-- `E` on a node: contravariant children are dualized. -/
theorem E_node (a : Fin d → CTree POL) :
    E POL (CTree.node a) = node (fun i => dualIf (POL i) (E POL (a i))) := by
  apply tree_ext; intro w
  cases w with
  | nil => rfl
  | cons i w =>
      simp only [E_label, node_label_cons, dualIf_label]
      rw [plabel_cons_node _ _ rfl, Bool.false_xor]
      show plabel POL (POL i) (project (AbsorbingSubtypeTrees.node fun j => (a j).raw) (i :: [])) w = _
      rw [project_node, project_nil]
      exact plabel_eq_sgn _ _ _

/-- `E` on a child of a node. -/
theorem project_E (t : CTree POL) (h : t.root = 1) (i : Fin d) :
    project (E POL t) [i] = dualIf (POL i) (E POL (t.child i)) := by
  rw [E_apply, project_encS false t.raw h, encS_eq_dualIf, Bool.false_xor]
  rfl

/-- The subtree of a raw tree at a path. -/
def CTree.proj (t : CTree POL) (p : List (Fin d)) : CTree POL := ⟨project t.raw p⟩

/-- `E` below a path of `f`-nodes: the subtree of the encoding is the encoding of
the subtree, dualized iff the path has odd polarity. -/
theorem project_E_path (t : CTree POL) (p : List (Fin d))
    (h : ∀ k < p.length, t.raw.label (p.take k) = 1) :
    project (E POL t) p = dualIf (pathPol POL p) (E POL (t.proj p)) := by
  apply tree_ext; intro q
  rw [project_label, dualIf_label, E_label, E_label, plabel_append_of_nodes _ _ _ _ h,
    Bool.false_xor, plabel_eq_sgn]
  rfl

theorem E_symm_node (b : Fin d → Tree d) :
    (E POL).symm (node b) = CTree.node (fun i => (E POL).symm (dualIf (POL i) (b i))) := by
  apply (E POL).injective
  rw [OrderIso.apply_symm_apply, E_node]
  congr 1; funext i
  simp

/-- **Derived constructor law.** -/
theorem CTree.node_le_node (a b : Fin d → CTree POL) :
    CTree.node a ≤ CTree.node b ↔ ∀ i, (POL i = true → b i ≤ a i) ∧ (POL i = false → a i ≤ b i) := by
  rw [← E_le_iff, E_node, E_node, AbsorbingSubtypeTrees.node_le_node]
  apply forall_congr'
  intro i
  cases hp : POL i <;> simp [E_le_iff]

/-- One-step unfolding of the order: the greatest-fixpoint equation. -/
theorem le_iff_cases (s t : CTree POL) :
    s ≤ t ↔ s = ⊥ ∨ t = ⊤ ∨ ∃ a b, s = CTree.node a ∧ t = CTree.node b ∧
      ∀ i, (POL i = true → b i ≤ a i) ∧ (POL i = false → a i ≤ b i) := by
  constructor
  · intro h
    rcases root_cases s with rfl | ⟨a, rfl⟩ | rfl
    · exact Or.inl rfl
    · rcases root_cases t with rfl | ⟨b, rfl⟩ | rfl
      · exact absurd h (not_node_le_bot a)
      · exact Or.inr (Or.inr ⟨a, b, rfl, rfl, (CTree.node_le_node a b).mp h⟩)
      · exact Or.inr (Or.inl rfl)
    · rcases root_cases t with rfl | ⟨b, rfl⟩ | rfl
      · exact absurd h not_top_le_bot
      · exact absurd h (not_top_le_node b)
      · exact Or.inr (Or.inl rfl)
  · rintro (rfl | rfl | ⟨a, b, rfl, rfl, h⟩)
    · exact bot_le
    · exact le_top
    · exact (CTree.node_le_node a b).mpr h

/-- The covariant special case: with all positions covariant, `E` commutes with
`node` without any dualization. -/
theorem E_node_covariant (hPOL : ∀ i, POL i = false) (a : Fin d → CTree POL) :
    E POL (CTree.node a) = node (fun i => E POL (a i)) := by
  rw [E_node]; congr 1; funext i; simp [hPOL i]

end NSSE.ContraTrees
