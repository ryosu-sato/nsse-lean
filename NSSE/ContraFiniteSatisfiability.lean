import NSSE.ContraFiniteCycles

/-! # Finite-tree satisfiability: the extremal shape model and Theorem F1 (stage S6, part 1)

Note v1366 §2. The two-set transitions of `ContraSatisfiability` (`next`), with the
**extremal label rule** of v1346 §8: on a state `(L, U)`

* `⊤` if a `⊤`-variable is in `L`; else
* `⊥` if a `⊥`-variable is in `U`; else
* `f` if `L` contains the parent of an original lower literal (`LowF`) and `U`
  the parent of an original upper literal (`UpF`); else
* `⊤` if `LowF`; else `⊥`.

The **shape model** is the unfolding `ρ(z) = T(↓z, ↑z)` (a raw contravariant tree,
regular by construction).

Main results:
* Lemma F1a `xlabel_mono`, `shape_compare` (`S ⊑ S' ⟹ T(S) ≤ T(S')`, original order);
* Lemma F1b `shapeModel_satisfies`: no clash ⟹ the shape model is a solution;
* `node_walk`: an `f`-branch of length `k+1` below `(↓z,↑z)` yields a walk with
  `k+1` edges of the signed pair graph from `(z,z)` (the normalised signed path
  judgement of F1c's proof);
* `finiteModel`: the depth-`n*n+1` finite unfolding; without signed C4 its image
  is the shape model (`toC_finiteModel`);
* Lemma F1c `shape_finite_iff`;
* **Theorem F1** `finiteSatisfiable_iff`: a four-form system has a finite solution
  iff it is clash-free and has no signed C4; the executable
  `decideFiniteSatisfiable` with `decideFiniteSatisfiable_correct`, and the finite
  model on success `decideFiniteSatisfiable_model`.
-/

namespace NSSE.ContraFiniteSatisfiability

open SubtypeConstraints (Constraints Query BoundLiteral)
open AbsorbingSubtypeTrees RegularSubtypeTrees
open ContraTrees ContraFiniteTrees ContraRegularTrees ContraConstraints ContraSupport
  ContraClashes ContraSatisfiability ContraFiniteCycles

variable {n d : Nat} {POL : Polarity d}

/-! ## The extremal label rule -/

def HasBot (φ : Constraints n d) (U : Finset (Fin n)) : Prop := ∃ x ∈ φ.bot, x ∈ U
def UpF (φ : Constraints n d) (U : Finset (Fin n)) : Prop := ∃ a ∈ φ.upper, a.1 ∈ U

instance (φ : Constraints n d) (U : Finset (Fin n)) : Decidable (HasBot φ U) := by
  unfold HasBot; infer_instance
instance (φ : Constraints n d) (U : Finset (Fin n)) : Decidable (UpF φ U) := by
  unfold UpF; infer_instance

/-- The extremal label rule (v1346 §8, v1366 §2). -/
def xlabel (φ : Constraints n d) (s : State n) : Label :=
  if HasTop φ s.1 then 2 else if HasBot φ s.2 then 0 else
    if LowF φ s.1 then (if UpF φ s.2 then 1 else 2) else 0

theorem xlabel_eq_one {φ : Constraints n d} {s : State n} (h : xlabel φ s = 1) :
    LowF φ s.1 ∧ UpF φ s.2 := by
  unfold xlabel at h
  split_ifs at h with h1 h2 h3 h4 <;> first | exact ⟨h3, h4⟩ | exact absurd h (by decide)

/-- **Lemma F1a (labels).** The extremal rule is monotone under `⊑`. -/
theorem xlabel_mono (φ : Constraints n d) {s t : State n} (h : Refines s t) :
    xlabel φ s ≤ xlabel φ t := by
  have ht : HasTop φ s.1 → HasTop φ t.1 := fun ⟨x, hx, hm⟩ => ⟨x, hx, h.1 hm⟩
  have hb : HasBot φ t.2 → HasBot φ s.2 := fun ⟨x, hx, hm⟩ => ⟨x, hx, h.2 hm⟩
  have hl : LowF φ s.1 → LowF φ t.1 := fun ⟨a, ha, hm⟩ => ⟨a, ha, h.1 hm⟩
  have hu : UpF φ t.2 → UpF φ s.2 := fun ⟨a, ha, hm⟩ => ⟨a, ha, h.2 hm⟩
  unfold xlabel
  by_cases h1 : HasTop φ s.1
  · rw [if_pos h1, if_pos (ht h1)]
  rw [if_neg h1]
  by_cases h2 : HasBot φ s.2
  · rw [if_pos h2]; exact Fin.zero_le _
  rw [if_neg h2]
  by_cases h3 : HasTop φ t.1
  · rw [if_pos h3]; exact Fin.le_last _
  rw [if_neg h3, if_neg (fun h => h2 (hb h))]
  by_cases h4 : LowF φ s.1
  · rw [if_pos h4, if_pos (hl h4)]
    by_cases h5 : UpF φ s.2
    · rw [if_pos h5]; split_ifs <;> decide
    · rw [if_neg h5, if_neg (fun h => h5 (hu h))]
  · rw [if_neg h4]; exact Fin.zero_le _

/-! ## The shape model -/

/-- The tree unfolded from a state under the extremal label rule. -/
def shapeTree (POL : Polarity d) (φ : Constraints n d) (s : State n) : CTree POL :=
  ctreeWith POL φ (xlabel φ) s

/-- **The shape model** `ρ(z) = T(↓z, ↑z)`. -/
def shapeModel (POL : Polarity d) (φ : Constraints n d) (x : Fin n) : CTree POL :=
  shapeTree POL φ (initial POL φ x)

theorem shapeModel_regular (φ : Constraints n d) (x : Fin n) : CRegular (shapeModel POL φ x) :=
  ctreeWith_regular φ _ _

theorem shapeTree_root (φ : Constraints n d) (s : State n) :
    (shapeTree POL φ s).root = xlabel φ s := rfl

theorem shapeTree_node (φ : Constraints n d) (s : State n) (h : xlabel φ s = 1) :
    shapeTree POL φ s = CTree.node (fun i => shapeTree POL φ (next POL φ s i)) := by
  rw [CTree.eq_node_of_root (shapeTree POL φ s) h]
  congr 1; funext i; exact ctreeWith_child φ _ s h i

theorem shapeTree_top (φ : Constraints n d) (s : State n) (h : xlabel φ s = 2) :
    shapeTree POL φ s = ⊤ := (ContraTrees.eq_top_iff_root _).mpr h

theorem shapeTree_bot (φ : Constraints n d) (s : State n) (h : xlabel φ s = 0) :
    shapeTree POL φ s = ⊥ := (ContraTrees.eq_bot_iff_root _).mpr h

/-- **Lemma F1a (trees).** `S ⊑ S' ⟹ T(S) ≤ T(S')` in the original order. -/
theorem shape_compare (φ : Constraints n d) {s t : State n} (h : Refines s t) :
    shapeTree POL φ s ≤ shapeTree POL φ t :=
  compareWith φ (xlabel φ) (fun _ _ h => xlabel_mono φ h) h

/-! ## Lemma F1b: the shape model solves every clash-free system -/

theorem shapeModel_satisfies (φ : Constraints n d) (hc : ¬ Clash POL φ) :
    Satisfies (treeConstructor POL) φ (shapeModel POL φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- upper literals `v ≤ f(d̄)`
    intro a ha
    have hnt : ¬ HasTop φ (down POL φ a.1) := by
      rintro ⟨x, hx, hm⟩
      exact hc (Or.inr (Or.inl ⟨x, hx, a, ha, (mem_down φ _ _).mp hm⟩))
    have hu : UpF φ (up POL φ a.1) := ⟨a, ha, refl_up φ a.1⟩
    change shapeTree POL φ (initial POL φ a.1) ≤ CTree.node (fun i => shapeModel POL φ (a.2 i))
    by_cases hb : HasBot φ (up POL φ a.1)
    · rw [shapeTree_bot φ _ (by simp [xlabel, initial, hnt, hb])]
      exact bot_le
    by_cases hf : LowF φ (down POL φ a.1)
    · rw [shapeTree_node φ _ (by simp [xlabel, initial, hnt, hb, hf, hu])]
      apply (CTree.node_le_node _ _).mpr
      intro i
      constructor
      · intro hi; exact shape_compare φ (upper_child_con φ a ha hi)
      · intro hi; exact shape_compare φ (upper_child_cov φ a ha hi)
    · rw [shapeTree_bot φ _ (by simp [xlabel, initial, hnt, hb, hf])]
      exact bot_le
  · -- lower literals `f(c̄) ≤ v`
    intro a ha
    change CTree.node (fun i => shapeModel POL φ (a.2 i)) ≤ shapeTree POL φ (initial POL φ a.1)
    by_cases ht : HasTop φ (down POL φ a.1)
    · rw [shapeTree_top φ _ (by simp [xlabel, initial, ht])]
      exact le_top
    have hnb : ¬ HasBot φ (up POL φ a.1) := by
      rintro ⟨y, hy, hm⟩
      exact hc (Or.inr (Or.inr ⟨a, ha, y, hy, (mem_up φ _ _).mp hm⟩))
    have hf : LowF φ (down POL φ a.1) := ⟨a, ha, refl_down φ a.1⟩
    by_cases hu : UpF φ (up POL φ a.1)
    · rw [shapeTree_node φ _ (by simp [xlabel, initial, ht, hnb, hf, hu])]
      apply (CTree.node_le_node _ _).mpr
      intro i
      constructor
      · intro hi; exact shape_compare φ (lower_child_con φ a ha hi)
      · intro hi; exact shape_compare φ (lower_child_cov φ a ha hi)
    · rw [shapeTree_top φ _ (by simp [xlabel, initial, ht, hnb, hf, hu])]
      exact le_top
  · -- `x = ⊥`
    intro x hx
    have hnt : ¬ HasTop φ (down POL φ x) := by
      rintro ⟨y, hy, hm⟩
      exact hc (Or.inl ⟨y, hy, x, hx, (mem_down φ _ _).mp hm⟩)
    have hb : HasBot φ (up POL φ x) := ⟨x, hx, refl_up φ x⟩
    exact shapeTree_bot φ _ (by simp [xlabel, initial, hnt, hb])
  · -- `x = ⊤`
    intro x hx
    have ht : HasTop φ (down POL φ x) := ⟨x, hx, refl_down φ x⟩
    exact shapeTree_top φ _ (by simp [xlabel, initial, ht])

/-! ## `f`-branches give walks of the signed pair graph (proof of F1c) -/

/-- `NodeDepth k s`: the unfolding from `s` has a branch of `k` consecutive
`f`-labelled nodes. -/
def NodeDepth (POL : Polarity d) (φ : Constraints n d) : Nat → State n → Prop
  | 0, _ => True
  | k + 1, s => xlabel φ s = 1 ∧ ∃ i, NodeDepth POL φ k (next POL φ s i)

/-- The normalised signed path judgement: an `f`-branch of length `k+1` from `s`
fixes literals `f(c̄) ≤ w`, `w ∈ L` and `w' ≤ f(d̄)`, `w' ∈ U` such that every
supported vertex `(p₁,p₂)` with `w ≤s p₁`, `p₂ ≤s w'` starts a walk with `k+1`
edges. -/
theorem node_walk_of (φ : Constraints n d) : ∀ (k : Nat) (s : State n),
    NodeDepth POL φ (k + 1) s →
    ∃ a ∈ φ.lower, a.1 ∈ s.1 ∧ ∃ b ∈ φ.upper, b.1 ∈ s.2 ∧
      ∀ p : Vertex n, Support POL φ p.1 p.2 → Support POL φ a.1 p.1 → Support POL φ p.2 b.1 →
        WalkFrom POL φ (k + 1) p := by
  intro k
  induction k with
  | zero =>
      rintro s ⟨hl, i, -⟩
      obtain ⟨⟨a, ha, haL⟩, ⟨b, hb, hbU⟩⟩ := xlabel_eq_one hl
      refine ⟨a, ha, haL, b, hb, hbU, fun p hs h1 h2 => ?_⟩
      exact .succ ⟨hs, i, a, ha, b, hb, h1, h2, rfl⟩ (.zero _)
  | succ k ih =>
      rintro s ⟨hl, i, hd⟩
      obtain ⟨a', ha', haL', b', hb', hbU', hw⟩ := ih _ hd
      obtain ⟨⟨a₀, ha₀, haL₀⟩, ⟨b₀, hb₀, hbU₀⟩⟩ := xlabel_eq_one hl
      cases hpi : POL i
      · rw [next_cov φ s hpi] at haL' hbU'
        obtain ⟨a, ha, haL, hsa⟩ := (mem_covL φ _ i _).mp haL'
        obtain ⟨b, hb, hbU, hsb⟩ := (mem_covU φ _ i _).mp hbU'
        refine ⟨a, ha, haL, b, hb, hbU, fun p hs h1 h2 => ?_⟩
        have he : PairStep POL φ p (a.2 i, b.2 i) := ⟨hs, i, a, ha, b, hb, h1, h2, by simp [hpi]⟩
        exact .succ he (hw _ (pairStep_target φ he) hsa hsb)
      · rw [next_con φ s hpi] at haL' hbU'
        obtain ⟨b, hb, hbU, hsb⟩ := (mem_conL φ _ i _).mp haL'
        obtain ⟨a, ha, haL, hsa⟩ := (mem_conU φ _ i _).mp hbU'
        refine ⟨a, ha, haL, b, hb, hbU, fun p hs h1 h2 => ?_⟩
        have he : PairStep POL φ p (b.2 i, a.2 i) := ⟨hs, i, a, ha, b, hb, h1, h2, by simp [hpi]⟩
        exact .succ he (hw _ (pairStep_target φ he) hsb hsa)

/-- An `f`-branch of length `k+1` below `(↓z,↑z)` yields a walk with `k+1` edges
from the vertex `(z,z)`. -/
theorem node_walk (φ : Constraints n d) (k : Nat) (z : Fin n)
    (h : NodeDepth POL φ (k + 1) (initial POL φ z)) : WalkFrom POL φ (k + 1) (z, z) := by
  obtain ⟨a, _, haL, b, _, hbU, hw⟩ := node_walk_of φ k _ h
  exact hw (z, z) (.refl z) ((mem_down φ _ _).mp haL) ((mem_up φ _ _).mp hbU)

theorem not_nodeDepth (φ : Constraints n d) (hc4 : ¬ SignedC4 POL φ) (z : Fin n) :
    ¬ NodeDepth POL φ (n * n + 1) (initial POL φ z) := fun h =>
  hc4 (signedC4_of_walk φ (walkFrom_pred φ _ _ (node_walk φ (n * n) z h)))

/-! ## The finite unfolding -/

/-- Unfolding with fuel `k` into a finite tree. -/
def unfoldF (POL : Polarity d) (φ : Constraints n d) : Nat → State n → FTree POL
  | 0, _ => FTree.bot
  | k + 1, s =>
      if xlabel φ s = 1 then FTree.node (fun i => unfoldF POL φ k (next POL φ s i))
      else if xlabel φ s = 2 then FTree.top else FTree.bot

theorem height_unfoldF (φ : Constraints n d) : ∀ (k : Nat) (s : State n),
    height (unfoldF POL φ k s) ≤ k := by
  intro k
  induction k with
  | zero => intro s; simp [unfoldF, height]
  | succ k ih =>
      intro s
      simp only [unfoldF]
      split_ifs
      · simp only [height]
        exact Nat.succ_le_succ (Finset.sup_le (fun i _ => ih _))
      · simp [height]
      · simp [height]

/-- Without an `f`-branch of length `k`, the fuel-`k` unfolding is exact. -/
theorem toC_unfoldF (φ : Constraints n d) : ∀ (k : Nat) (s : State n),
    ¬ NodeDepth POL φ k s → toC (unfoldF POL φ k s) = shapeTree POL φ s := by
  intro k
  induction k with
  | zero => intro s h; exact absurd trivial h
  | succ k ih =>
      intro s h
      simp only [unfoldF]
      by_cases h1 : xlabel φ s = 1
      · rw [if_pos h1, toC_node, shapeTree_node φ s h1]
        congr 1; funext i
        exact ih _ (fun hd => h ⟨h1, i, hd⟩)
      · rw [if_neg h1]
        by_cases h2 : xlabel φ s = 2
        · rw [if_pos h2, toC_top, shapeTree_top φ s h2]
        · rw [if_neg h2, toC_bot]
          have h0 : xlabel φ s = 0 := by
            revert h1 h2; generalize xlabel φ s = l; revert l; decide
          rw [shapeTree_bot φ s h0]

/-- **The explicit finite model**: the depth-`n*n+1` finite unfolding of the shape
model. -/
def finiteModel (POL : Polarity d) (φ : Constraints n d) (x : Fin n) : FTree POL :=
  unfoldF POL φ (n * n + 1) (initial POL φ x)

theorem height_finiteModel (φ : Constraints n d) (x : Fin n) :
    height (finiteModel POL φ x) ≤ n * n + 1 := height_unfoldF φ _ _

theorem toC_finiteModel (φ : Constraints n d) (hc4 : ¬ SignedC4 POL φ) (x : Fin n) :
    toC (finiteModel POL φ x) = shapeModel POL φ x :=
  toC_unfoldF φ _ _ (not_nodeDepth φ hc4 x)

theorem finiteModel_satisfies (φ : Constraints n d) (hc : ¬ Clash POL φ)
    (hc4 : ¬ SignedC4 POL φ) : Satisfies (finiteConstructor POL) φ (finiteModel POL φ) := by
  rw [finite_satisfies_iff]
  have : (fun x => toC (finiteModel POL φ x)) = shapeModel POL φ :=
    funext (toC_finiteModel φ hc4)
  rw [this]
  exact shapeModel_satisfies φ hc

/-- **Lemma F1c (v1366 §2).** For a clash-free system, the shape model is finite
(every value is the image of a finite tree) iff there is no signed C4. -/
theorem shape_finite_iff (φ : Constraints n d) (hc : ¬ Clash POL φ) :
    (∀ x, ∃ t : FTree POL, toC t = shapeModel POL φ x) ↔ ¬ SignedC4 POL φ := by
  constructor
  · intro h hc4
    choose t ht using h
    apply not_finiteSatisfiable_of_c4 hc4
    refine ⟨t, ?_⟩
    rw [finite_satisfies_iff]
    have : (fun x => toC (t x)) = shapeModel POL φ := funext ht
    rw [this]
    exact shapeModel_satisfies φ hc
  · intro hc4 x
    exact ⟨_, toC_finiteModel φ hc4 x⟩

/-! ## Theorem F1 and the decision -/

/-- **Theorem F1 (v1366 §2).** A four-form system has a finite solution iff it is
clash-free and has no signed C4. -/
theorem finiteSatisfiable_iff (φ : Constraints n d) :
    Satisfiable (finiteConstructor POL) φ ↔ ¬ Clash POL φ ∧ ¬ SignedC4 POL φ := by
  constructor
  · intro h
    exact ⟨fun hc => not_finiteSatisfiable_of_clash hc h, fun hc4 => not_finiteSatisfiable_of_c4 hc4 h⟩
  · rintro ⟨hc, hc4⟩
    exact ⟨_, finiteModel_satisfies φ hc hc4⟩

/-- **The executable finite-tree satisfiability decision.** -/
def decideFiniteSatisfiable (POL : Polarity d) (φ : Constraints n d) : Bool :=
  !clashBool POL φ && !c4Bool POL φ

theorem decideFiniteSatisfiable_iff (φ : Constraints n d) :
    decideFiniteSatisfiable POL φ = true ↔ ¬ Clash POL φ ∧ ¬ SignedC4 POL φ := by
  rw [← clashBool_correct, ← c4Bool_correct]
  unfold decideFiniteSatisfiable
  cases clashBool POL φ <;> cases c4Bool POL φ <;> simp

theorem decideFiniteSatisfiable_correct (φ : Constraints n d) :
    decideFiniteSatisfiable POL φ = true ↔ Satisfiable (finiteConstructor POL) φ :=
  (decideFiniteSatisfiable_iff φ).trans (finiteSatisfiable_iff φ).symm

/-- On success the explicit finite model is a solution. -/
theorem decideFiniteSatisfiable_model (φ : Constraints n d)
    (h : decideFiniteSatisfiable POL φ = true) :
    Satisfies (finiteConstructor POL) φ (finiteModel POL φ) :=
  let h' := (decideFiniteSatisfiable_iff φ).mp h
  finiteModel_satisfies φ h'.1 h'.2

/-- Finitely unsatisfiable systems entail everything over finite trees. -/
theorem finiteEntails_of_decide_false (Q : Query n d)
    (h : decideFiniteSatisfiable POL Q.constraints = false) :
    Entails (finiteConstructor POL) Q := by
  apply entails_of_unsatisfiable
  rw [← decideFiniteSatisfiable_correct, h]
  simp

/-- Finite satisfiability is strictly a refinement of the arbitrary-tree test:
finitely satisfiable ⟹ satisfiable, and the two agree exactly on C4-free systems. -/
theorem finiteSatisfiable_iff_satisfiable_of_noC4 (φ : Constraints n d)
    (hc4 : ¬ SignedC4 POL φ) :
    Satisfiable (finiteConstructor POL) φ ↔ Satisfiable (treeConstructor POL) φ := by
  rw [finiteSatisfiable_iff, satisfiable_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hc4⟩⟩

end NSSE.ContraFiniteSatisfiability
