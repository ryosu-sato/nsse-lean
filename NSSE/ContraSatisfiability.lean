import NSSE.ContraClashes

/-! # Satisfiability of flat contravariant systems: the two-set model (stage S2)

Notes v1362 §4 (Theorem 7), v1361 §5. States are pairs `(L, U)` of variable
sets (variables below, resp. above, the node). The label is read from `L` only:
`⊤` if `L` contains a `⊤`-variable, `f` if it contains the parent of an original
lower literal, else `⊥`. Transitions:

```
covariant i:      L' = {u : f(c̄) ≤ v, v ∈ L, u ≤s c_i}    U' = {u : v ≤ f(d̄), v ∈ U, d_i ≤s u}
contravariant i:  L' = {u : v ≤ f(d̄), v ∈ U, u ≤s d_i}    U' = {u : f(c̄) ≤ v, v ∈ L, c_i ≤s u}
```

and the value of `z` is the unfolding from `(↓z, ↑z)`. The graph is finite
(`2^n · 2^n` states), so the model is a REGULAR raw contravariant tree.

Main results (no clash = C1–C3 with the polarity-aware closure):
* `model_satisfies`: no clash ⇒ the two-set model satisfies every literal in the
  ORIGINAL coinductive contravariant order;
* `satisfiable_iff`, `regularSatisfiable_iff`, `satisfiable_iff_regularSatisfiable`;
* `decideSatisfiable` with `decideSatisfiable_correct` (arbitrary trees) and
  `decideRegularSatisfiable_correct` (regular trees).

Proof as in v1362 §4, except that the reachable-state invariant is not needed
for the literal checks (they only inspect initial states); it is still proved
(`invariant_run`) as an interface for later stages.
-/

namespace NSSE.ContraSatisfiability

open SubtypeConstraints (Constraints Query BoundLiteral)
open AbsorbingSubtypeTrees RegularSubtypeTrees
open ContraTrees ContraRegularTrees ContraConstraints ContraSupport ContraClashes

abbrev State (n : Nat) := Finset (Fin n) × Finset (Fin n)

variable {n d : Nat} {POL : Polarity d}

/-! ## Sets and transitions, computed from the exact support table -/

def down (POL : Polarity d) (φ : Constraints n d) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun z => Support POL φ z x)

def up (POL : Polarity d) (φ : Constraints n d) (x : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun z => Support POL φ x z)

@[simp] theorem mem_down (φ : Constraints n d) (x z : Fin n) :
    z ∈ down POL φ x ↔ Support POL φ z x := by simp [down]

@[simp] theorem mem_up (φ : Constraints n d) (x z : Fin n) :
    z ∈ up POL φ x ↔ Support POL φ x z := by simp [up]

/-- Covariant `L`-step: lower bounds from original lower literals on `L`. -/
def covL (POL : Polarity d) (φ : Constraints n d) (L : Finset (Fin n)) (i : Fin d) :
    Finset (Fin n) :=
  Finset.univ.filter (fun z => ∃ a ∈ φ.lower, a.1 ∈ L ∧ Support POL φ z (a.2 i))

/-- Covariant `U`-step: upper bounds from original upper literals on `U`. -/
def covU (POL : Polarity d) (φ : Constraints n d) (U : Finset (Fin n)) (i : Fin d) :
    Finset (Fin n) :=
  Finset.univ.filter (fun z => ∃ a ∈ φ.upper, a.1 ∈ U ∧ Support POL φ (a.2 i) z)

/-- Contravariant `L`-step: an upper literal on the parent is a LOWER bound on a
contravariant child. -/
def conL (POL : Polarity d) (φ : Constraints n d) (U : Finset (Fin n)) (i : Fin d) :
    Finset (Fin n) :=
  Finset.univ.filter (fun z => ∃ a ∈ φ.upper, a.1 ∈ U ∧ Support POL φ z (a.2 i))

/-- Contravariant `U`-step: a lower literal on the parent is an UPPER bound on a
contravariant child. -/
def conU (POL : Polarity d) (φ : Constraints n d) (L : Finset (Fin n)) (i : Fin d) :
    Finset (Fin n) :=
  Finset.univ.filter (fun z => ∃ a ∈ φ.lower, a.1 ∈ L ∧ Support POL φ (a.2 i) z)

@[simp] theorem mem_covL (φ : Constraints n d) (L : Finset (Fin n)) (i : Fin d) (z : Fin n) :
    z ∈ covL POL φ L i ↔ ∃ a ∈ φ.lower, a.1 ∈ L ∧ Support POL φ z (a.2 i) := by simp [covL]
@[simp] theorem mem_covU (φ : Constraints n d) (U : Finset (Fin n)) (i : Fin d) (z : Fin n) :
    z ∈ covU POL φ U i ↔ ∃ a ∈ φ.upper, a.1 ∈ U ∧ Support POL φ (a.2 i) z := by simp [covU]
@[simp] theorem mem_conL (φ : Constraints n d) (U : Finset (Fin n)) (i : Fin d) (z : Fin n) :
    z ∈ conL POL φ U i ↔ ∃ a ∈ φ.upper, a.1 ∈ U ∧ Support POL φ z (a.2 i) := by simp [conL]
@[simp] theorem mem_conU (φ : Constraints n d) (L : Finset (Fin n)) (i : Fin d) (z : Fin n) :
    z ∈ conU POL φ L i ↔ ∃ a ∈ φ.lower, a.1 ∈ L ∧ Support POL φ (a.2 i) z := by simp [conU]

/-- The polarity-switched transition. -/
def next (POL : Polarity d) (φ : Constraints n d) (s : State n) (i : Fin d) : State n :=
  if POL i = true then (conL POL φ s.2 i, conU POL φ s.1 i) else (covL POL φ s.1 i, covU POL φ s.2 i)

theorem next_cov (φ : Constraints n d) (s : State n) {i : Fin d} (hi : POL i = false) :
    next POL φ s i = (covL POL φ s.1 i, covU POL φ s.2 i) := by simp [next, hi]

theorem next_con (φ : Constraints n d) (s : State n) {i : Fin d} (hi : POL i = true) :
    next POL φ s i = (conL POL φ s.2 i, conU POL φ s.1 i) := by simp [next, hi]

def HasTop (φ : Constraints n d) (L : Finset (Fin n)) : Prop := ∃ x ∈ φ.top, x ∈ L
def LowF (φ : Constraints n d) (L : Finset (Fin n)) : Prop := ∃ a ∈ φ.lower, a.1 ∈ L

instance (φ : Constraints n d) (L : Finset (Fin n)) : Decidable (HasTop φ L) := by
  unfold HasTop; infer_instance
instance (φ : Constraints n d) (L : Finset (Fin n)) : Decidable (LowF φ L) := by
  unfold LowF; infer_instance

/-- The label, read from the lower set only. -/
def label (φ : Constraints n d) (L : Finset (Fin n)) : Label :=
  if HasTop φ L then 2 else if LowF φ L then 1 else 0

def graph (POL : Polarity d) (φ : Constraints n d) : Graph (State n) d :=
  ⟨fun s => label φ s.1, next POL φ⟩

def initial (POL : Polarity d) (φ : Constraints n d) (x : Fin n) : State n :=
  (down POL φ x, up POL φ x)

/-- The raw tree unfolded from a state. -/
def ctree (POL : Polarity d) (φ : Constraints n d) (s : State n) : CTree POL :=
  ⟨(graph POL φ).tree s⟩

/-- **The two-set model.** -/
def model (POL : Polarity d) (φ : Constraints n d) (x : Fin n) : CTree POL :=
  ctree POL φ (initial POL φ x)

theorem state_count : Fintype.card (State n) = 2 ^ n * 2 ^ n := by simp

/-- The model is regular: it is the unfolding of the finite graph `graph POL φ`. -/
theorem model_regular (φ : Constraints n d) (x : Fin n) : CRegular (model POL φ x) :=
  (graph POL φ).regular (initial POL φ x)

theorem ctree_root (φ : Constraints n d) (s : State n) :
    (ctree POL φ s).root = label φ s.1 := rfl

theorem ctree_child (φ : Constraints n d) (s : State n) (h : label φ s.1 = 1) (i : Fin d) :
    (ctree POL φ s).child i = ctree POL φ (next POL φ s i) := by
  show (⟨project ((graph POL φ).tree s) [i]⟩ : CTree POL) = ⟨(graph POL φ).tree (next POL φ s i)⟩
  rw [Graph.project_tree]
  simp only [Graph.step]
  rw [if_pos (show (graph POL φ).label s = 1 from h)]
  rfl

theorem ctree_node (φ : Constraints n d) (s : State n) (h : label φ s.1 = 1) :
    ctree POL φ s = CTree.node (fun i => ctree POL φ (next POL φ s i)) := by
  rw [CTree.eq_node_of_root (ctree POL φ s) h]
  congr 1; funext i; exact ctree_child φ s h i

theorem ctree_top (φ : Constraints n d) (s : State n) (h : label φ s.1 = 2) : ctree POL φ s = ⊤ :=
  (ContraTrees.eq_top_iff_root _).mpr h

theorem ctree_bot (φ : Constraints n d) (s : State n) (h : label φ s.1 = 0) : ctree POL φ s = ⊥ :=
  (ContraTrees.eq_bot_iff_root _).mpr h

/-! ## Monotonicity and the comparison principle -/

/-- `(L,U) ⊑ (L',U')` iff `L ⊆ L'` and `U' ⊆ U`. -/
def Refines (s t : State n) : Prop := s.1 ⊆ t.1 ∧ t.2 ⊆ s.2

theorem label_mono (φ : Constraints n d) {L K : Finset (Fin n)} (h : L ⊆ K) :
    label φ L ≤ label φ K := by
  have ht : HasTop φ L → HasTop φ K := fun ⟨x, hx, hm⟩ => ⟨x, hx, h hm⟩
  have hf : LowF φ L → LowF φ K := fun ⟨a, ha, hm⟩ => ⟨a, ha, h hm⟩
  by_cases hL : HasTop φ L <;> by_cases hK : HasTop φ K <;>
    by_cases hLF : LowF φ L <;> by_cases hKF : LowF φ K <;> simp_all [label]

theorem covL_mono (φ : Constraints n d) {L K : Finset (Fin n)} (h : L ⊆ K) (i : Fin d) :
    covL POL φ L i ⊆ covL POL φ K i := by
  intro z hz
  obtain ⟨a, ha, hm, hs⟩ := (mem_covL φ L i z).mp hz
  exact (mem_covL φ K i z).mpr ⟨a, ha, h hm, hs⟩

theorem covU_mono (φ : Constraints n d) {L K : Finset (Fin n)} (h : L ⊆ K) (i : Fin d) :
    covU POL φ L i ⊆ covU POL φ K i := by
  intro z hz
  obtain ⟨a, ha, hm, hs⟩ := (mem_covU φ L i z).mp hz
  exact (mem_covU φ K i z).mpr ⟨a, ha, h hm, hs⟩

theorem conL_mono (φ : Constraints n d) {L K : Finset (Fin n)} (h : L ⊆ K) (i : Fin d) :
    conL POL φ L i ⊆ conL POL φ K i := by
  intro z hz
  obtain ⟨a, ha, hm, hs⟩ := (mem_conL φ L i z).mp hz
  exact (mem_conL φ K i z).mpr ⟨a, ha, h hm, hs⟩

theorem conU_mono (φ : Constraints n d) {L K : Finset (Fin n)} (h : L ⊆ K) (i : Fin d) :
    conU POL φ L i ⊆ conU POL φ K i := by
  intro z hz
  obtain ⟨a, ha, hm, hs⟩ := (mem_conU φ L i z).mp hz
  exact (mem_conU φ K i z).mpr ⟨a, ha, h hm, hs⟩

/-- A covariant step preserves `⊑`, a contravariant step reverses it. -/
theorem next_refines (φ : Constraints n d) {s t : State n} (h : Refines s t) (i : Fin d) :
    if POL i = true then Refines (next POL φ t i) (next POL φ s i)
    else Refines (next POL φ s i) (next POL φ t i) := by
  cases hp : POL i
  · simp only [Bool.false_eq_true, if_false]
    rw [next_cov φ s hp, next_cov φ t hp]
    exact ⟨covL_mono φ h.1 i, covU_mono φ h.2 i⟩
  · simp only [if_true]
    rw [next_con φ s hp, next_con φ t hp]
    exact ⟨conL_mono φ h.2 i, conU_mono φ h.1 i⟩

theorem label_cases {a b : Label} (h : a ≤ b) (h0 : a ≠ 0) (h2 : b ≠ 2) : a = 1 ∧ b = 1 := by
  revert a b; decide

/-! ### Generic label rules (interface for S6)

The comparison principle holds for EVERY label rule that is monotone under `⊑`
(v1366 Lemma F1a uses it with the extremal label rule for finite trees). -/

/-- The two-set transitions with an arbitrary label rule. -/
def graphWith (POL : Polarity d) (φ : Constraints n d) (lab : State n → Label) :
    Graph (State n) d := ⟨lab, next POL φ⟩

def ctreeWith (POL : Polarity d) (φ : Constraints n d) (lab : State n → Label) (s : State n) :
    CTree POL := ⟨(graphWith POL φ lab).tree s⟩

theorem ctreeWith_regular (φ : Constraints n d) (lab : State n → Label) (s : State n) :
    CRegular (ctreeWith POL φ lab s) := (graphWith POL φ lab).regular s

theorem ctreeWith_root (φ : Constraints n d) (lab : State n → Label) (s : State n) :
    (ctreeWith POL φ lab s).root = lab s := rfl

theorem ctreeWith_child (φ : Constraints n d) (lab : State n → Label) (s : State n)
    (h : lab s = 1) (i : Fin d) :
    (ctreeWith POL φ lab s).child i = ctreeWith POL φ lab (next POL φ s i) := by
  show (⟨project ((graphWith POL φ lab).tree s) [i]⟩ : CTree POL) =
    ⟨(graphWith POL φ lab).tree (next POL φ s i)⟩
  rw [Graph.project_tree]
  simp only [Graph.step]
  rw [if_pos (show (graphWith POL φ lab).label s = 1 from h)]
  rfl

/-- **Comparison principle** for a monotone label rule, in the ORIGINAL
coinductive order: `S ⊑ S' ⟹ T(S) ≤ T(S')`. -/
theorem compareWith (φ : Constraints n d) (lab : State n → Label)
    (hmono : ∀ s t : State n, Refines s t → lab s ≤ lab t) {s t : State n} (h : Refines s t) :
    ctreeWith POL φ lab s ≤ ctreeWith POL φ lab t := by
  let R : CTree POL → CTree POL → Prop := fun a b =>
    ∃ s t, Refines s t ∧ a = ctreeWith POL φ lab s ∧ b = ctreeWith POL φ lab t
  have hR : IsSim POL R := by
    rintro a b ⟨s, t, hst, rfl, rfl⟩
    rw [ctreeWith_root, ctreeWith_root]
    by_cases h0 : lab s = 0
    · exact Or.inl h0
    by_cases h2 : lab t = 2
    · exact Or.inr (Or.inl h2)
    obtain ⟨hs1, ht1⟩ := label_cases (hmono s t hst) h0 h2
    refine Or.inr (Or.inr ⟨hs1, ht1, fun i => ?_⟩)
    rw [ctreeWith_child φ lab s hs1, ctreeWith_child φ lab t ht1]
    have hn := next_refines (POL := POL) φ hst i
    split_ifs at hn ⊢
    · exact ⟨_, _, hn, rfl, rfl⟩
    · exact ⟨_, _, hn, rfl, rfl⟩
  exact le_of_isSim hR ⟨s, t, h, rfl, rfl⟩

theorem ctree_eq_ctreeWith (φ : Constraints n d) (s : State n) :
    ctree POL φ s = ctreeWith POL φ (fun s => label φ s.1) s := rfl

/-- **Comparison principle** for the two-set model. -/
theorem compare (φ : Constraints n d) {s t : State n} (h : Refines s t) :
    ctree POL φ s ≤ ctree POL φ t :=
  compareWith φ (fun s => label φ s.1) (fun _ _ h => label_mono φ h.1) h

/-! ### The signed pair graph (interface for S6, v1366 §1) -/

/-- An edge `(a,b) −i→ (a',b')` of the signed pair graph: a lower literal
`f(c̄) ≤ w` with `w ≤s a`, an upper literal `w' ≤ f(d̄)` with `b ≤s w'`, and
`(a',b') = (c_i,d_i)` at a covariant, `(d_i,c_i)` at a contravariant `i`. -/
def PairEdge (POL : Polarity d) (φ : Constraints n d) (p : Fin n × Fin n) (i : Fin d)
    (q : Fin n × Fin n) : Prop :=
  ∃ a ∈ φ.lower, ∃ b ∈ φ.upper, Support POL φ a.1 p.1 ∧ Support POL φ p.2 b.1 ∧
    q = if POL i = true then (b.2 i, a.2 i) else (a.2 i, b.2 i)

instance (φ : Constraints n d) (p : Fin n × Fin n) (i : Fin d) (q : Fin n × Fin n) :
    Decidable (PairEdge POL φ p i q) := by
  unfold PairEdge; infer_instance

/-- Targets of edges from supported pairs are supported. -/
theorem pairEdge_supported (φ : Constraints n d) {p q : Fin n × Fin n} {i : Fin d}
    (hp : Support POL φ p.1 p.2) (he : PairEdge POL φ p i q) : Support POL φ q.1 q.2 := by
  obtain ⟨a, ha, b, hb, h1, h2, rfl⟩ := he
  have hab : Support POL φ a.1 b.1 := .trans h1 (.trans hp h2)
  cases hpi : POL i
  · simpa [hpi] using Support.decompCov ha hb hab i hpi
  · simpa [hpi] using Support.decompCon ha hb hab i hpi

/-! ## Theorem 7: no clash ⇒ the two-set model is a (regular) solution -/

theorem refl_down (φ : Constraints n d) (x : Fin n) : x ∈ down POL φ x :=
  (mem_down φ x x).mpr (.refl x)

theorem refl_up (φ : Constraints n d) (x : Fin n) : x ∈ up POL φ x :=
  (mem_up φ x x).mpr (.refl x)

/-- The lower literal `f(c̄) ≤ v`, covariant child: `(↓c_i, ↑c_i) ⊑ child`. -/
theorem lower_child_cov (φ : Constraints n d) (a : BoundLiteral n d) (ha : a ∈ φ.lower)
    {i : Fin d} (hi : POL i = false) :
    Refines (initial POL φ (a.2 i)) (next POL φ (initial POL φ a.1) i) := by
  rw [next_cov φ _ hi]
  constructor
  · intro u hu
    exact (mem_covL φ _ i u).mpr ⟨a, ha, refl_down φ a.1, (mem_down φ _ u).mp hu⟩
  · intro u hu
    obtain ⟨b, hb, hm, hs⟩ := (mem_covU φ _ i u).mp hu
    exact (mem_up φ _ u).mpr (.trans (.decompCov ha hb ((mem_up φ _ _).mp hm) i hi) hs)

/-- The lower literal `f(c̄) ≤ v`, contravariant child: `child ⊑ (↓c_i, ↑c_i)`. -/
theorem lower_child_con (φ : Constraints n d) (a : BoundLiteral n d) (ha : a ∈ φ.lower)
    {i : Fin d} (hi : POL i = true) :
    Refines (next POL φ (initial POL φ a.1) i) (initial POL φ (a.2 i)) := by
  rw [next_con φ _ hi]
  constructor
  · intro u hu
    obtain ⟨b, hb, hm, hs⟩ := (mem_conL φ _ i u).mp hu
    exact (mem_down φ _ u).mpr (.trans hs (.decompCon ha hb ((mem_up φ _ _).mp hm) i hi))
  · intro u hu
    exact (mem_conU φ _ i u).mpr ⟨a, ha, refl_down φ a.1, (mem_up φ _ u).mp hu⟩

/-- The upper literal `v ≤ f(d̄)`, covariant child: `child ⊑ (↓d_i, ↑d_i)`. -/
theorem upper_child_cov (φ : Constraints n d) (a : BoundLiteral n d) (ha : a ∈ φ.upper)
    {i : Fin d} (hi : POL i = false) :
    Refines (next POL φ (initial POL φ a.1) i) (initial POL φ (a.2 i)) := by
  rw [next_cov φ _ hi]
  constructor
  · intro u hu
    obtain ⟨b, hb, hm, hs⟩ := (mem_covL φ _ i u).mp hu
    exact (mem_down φ _ u).mpr (.trans hs (.decompCov hb ha ((mem_down φ _ _).mp hm) i hi))
  · intro u hu
    exact (mem_covU φ _ i u).mpr ⟨a, ha, refl_up φ a.1, (mem_up φ _ u).mp hu⟩

/-- The upper literal `v ≤ f(d̄)`, contravariant child: `(↓d_i, ↑d_i) ⊑ child`. -/
theorem upper_child_con (φ : Constraints n d) (a : BoundLiteral n d) (ha : a ∈ φ.upper)
    {i : Fin d} (hi : POL i = true) :
    Refines (initial POL φ (a.2 i)) (next POL φ (initial POL φ a.1) i) := by
  rw [next_con φ _ hi]
  constructor
  · intro u hu
    exact (mem_conL φ _ i u).mpr ⟨a, ha, refl_up φ a.1, (mem_down φ _ u).mp hu⟩
  · intro u hu
    obtain ⟨b, hb, hm, hs⟩ := (mem_conU φ _ i u).mp hu
    exact (mem_up φ _ u).mpr (.trans (.decompCon hb ha ((mem_down φ _ _).mp hm) i hi) hs)

/-- **Theorem 7 (v1362 §4).** Without a clash the two-set model satisfies every
original literal in the original contravariant order. -/
theorem model_satisfies (φ : Constraints n d) (hc : ¬ Clash POL φ) :
    Satisfies (treeConstructor POL) φ (model POL φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- upper literals `v ≤ f(d̄)`
    intro a ha
    have hnt : ¬ HasTop φ (down POL φ a.1) := by
      rintro ⟨x, hx, hm⟩
      exact hc (Or.inr (Or.inl ⟨x, hx, a, ha, (mem_down φ _ _).mp hm⟩))
    by_cases hf : LowF φ (down POL φ a.1)
    · have hl : label φ (initial POL φ a.1).1 = 1 := by
        simp [initial, label, hnt, hf]
      change ctree POL φ (initial POL φ a.1) ≤ CTree.node (fun i => model POL φ (a.2 i))
      rw [ctree_node φ _ hl]
      apply (CTree.node_le_node _ _).mpr
      intro i
      constructor
      · intro hi; exact compare φ (upper_child_con φ a ha hi)
      · intro hi; exact compare φ (upper_child_cov φ a ha hi)
    · have hl : label φ (initial POL φ a.1).1 = 0 := by
        simp [initial, label, hnt, hf]
      change ctree POL φ (initial POL φ a.1) ≤ _
      rw [ctree_bot φ _ hl]
      exact bot_le
  · -- lower literals `f(c̄) ≤ v`
    intro a ha
    by_cases ht : HasTop φ (down POL φ a.1)
    · have hl : label φ (initial POL φ a.1).1 = 2 := by simp [initial, label, ht]
      change _ ≤ ctree POL φ (initial POL φ a.1)
      rw [ctree_top φ _ hl]
      exact le_top
    · have hf : LowF φ (down POL φ a.1) := ⟨a, ha, refl_down φ a.1⟩
      have hl : label φ (initial POL φ a.1).1 = 1 := by simp [initial, label, ht, hf]
      change CTree.node (fun i => model POL φ (a.2 i)) ≤ ctree POL φ (initial POL φ a.1)
      rw [ctree_node φ _ hl]
      apply (CTree.node_le_node _ _).mpr
      intro i
      constructor
      · intro hi; exact compare φ (lower_child_con φ a ha hi)
      · intro hi; exact compare φ (lower_child_cov φ a ha hi)
  · -- `x = ⊥`
    intro x hx
    have hnt : ¬ HasTop φ (down POL φ x) := by
      rintro ⟨y, hy, hm⟩
      exact hc (Or.inl ⟨y, hy, x, hx, (mem_down φ _ _).mp hm⟩)
    have hnf : ¬ LowF φ (down POL φ x) := by
      rintro ⟨a, ha, hm⟩
      exact hc (Or.inr (Or.inr ⟨a, ha, x, hx, (mem_down φ _ _).mp hm⟩))
    exact ctree_bot φ _ (by simp [initial, label, hnt, hnf])
  · -- `x = ⊤`
    intro x hx
    have ht : HasTop φ (down POL φ x) := ⟨x, hx, refl_down φ x⟩
    exact ctree_top φ _ (by simp [initial, label, ht])

/-- The same model on the covariant carrier, through the encoding `E`. -/
theorem model_encSatisfies (φ : Constraints n d) (hc : ¬ Clash POL φ) :
    EncSatisfies POL φ (fun x => E POL (model POL φ x)) :=
  (satisfies_iff_enc φ _).mp (model_satisfies φ hc)

/-! ## The decision -/

theorem satisfiable_iff (φ : Constraints n d) :
    Satisfiable (treeConstructor POL) φ ↔ ¬ Clash POL φ :=
  ⟨no_clash_of_satisfiable, fun h => ⟨model POL φ, model_satisfies φ h⟩⟩

theorem regularSatisfiable_iff (φ : Constraints n d) :
    RegularSatisfiable POL φ ↔ ¬ Clash POL φ :=
  ⟨fun h => no_clash_of_satisfiable (regularSatisfiable_imp φ h),
    fun h => ⟨model POL φ, model_regular φ, model_satisfies φ h⟩⟩

/-- `Sat_Reg = Sat_All`. -/
theorem satisfiable_iff_regularSatisfiable (φ : Constraints n d) :
    Satisfiable (treeConstructor POL) φ ↔ RegularSatisfiable POL φ :=
  (satisfiable_iff φ).trans (regularSatisfiable_iff φ).symm

/-- The total executable satisfiability decision. -/
def decideSatisfiable (POL : Polarity d) (φ : Constraints n d) : Bool := !clashBool POL φ

theorem decideSatisfiable_iff_no_clash (φ : Constraints n d) :
    decideSatisfiable POL φ = true ↔ ¬ Clash POL φ := by
  rw [← clashBool_correct]
  unfold decideSatisfiable
  cases clashBool POL φ <;> simp

theorem decideSatisfiable_correct (φ : Constraints n d) :
    decideSatisfiable POL φ = true ↔ Satisfiable (treeConstructor POL) φ :=
  (decideSatisfiable_iff_no_clash φ).trans (satisfiable_iff φ).symm

theorem decideRegularSatisfiable_correct (φ : Constraints n d) :
    decideSatisfiable POL φ = true ↔ RegularSatisfiable POL φ :=
  (decideSatisfiable_iff_no_clash φ).trans (regularSatisfiable_iff φ).symm

/-- Unsatisfiable systems entail everything (arbitrary and regular trees). -/
theorem entails_of_decide_false (Q : Query n d) (h : decideSatisfiable POL Q.constraints = false) :
    Entails (treeConstructor POL) Q := by
  apply entails_of_unsatisfiable
  rw [← decideSatisfiable_correct, h]
  simp

theorem regularEntails_of_decide_false (Q : Query n d)
    (h : decideSatisfiable POL Q.constraints = false) : RegularEntails POL Q :=
  regularEntails_of_entails Q (entails_of_decide_false Q h)

/-! ## The reachable-state invariant (v1362 §4), as an interface -/

/-- One graph step preserves the invariant `u ∈ L ∧ v ∈ U ⟹ u ≤s v`. -/
theorem invariant_step (φ : Constraints n d) (s : State n)
    (hs : ∀ u ∈ s.1, ∀ v ∈ s.2, Support POL φ u v) (i : Fin d) :
    ∀ u ∈ (next POL φ s i).1, ∀ v ∈ (next POL φ s i).2, Support POL φ u v := by
  intro u hu v hv
  cases hp : POL i
  · rw [next_cov φ s hp] at hu hv
    obtain ⟨a, ha, hm, hs1⟩ := (mem_covL φ _ i u).mp hu
    obtain ⟨b, hb, hm', hs2⟩ := (mem_covU φ _ i v).mp hv
    exact .trans hs1 (.trans (.decompCov ha hb (hs _ hm _ hm') i hp) hs2)
  · rw [next_con φ s hp] at hu hv
    obtain ⟨b, hb, hm', hs1⟩ := (mem_conL φ _ i u).mp hu
    obtain ⟨a, ha, hm, hs2⟩ := (mem_conU φ _ i v).mp hv
    exact .trans hs1 (.trans (.decompCon ha hb (hs _ hm _ hm') i hp) hs2)

theorem invariant_run_of (φ : Constraints n d) (w : List (Fin d)) : ∀ (s : State n),
    (∀ u ∈ s.1, ∀ v ∈ s.2, Support POL φ u v) →
    ∀ u ∈ ((graph POL φ).run s w).1, ∀ v ∈ ((graph POL φ).run s w).2, Support POL φ u v := by
  induction w with
  | nil => intro s hs; exact hs
  | cons i w ih =>
      intro s hs
      refine ih ((graph POL φ).step s i) ?_
      unfold Graph.step
      split_ifs
      · exact invariant_step φ s hs i
      · exact hs

/-- Every state reachable from `(↓z, ↑z)` (by the graph's absorbing run) has
`u ∈ L ∧ v ∈ U ⟹ u ≤s v`. -/
theorem invariant_run (φ : Constraints n d) (z : Fin n) (w : List (Fin d)) {u v : Fin n}
    (hu : u ∈ ((graph POL φ).run (initial POL φ z) w).1)
    (hv : v ∈ ((graph POL φ).run (initial POL φ z) w).2) : Support POL φ u v := by
  refine invariant_run_of φ w _ ?_ u hu v hv
  intro u hu v hv
  exact .trans ((mem_down φ _ _).mp hu) ((mem_up φ _ _).mp hv)

end NSSE.ContraSatisfiability
