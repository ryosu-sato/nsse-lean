import NSSE.ContraSatisfiability

/-! # The signed pair graph, signed C4, and Lemma F0 (stage S6, part 1)

Note v1366 §1. Fix `POL` and a flat system `φ` with polarity-aware support `≤s`.
The **signed pair graph** `G_φ` has as vertices the supported pairs `(a, b)`,
`a ≤s b`, and an edge `(a,b) −i→ (a',b')` whenever there are an original lower
literal `f(c̄) ≤ w` with `w ≤s a` and an original upper literal `w' ≤ f(d̄)` with
`b ≤s w'`, and `(a',b') = (c_i,d_i)` at a covariant, `(d_i,c_i)` at a
contravariant `i` (`ContraSatisfiability.PairEdge`). **Signed C4** := `G_φ` has a
(nonempty) directed cycle.

Contents:
* `PairStep` (an edge out of a SUPPORTED vertex), `SignedC4` (a `TransGen` loop);
* walks `WalkFrom k p` (a walk with `k` edges starting at `p`), arbitrarily long
  walks from a cycle, and the pigeonhole converse `signedC4_iff_walk`
  (`SignedC4 ↔ ∃ p, WalkFrom (n*n) p`);
* the executable test `c4Bool` (iterated walk sets on the `n*n` vertices, edge
  relation computed from the exact support table) with `c4Bool_correct`;
* **Lemma F0** `not_finiteSatisfiable_of_c4`: a signed C4 excludes finite
  solutions (every vertex `p` met by a walk of length `k` bounds an interval
  `[ρ p.1, ρ p.2]` whose members have height `≥ k`).
-/

namespace NSSE.ContraFiniteCycles

open SubtypeConstraints (Constraints Query BoundLiteral)
open ContraTrees ContraFiniteTrees ContraConstraints ContraSupport ContraClashes
  ContraSatisfiability

variable {n d : Nat} {POL : Polarity d}

/-- Vertices of the signed pair graph (all pairs; only supported ones have
outgoing `PairStep` edges). -/
abbrev Vertex (n : Nat) := Fin n × Fin n

theorem vertex_card : Fintype.card (Vertex n) = n * n := by simp

/-- An edge of `G_φ` out of a supported vertex. -/
def PairStep (POL : Polarity d) (φ : Constraints n d) (p q : Vertex n) : Prop :=
  Support POL φ p.1 p.2 ∧ ∃ i, PairEdge POL φ p i q

/-- **Signed C4**: the signed pair graph has a nonempty directed cycle. -/
def SignedC4 (POL : Polarity d) (φ : Constraints n d) : Prop :=
  ∃ p, Relation.TransGen (PairStep POL φ) p p

/-- Targets of `PairStep` edges are supported vertices. -/
theorem pairStep_target (φ : Constraints n d) {p q : Vertex n} (h : PairStep POL φ p q) :
    Support POL φ q.1 q.2 := by
  obtain ⟨hs, i, he⟩ := h
  exact pairEdge_supported φ hs he

/-! ## Walks -/

/-- `WalkFrom k p`: a walk with `k` edges of `G_φ` starting at `p`. -/
inductive WalkFrom (POL : Polarity d) (φ : Constraints n d) : Nat → Vertex n → Prop
  | zero (p : Vertex n) : WalkFrom POL φ 0 p
  | succ {k : Nat} {p q : Vertex n} : PairStep POL φ p q → WalkFrom POL φ k q →
      WalkFrom POL φ (k + 1) p

theorem walkFrom_pred (φ : Constraints n d) :
    ∀ (k : Nat) (p : Vertex n), WalkFrom POL φ (k + 1) p → WalkFrom POL φ k p := by
  intro k
  induction k with
  | zero => intro p _; exact .zero p
  | succ k ih =>
      intro p h
      cases h with
      | succ hs w => exact .succ hs (ih _ w)

theorem walkFrom_mono (φ : Constraints n d) {k m : Nat} (hkm : k ≤ m) {p : Vertex n}
    (h : WalkFrom POL φ m p) : WalkFrom POL φ k p := by
  induction hkm with
  | refl => exact h
  | step _ ih => exact ih (walkFrom_pred φ _ _ h)

/-- A path `p →⁺ q` prepends at least one edge to any walk from `q`. -/
theorem walkFrom_of_transGen (φ : Constraints n d) {p q : Vertex n}
    (h : Relation.TransGen (PairStep POL φ) p q) :
    ∀ {k : Nat}, WalkFrom POL φ k q → WalkFrom POL φ (k + 1) p := by
  induction h using Relation.TransGen.head_induction_on with
  | base hpq => intro k w; exact .succ hpq w
  | ih hab _ ih =>
      intro k w
      exact walkFrom_pred φ _ _ (.succ hab (ih w))

/-- A cycle through `p` gives walks of every length from `p`. -/
theorem walkFrom_of_cycle (φ : Constraints n d) {p : Vertex n}
    (h : Relation.TransGen (PairStep POL φ) p p) : ∀ k, WalkFrom POL φ k p := by
  intro k
  induction k with
  | zero => exact .zero p
  | succ k ih => exact walkFrom_of_transGen φ h ih

/-- A walk as a function on positions. -/
theorem walkFrom_fun (φ : Constraints n d) {k : Nat} {p : Vertex n} (h : WalkFrom POL φ k p) :
    ∃ f : Nat → Vertex n, f 0 = p ∧ ∀ j < k, PairStep POL φ (f j) (f (j + 1)) := by
  induction h with
  | zero p => exact ⟨fun _ => p, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | @succ k p q hpq _ ih =>
      obtain ⟨f, hf0, hf⟩ := ih
      refine ⟨fun j => if j = 0 then p else f (j - 1), by simp, ?_⟩
      intro j hj
      rcases j with _ | j
      · simpa [hf0] using hpq
      · simpa using hf j (by omega)

theorem transGen_of_fun (φ : Constraints n d) {k : Nat} {f : Nat → Vertex n}
    (hf : ∀ j < k, PairStep POL φ (f j) (f (j + 1))) :
    ∀ (m j : Nat), j + m + 1 ≤ k → Relation.TransGen (PairStep POL φ) (f j) (f (j + m + 1)) := by
  intro m
  induction m with
  | zero => intro j hj; exact .single (hf j (by omega))
  | succ m ih =>
      intro j hj
      have h1 := ih j (by omega)
      have h2 := hf (j + m + 1) (by omega)
      exact .tail h1 (by simpa [Nat.add_assoc] using h2)

/-- **Pigeonhole.** A walk with `n*n` edges revisits a vertex, hence closes a cycle. -/
theorem signedC4_of_walk (φ : Constraints n d) {p : Vertex n} (h : WalkFrom POL φ (n * n) p) :
    SignedC4 POL φ := by
  obtain ⟨f, _, hf⟩ := walkFrom_fun φ h
  let g : Fin (n * n + 1) → Vertex n := fun j => f j.1
  have hcard : Fintype.card (Vertex n) < Fintype.card (Fin (n * n + 1)) := by
    rw [vertex_card, Fintype.card_fin]; omega
  obtain ⟨x, y, hxy, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  have hx := x.2
  have hy := y.2
  have hne : x.1 ≠ y.1 := fun h => hxy (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · refine ⟨f x.1, ?_⟩
    have := transGen_of_fun φ hf (y.1 - x.1 - 1) x.1 (by omega)
    have he : x.1 + (y.1 - x.1 - 1) + 1 = y.1 := by omega
    rw [he] at this
    have hg' : f x.1 = f y.1 := hg
    rwa [← hg'] at this
  · refine ⟨f y.1, ?_⟩
    have := transGen_of_fun φ hf (x.1 - y.1 - 1) y.1 (by omega)
    have he : y.1 + (x.1 - y.1 - 1) + 1 = x.1 := by omega
    rw [he] at this
    have hg' : f x.1 = f y.1 := hg
    rwa [hg'] at this

/-- Signed C4 iff some vertex starts a walk with `n*n` edges. -/
theorem signedC4_iff_walk (φ : Constraints n d) :
    SignedC4 POL φ ↔ ∃ p, WalkFrom POL φ (n * n) p :=
  ⟨fun ⟨p, hp⟩ => ⟨p, walkFrom_of_cycle φ hp _⟩, fun ⟨_, hp⟩ => signedC4_of_walk φ hp⟩

/-! ## The executable cycle test -/

/-- Boolean edge test from a support matrix `rel`. -/
def stepB (POL : Polarity d) (φ : Constraints n d) (rel : Fin n → Fin n → Bool)
    (p q : Vertex n) : Bool :=
  rel p.1 p.2 && φ.lower.any (fun a => rel a.1 p.1 && φ.upper.any (fun b => rel p.2 b.1 &&
    decide (∃ i : Fin d, q = if POL i = true then (b.2 i, a.2 i) else (a.2 i, b.2 i))))

theorem stepB_correct (φ : Constraints n d) (p q : Vertex n) :
    stepB POL φ (table POL φ) p q = true ↔ PairStep POL φ p q := by
  simp only [stepB, Bool.and_eq_true, List.any_eq_true, table_correct, decide_eq_true_eq]
  constructor
  · rintro ⟨hs, a, ha, h1, b, hb, h2, i, hq⟩
    exact ⟨hs, i, a, ha, b, hb, h1, h2, hq⟩
  · rintro ⟨hs, i, a, ha, b, hb, h1, h2, hq⟩
    exact ⟨hs, a, ha, h1, b, hb, h2, i, hq⟩

/-- Vertices starting a walk with `k` edges, computed level by level. -/
def walkSet (step : Vertex n → Vertex n → Bool) : Nat → Finset (Vertex n)
  | 0 => Finset.univ
  | k + 1 =>
      let W := walkSet step k
      Finset.univ.filter (fun p => ∃ q ∈ W, step p q = true)

theorem mem_walkSet (φ : Constraints n d) (k : Nat) (p : Vertex n) :
    p ∈ walkSet (stepB POL φ (table POL φ)) k ↔ WalkFrom POL φ k p := by
  induction k generalizing p with
  | zero => simp only [walkSet, Finset.mem_univ, true_iff]; exact .zero p
  | succ k ih =>
      simp only [walkSet, Finset.mem_filter, Finset.mem_univ, true_and, stepB_correct, ih]
      constructor
      · rintro ⟨q, hq, hs⟩; exact .succ hs hq
      · intro h
        cases h with
        | succ hs w => exact ⟨_, w, hs⟩

/-- **The executable signed-C4 test** (`|V| = n*n` levels of walk sets). -/
def c4Bool (POL : Polarity d) (φ : Constraints n d) : Bool :=
  let rel := table POL φ
  decide (walkSet (stepB POL φ rel) (n * n)).Nonempty

theorem c4Bool_correct (φ : Constraints n d) : c4Bool POL φ = true ↔ SignedC4 POL φ := by
  rw [signedC4_iff_walk]
  simp only [c4Bool, decide_eq_true_eq, Finset.Nonempty, mem_walkSet]

instance (φ : Constraints n d) : Decidable (SignedC4 POL φ) :=
  decidable_of_iff _ (c4Bool_correct φ)

/-! ## Lemma F0: a signed C4 excludes finite solutions -/

theorem FTree.not_node_le_bot (c : Fin d → FTree POL) : ¬ FTree.node c ≤ (FTree.bot : FTree POL) := by
  intro h
  rw [le_iff_below] at h
  cases h

theorem FTree.not_top_le_node (c : Fin d → FTree POL) : ¬ (FTree.top : FTree POL) ≤ FTree.node c := by
  intro h
  rw [le_iff_below] at h
  cases h

/-- Members of the interval of a vertex that starts a walk with `k` edges have
height at least `k` (the walk's edges force nodes along a path). -/
theorem walk_height (φ : Constraints n d) (ρ : Fin n → FTree POL)
    (hρ : Satisfies (finiteConstructor POL) φ ρ) {k : Nat} {p : Vertex n}
    (h : WalkFrom POL φ k p) :
    ∀ t : FTree POL, ρ p.1 ≤ t → t ≤ ρ p.2 → k ≤ height t := by
  induction h with
  | zero p => intro t _ _; exact Nat.zero_le _
  | @succ k p q hpq _ ih =>
      intro t hlt hut
      obtain ⟨_, i, a, ha, b, hb, h1, h2, hq⟩ := hpq
      have hlow : FTree.node (fun j => ρ (a.2 j)) ≤ t :=
        ((hρ.2.1 a ha).trans (support_sound (finiteConstructor POL) φ ρ hρ h1)).trans hlt
      have hup : t ≤ FTree.node (fun j => ρ (b.2 j)) :=
        hut.trans ((support_sound (finiteConstructor POL) φ ρ hρ h2).trans (hρ.1 b hb))
      cases t with
      | bot => exact absurd hlow (FTree.not_node_le_bot _)
      | top => exact absurd hup (FTree.not_top_le_node _)
      | node c =>
          have hl := ((FTree.node_le_node _ _).mp hlow) i
          have hu := ((FTree.node_le_node _ _).mp hup) i
          have hk : k ≤ height (c i) := by
            cases hpi : POL i
            · have hq' : q = (a.2 i, b.2 i) := by simpa [hpi] using hq
              subst hq'
              exact ih (c i) (hl.2 hpi) (hu.2 hpi)
            · have hq' : q = (b.2 i, a.2 i) := by simpa [hpi] using hq
              subst hq'
              exact ih (c i) (hu.1 hpi) (hl.1 hpi)
          exact Nat.succ_le_of_lt (lt_of_le_of_lt hk (child_height_lt c i))

/-- **Lemma F0 (v1366 §1).** A signed C4 excludes finite solutions. -/
theorem not_finiteSatisfiable_of_c4 {φ : Constraints n d} (h : SignedC4 POL φ) :
    ¬ Satisfiable (finiteConstructor POL) φ := by
  rintro ⟨ρ, hρ⟩
  obtain ⟨p, hp⟩ := h
  have w := walkFrom_of_cycle φ hp (height (ρ p.1) + 1)
  have hs : Support POL φ p.1 p.2 := by
    cases w with
    | succ hs _ => exact hs.1
  have := walk_height φ ρ hρ w (ρ p.1) le_rfl (support_sound (finiteConstructor POL) φ ρ hρ hs)
  omega

/-- The covariant reading: for `POL = (+,…,+)` an edge is the covariant
decomposition step. -/
theorem pairStep_covariant (hPOL : ∀ i, POL i = false) (φ : Constraints n d) (p q : Vertex n) :
    PairStep POL φ p q ↔ Support POL φ p.1 p.2 ∧ ∃ i, ∃ a ∈ φ.lower, ∃ b ∈ φ.upper,
      Support POL φ a.1 p.1 ∧ Support POL φ p.2 b.1 ∧ q = (a.2 i, b.2 i) := by
  simp [PairStep, PairEdge, hPOL]

end NSSE.ContraFiniteCycles
