import NSSE.ContraAutomaton
import NSSE.AbsorbingForwardSoundness
import NSSE.ContraSatisfiability

/-! # Soundness of the polarity-bit set-token automaton (contravariant NSSE, stage S3)

notes_v1362 §3 (Lemmas 3–6, Proposition (soundness)), v1361 §3 and §6 (odd-root P-edges,
Codex's argument).

**Safety.** By the encoding lemma (S1, `le_iff_plabel`), `s ≤ t` in the original order iff
`plabel(s, w) ≤ plabel(t, w)` for every word `w`. A word `w` is left-safe for `(s, t)` if
`plabel(s,w) = T → plabel(t,w) = T` and right-safe if `plabel(t,w) = B → plabel(s,w) = B`
(`CSafe`, stated on the raw trees through `plabel`). Through `E` this is the covariant label
safety `AbsorbingSubtypeSafety.Safe` of the encodings (`csafe_iff_safe`).

**Meaning of a state** (`Bounds`). For a valuation `τ` of encoded trees, a triple
`(S_x, S_y, σ)` bounds a pair of (encoded) trees `(a, b)` if `a ≤ dualIf σ (τ u)` for
`u ∈ S_x` and `dualIf σ (τ v) ≤ b` for `v ∈ S_y`. With `τ = E ∘ ρ` and all prefixes nodes,
`project (E ρ(x)) p = dualIf (pol p) (E (P_p ρ(x)))`, so this is exactly the meaning of
v1362 §3 (upper bounds at `+`, lower bounds at `−`), but it is stated without any
node-prefix premise: absorbed leaves are handled by the covariant label calculus.

All semantic statements are proved for an arbitrary valuation of encoded trees satisfying
the table facts (`EncSound`), and `encSound_of_satisfies` derives these facts from any
solution over arbitrary contravariant trees. Regular and finite solutions are special cases.
-/

namespace NSSE.ContraSoundness

open GuardedBlockRelation
open SubtypeConstraints (Constraints Query)
open AbsorbingSubtypeTrees AbsorbingSubtypeSafety
open ContraTrees ContraFiniteTrees ContraRegularTrees ContraConstraints ContraSupport ContraAutomaton
open ForwardTableAutomaton (Side)

variable {n d : Nat} {POL : Polarity d}

/-! ## Label facts -/

theorem label_le_zero {a : Label} (h : a ≤ 0) : a = 0 := by
  fin_cases a <;> simp_all

theorem two_le_label {a : Label} (h : 2 ≤ a) : a = 2 := by
  fin_cases a <;> simp_all

theorem swap_eq_two {a : Label} : swap a = 2 ↔ a = 0 := by fin_cases a <;> decide
theorem swap_eq_zero {a : Label} : swap a = 0 ↔ a = 2 := by fin_cases a <;> decide

theorem project_dualIf (σ : Bool) (t : Tree d) (p : List (Fin d)) :
    project (dualIf σ t) p = dualIf σ (project t p) := by
  cases σ
  · rfl
  · exact (dual_project t p).symm

theorem dualIf_not (σ : Bool) (t : Tree d) : dualIf (!σ) t = dual (dualIf σ t) := by
  cases σ <;> simp

theorem dualIf_le_dualIf (σ : Bool) {s t : Tree d} (h : s ≤ t) :
    (if σ then dualIf σ t ≤ dualIf σ s else dualIf σ s ≤ dualIf σ t) := by
  cases σ
  · exact h
  · simpa using h

/-! ## Safety in the original order -/

/-- Left/right safety of a word for a pair of ORIGINAL trees, in polarity-adjusted labels. -/
def CSafe (POL : Polarity d) (side : Side) (s t : CTree POL) (w : List (Fin d)) : Prop :=
  match side with
  | .left => plabel POL false s.raw w = 2 → plabel POL false t.raw w = 2
  | .right => plabel POL false t.raw w = 0 → plabel POL false s.raw w = 0

theorem csafe_iff_safe (side : Side) (s t : CTree POL) (w : List (Fin d)) :
    CSafe POL side s t w ↔ Safe side (E POL s) (E POL t) w := by
  cases side <;> rfl

/-- Pointwise criterion (v1362 Lemma 1 and the two failure modes): the original order is
universal left and right safety. -/
theorem le_iff_all_csafe (s t : CTree POL) : s ≤ t ↔ ∀ side w, CSafe POL side s t w := by
  rw [← E_le_iff, below_iff_all_safe]
  simp only [csafe_iff_safe]

/-- Query safety over arbitrary contravariant trees. -/
def QuerySafe (POL : Polarity d) (Q : Query n d) (side : Side) (w : List (Fin d)) : Prop :=
  ∀ ρ : Fin n → CTree POL, Satisfies (treeConstructor POL) Q.constraints ρ →
    CSafe POL side (ρ Q.left) (ρ Q.right) w

def RegularQuerySafe (POL : Polarity d) (Q : Query n d) (side : Side) (w : List (Fin d)) : Prop :=
  ∀ ρ : Fin n → CTree POL, (∀ x, CRegular (ρ x)) → Satisfies (treeConstructor POL) Q.constraints ρ →
    CSafe POL side (ρ Q.left) (ρ Q.right) w

def FiniteQuerySafe (POL : Polarity d) (Q : Query n d) (side : Side) (w : List (Fin d)) : Prop :=
  ∀ ρ : Fin n → FTree POL, Satisfies (finiteConstructor POL) Q.constraints ρ →
    CSafe POL side (toC (ρ Q.left)) (toC (ρ Q.right)) w

theorem entails_iff_all_safe (Q : Query n d) :
    Entails (treeConstructor POL) Q ↔ ∀ side w, QuerySafe POL Q side w := by
  constructor
  · intro h side w ρ hρ; exact (le_iff_all_csafe _ _).mp (h ρ hρ) side w
  · intro h ρ hρ; exact (le_iff_all_csafe _ _).mpr (fun side w => h side w ρ hρ)

theorem regularEntails_iff_all_safe (Q : Query n d) :
    RegularEntails POL Q ↔ ∀ side w, RegularQuerySafe POL Q side w := by
  constructor
  · intro h side w ρ hr hρ; exact (le_iff_all_csafe _ _).mp (h ρ hr hρ) side w
  · intro h ρ hr hρ; exact (le_iff_all_csafe _ _).mpr (fun side w => h side w ρ hr hρ)

theorem finiteEntails_iff_all_safe (Q : Query n d) :
    Entails (finiteConstructor POL) Q ↔ ∀ side w, FiniteQuerySafe POL Q side w := by
  constructor
  · intro h side w ρ hρ
    exact (le_iff_all_csafe _ _).mp ((toC_le_iff _ _).mpr (h ρ hρ)) side w
  · intro h ρ hρ
    exact (toC_le_iff _ _).mp ((le_iff_all_csafe _ _).mpr (fun side w => h side w ρ hρ))

theorem querySafe_regular {Q : Query n d} {side : Side} {w : List (Fin d)}
    (h : QuerySafe POL Q side w) : RegularQuerySafe POL Q side w := fun ρ _ hρ => h ρ hρ

theorem querySafe_finite {Q : Query n d} {side : Side} {w : List (Fin d)}
    (h : QuerySafe POL Q side w) : FiniteQuerySafe POL Q side w := fun ρ hρ =>
  h (fun x => toC (ρ x)) ((finite_satisfies_iff _ ρ).mp hρ)

/-! ## The table facts in encoded form -/

/-- What the automaton needs to know about a valuation `τ` of ENCODED trees: the five tables
are sound, with the contravariant child dualized (`dualIf (POL i)`). -/
structure EncSound (D : Tables n d) (POL : Polarity d) (τ : Fin n → Tree d) : Prop where
  le : ∀ u v, D.le u v = true → τ u ≤ τ v
  upper : ∀ u i z, D.upper u i z = true →
    project (τ u) [i] ≤ dualIf (POL i) (τ z) ∧ (τ u).label [] ≠ 2
  lower : ∀ u i z, D.lower u i z = true →
    dualIf (POL i) (τ z) ≤ project (τ u) [i] ∧ (τ u).label [] ≠ 0
  bot : ∀ u, D.bot u = true → τ u = ⊥
  top : ∀ u, D.top u = true → τ u = ⊤

/-- Every solution over arbitrary contravariant trees gives sound tables for its encoding
(v1362 Lemma 2). -/
theorem encSound_of_satisfies (φ : Constraints n d) (ρ : Fin n → CTree POL)
    (hρ : Satisfies (treeConstructor POL) φ ρ) :
    EncSound (tables POL φ) POL (fun x => E POL (ρ x)) where
  le u v h := (E_le_iff _ _).mpr (computed_le_sound (treeConstructor POL) φ ρ hρ h)
  upper u i z h := by
    obtain ⟨c, hc, hle⟩ := computed_upper_sound (treeConstructor POL) φ ρ hρ h
    have he : E POL (ρ u) ≤ E POL (CTree.node c) := (E_le_iff _ _).mpr hle
    rw [E_node] at he
    refine ⟨?_, ?_⟩
    · have := project_mono he [i]
      simpa only [project_node, project_nil, hc] using this
    · intro h2
      have := he []
      rw [h2, node_label_nil] at this
      exact absurd this (by decide)
  lower u i z h := by
    obtain ⟨c, hc, hle⟩ := computed_lower_sound (treeConstructor POL) φ ρ hρ h
    have he : E POL (CTree.node c) ≤ E POL (ρ u) := (E_le_iff _ _).mpr hle
    rw [E_node] at he
    refine ⟨?_, ?_⟩
    · have := project_mono he [i]
      simpa only [project_node, project_nil, hc] using this
    · intro h0
      have := he []
      rw [h0, node_label_nil] at this
      exact absurd this (by decide)
  bot u h := by
    simp only [computed_bot_sound (treeConstructor POL) φ ρ hρ h, E_bot]
  top u h := by
    simp only [computed_top_sound (treeConstructor POL) φ ρ hρ h, E_top]

section Valuation

variable {D : Tables n d} {τ : Fin n → Tree d} (hτ : EncSound D POL τ)
include hτ

theorem leS_enc {σ : Bool} {u v : Fin n} (h : LeS D σ u v = true) :
    dualIf σ (τ u) ≤ dualIf σ (τ v) := by
  cases σ
  · exact hτ.le u v h
  · simpa using hτ.le v u h

theorem xBot_enc {σ : Bool} {u : Fin n} (h : xBot D σ u = true) : dualIf σ (τ u) = ⊥ := by
  cases σ
  · exact hτ.bot u h
  · simp [hτ.top u h]

theorem yTop_enc {σ : Bool} {v : Fin n} (h : yTop D σ v = true) : dualIf σ (τ v) = ⊤ := by
  cases σ
  · exact hτ.top v h
  · simp [hτ.bot v h]

/-- One x-move: the child bound in encoded form, and the source is not a real ⊤ in plabels. -/
theorem xMove_enc {σ : Bool} {u z : Fin n} {i : Fin d} (h : xMove D σ u i z = true) :
    project (dualIf σ (τ u)) [i] ≤ dualIf (xor σ (POL i)) (τ z) ∧
      (dualIf σ (τ u)).label [] ≠ 2 := by
  cases σ
  · simpa [xMove] using hτ.upper u i z h
  · obtain ⟨h1, h2⟩ := hτ.lower u i z h
    refine ⟨?_, ?_⟩
    · rw [project_dualIf, dualIf_xor, dualIf_true, dualIf_true]
      exact (dual_le_dual _ _).mpr h1
    · simpa [dualIf_label, swap_eq_two] using h2

/-- One y-move: the child bound in encoded form, and the source is not a real ⊥ in plabels. -/
theorem yMove_enc {σ : Bool} {v z : Fin n} {i : Fin d} (h : yMove D σ v i z = true) :
    dualIf (xor σ (POL i)) (τ z) ≤ project (dualIf σ (τ v)) [i] ∧
      (dualIf σ (τ v)).label [] ≠ 0 := by
  cases σ
  · simpa [yMove] using hτ.lower v i z h
  · obtain ⟨h1, h2⟩ := hτ.upper v i z h
    refine ⟨?_, ?_⟩
    · rw [project_dualIf, dualIf_xor, dualIf_true, dualIf_true]
      exact (dual_le_dual _ _).mpr h1
    · simpa [dualIf_label, swap_eq_zero] using h2

omit hτ in
/-- The meaning of a triple: the bounds it puts on a pair of encoded subtrees. -/
def Bounds (τ : Fin n → Tree d) (q : Triple n) (a b : Tree d) : Prop :=
  (∀ u, q.1 u = true → a ≤ dualIf q.2.2 (τ u)) ∧ (∀ v, q.2.1 v = true → dualIf q.2.2 (τ v) ≤ b)

omit hτ in
/-- Safety of a state for a word: every pair it bounds is safe. `ALL` is safe for all words. -/
def StateSafe (τ : Fin n → Tree d) (side : Side) : State n → List (Fin d) → Prop
  | none, _ => True
  | some q, w => ∀ a b, Bounds τ q a b → Safe side a b w

theorem escape_le {q : Triple n} (h : Escape D q) {a b : Tree d} (hb : Bounds τ q a b) : a ≤ b := by
  rcases h with ⟨u, hu, hx⟩ | ⟨v, hv, hy⟩ | ⟨u, v, hu, hv, hl⟩
  · have := hb.1 u hu
    rw [xBot_enc hτ hx] at this
    exact this.trans bot_le
  · have := hb.2 v hv
    rw [yTop_enc hτ hy] at this
    exact le_top.trans this
  · exact (hb.1 u hu).trans ((leS_enc hτ hl).trans (hb.2 v hv))

/-- v1362 Lemma 4: every final state is safe for `ε` on its side; escapes for every word. -/
theorem escape_safe {q : Triple n} (h : Escape D q) (side : Side) (w : List (Fin d)) :
    StateSafe τ side (some q) w :=
  fun _ _ hb => below_safe (escape_le hτ h hb) side w

theorem final_safe (side : Side) {q : State n} (h : Final D side q) : StateSafe τ side q [] := by
  cases q with
  | none => trivial
  | some q =>
      intro a b hb
      rcases h with he | ⟨v, i, z, hv, hm⟩
      · exact below_safe (escape_le hτ he hb) side []
      · cases side with
        | left =>
            have h1 := hb.1 v hv
            have h2 := (xMove_enc hτ hm).2
            intro ha
            exact absurd (two_le_label (ha ▸ h1 [])) h2
        | right =>
            have h1 := hb.2 v hv
            have h2 := (yMove_enc hτ hm).2
            intro hb0
            exact absurd (label_le_zero (hb0 ▸ h1 [])) h2

/-- The bounds propagate along one letter of a non-escape triple (v1362 Lemma 3, the meaning). -/
theorem bounds_next {q : Triple n} {a b : Tree d} (hb : Bounds τ q a b) (i : Fin d) :
    Bounds τ (next D POL q i) (project a [i]) (project b [i]) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨u, hu, hm⟩ := of_decide_eq_true hz
    exact (project_mono (hb.1 u hu) [i]).trans (xMove_enc hτ hm).1
  · intro z hz
    obtain ⟨v, hv, hm⟩ := of_decide_eq_true hz
    exact (yMove_enc hτ hm).1.trans (project_mono (hb.2 v hv) [i])

/-- v1362 Lemma 3 (one step back). -/
theorem step_lift (side : Side) (q : State n) (i : Fin d) (tail : List (Fin d))
    (ht : StateSafe τ side (delta D POL q i) tail) : StateSafe τ side q (i :: tail) := by
  cases q with
  | none => trivial
  | some q =>
      by_cases he : Escape D q
      · exact escape_safe hτ he side _
      · rw [delta_proper D POL he] at ht
        intro a b hb
        exact (safe_append side a b [i] tail).mpr (ht _ _ (bounds_next hτ hb i))

theorem run_lift (side : Side) (q : State n) (path tail : List (Fin d))
    (ht : StateSafe τ side (run D POL q path) tail) : StateSafe τ side q (path ++ tail) := by
  induction path generalizing q with
  | nil => exact ht
  | cons i path ih => exact step_lift hτ side q i _ (ih _ ht)

/-- The meaning along a proper run. -/
theorem bounds_run {q r : Triple n} {path : List (Fin d)} (h : run D POL (some q) path = some r)
    {a b : Tree d} (hb : Bounds τ q a b) : Bounds τ r (project a path) (project b path) := by
  induction path generalizing q a b with
  | nil =>
      simp only [run_nil, Option.some.injEq] at h
      subst h
      simpa only [project_nil] using hb
  | cons i path ih =>
      rw [run_cons] at h
      by_cases he : Escape D q
      · rw [delta_escape D POL he, run_all] at h; exact Option.noConfusion h
      · rw [delta_proper D POL he] at h
        have := ih h (bounds_next hτ hb i)
        simpa only [← project_append, List.singleton_append] using this

omit hτ in
theorem start_bounds (x y : Fin n) :
    ∃ q, start x y = some q ∧ Bounds τ q (τ x) (τ y) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · intro u hu
    have : u = x := of_decide_eq_true hu
    subst this; exact le_rfl
  · intro v hv
    have : v = y := of_decide_eq_true hv
    subst this; exact le_rfl

/-- The state meaning at every word: after `p`, the state reached from `({x},{y},+)` bounds
`(project (τ x) p, project (τ y) p)`, and its polarity bit is `pathPol POL p`. -/
theorem meaning (x y : Fin n) (p : List (Fin d)) {r : Triple n}
    (h : run D POL (start x y) p = some r) :
    Bounds τ r (project (τ x) p) (project (τ y) p) ∧ r.2.2 = pathPol POL p := by
  obtain ⟨q, hq, hb⟩ := start_bounds (τ := τ) x y
  rw [hq] at h
  refine ⟨bounds_run hτ h hb, ?_⟩
  have := start_sigma D POL (x := x) (y := y) (hq ▸ h)
  exact this

/-! ### Periodic tails (Lemmas 5 and 6) -/

omit hτ in
/-- Odd root, right side (Codex's argument, v1361 §6): if `c ≤ b` and `dual c ≤ P_r b`, then
`b` reads no `B` on `pr(r*)`. -/
theorem odd_right {c b : Tree d} (root tail : List (Fin d)) (hc : c ≤ b)
    (hd : dual c ≤ project b root) (hp : tail <+: root ++ tail) : b.label tail ≠ 0 := by
  intro h0
  rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append root tail) with h | h
  · -- `tail` is a prefix of the root: the leaf ⊥ at `tail` absorbs the whole root
    obtain ⟨m, rfl⟩ := h
    have hb : ∀ w, b.label (tail ++ m ++ w) = 0 := by
      intro w
      rw [List.append_assoc, b.absorbs tail (m ++ w) (by rw [h0]; decide), h0]
    have hcw : c.label tail = 2 := by
      have := hd tail
      simp only [dual_label, project_label, hb] at this
      exact swap_eq_zero.mp (label_le_zero this)
    have := hc tail
    rw [hcw, h0] at this
    exact absurd this (by decide)
  · obtain ⟨u, rfl⟩ := h
    have hu : u <+: root ++ u := (List.prefix_append_right_inj root).mp hp
    have h1 := hd u
    simp only [dual_label, project_label, h0] at h1
    have hcu : c.label u = 2 := swap_eq_zero.mp (label_le_zero h1)
    have hbu : b.label u = 2 := two_le_label (hcu ▸ hc u)
    obtain ⟨m, hm⟩ := hu
    have := b.absorbs u m (by rw [hbu]; decide)
    rw [hm, hbu, h0] at this
    exact absurd this (by decide)

omit hτ in
/-- Odd root, left side: if `a ≤ c` and `P_r a ≤ dual c`, then `a` reads no `T` on `pr(r*)`. -/
theorem odd_left {a c : Tree d} (root tail : List (Fin d)) (hc : a ≤ c)
    (hd : project a root ≤ dual c) (hp : tail <+: root ++ tail) : a.label tail ≠ 2 := by
  intro h2
  rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append root tail) with h | h
  · obtain ⟨m, rfl⟩ := h
    have ha : ∀ w, a.label (tail ++ m ++ w) = 2 := by
      intro w
      rw [List.append_assoc, a.absorbs tail (m ++ w) (by rw [h2]; decide), h2]
    have hcw : c.label tail = 0 := by
      have := hd tail
      simp only [dual_label, project_label, ha] at this
      exact swap_eq_two.mp (two_le_label this)
    have := hc tail
    rw [hcw, h2] at this
    exact absurd this (by decide)
  · obtain ⟨u, rfl⟩ := h
    have hu : u <+: root ++ u := (List.prefix_append_right_inj root).mp hp
    have h1 := hd u
    simp only [dual_label, project_label, h2] at h1
    have hcu : c.label u = 0 := swap_eq_two.mp (two_le_label h1)
    have hau : a.label u = 0 := label_le_zero (hcu ▸ hc u)
    obtain ⟨m, hm⟩ := hu
    have := a.absorbs u m (by rw [hau]; decide)
    rw [hm, hau, h2] at this
    exact absurd this (by decide)

/-- v1362 Lemmas 5 and 6: a P-edge certifies safety of its target on every prefix of a power
of the root (even roots: the covariant periodic argument on encodings; odd roots: the
self-relation argument). -/
theorem pedge_safe (side : Side) {q s : State n} (root tail : List (Fin d)) (k : Nat)
    (hr : s = run D POL q root) (hp : PEdge D side s q)
    (ht : tail <+: Language.wordPower root k) : StateSafe τ side q tail := by
  have hword := AbsorbingForwardSoundness.prefix_root_self root tail k ht
  cases q with
  | none => trivial
  | some q =>
      cases s with
      | none => cases side <;> exact False.elim hp
      | some s =>
          intro a b hb
          have hb' := bounds_run hτ hr.symm hb
          cases side with
          | right =>
              simp only [PEdge] at hp
              by_cases hpar : xor q.2.2 s.2.2 = true
              · rw [if_pos hpar] at hp
                obtain ⟨v', l, hv', hl, hle⟩ := hp
                have hs : s.2.2 = !q.2.2 := by
                  cases hq : q.2.2 <;> cases hs : s.2.2 <;> simp_all
                have hd : dual (dualIf q.2.2 (τ l)) ≤ project b root := by
                  rw [← dualIf_not, ← hs]
                  exact (leS_enc hτ hle).trans (hb'.2 v' hv')
                intro h0
                exact absurd h0 (odd_right root tail (hb.2 l hl) hd hword)
              · rw [if_neg hpar] at hp
                obtain ⟨u, v', hu, hv', hle⟩ := hp
                have hs : s.2.2 = q.2.2 := by
                  cases hq : q.2.2 <;> cases hs : s.2.2 <;> simp_all
                have hab : a ≤ project b root := by
                  refine (hb.1 u hu).trans ((leS_enc hτ hle).trans ?_)
                  have := hb'.2 v' hv'
                  rwa [hs] at this
                exact periodic_right a b root tail hab hword
          | left =>
              simp only [PEdge] at hp
              by_cases hpar : xor q.2.2 s.2.2 = true
              · rw [if_pos hpar] at hp
                obtain ⟨u, u', hu, hu', hle⟩ := hp
                have hs : s.2.2 = !q.2.2 := by
                  cases hq : q.2.2 <;> cases hs : s.2.2 <;> simp_all
                have hd : project a root ≤ dual (dualIf q.2.2 (τ u)) := by
                  rw [← dualIf_not, ← hs]
                  exact (hb'.1 u' hu').trans (leS_enc hτ hle)
                intro h2
                exact absurd h2 (odd_left root tail (hb.1 u hu) hd hword)
              · rw [if_neg hpar] at hp
                obtain ⟨u', l, hu', hl, hle⟩ := hp
                have hs : s.2.2 = q.2.2 := by
                  cases hq : q.2.2 <;> cases hs : s.2.2 <;> simp_all
                have hab : project a root ≤ b := by
                  have := hb'.1 u' hu'
                  rw [hs] at this
                  exact this.trans ((leS_enc hτ hle).trans (hb.2 l hl))
                exact periodic_left a b root tail hab hword

/-- Ordinary acceptance is sound (Lemma 4, then Lemma 3 backwards). -/
theorem raw_accepts_safe (side : Side) (x y : Fin n) (path : List (Fin d))
    (h : (rawNFA D POL side x y).Accepts path) : Safe side (τ x) (τ y) path := by
  rw [accepts_iff] at h
  have hs := run_lift hτ side (start x y) path [] (final_safe hτ side h)
  rw [List.append_nil] at hs
  obtain ⟨q, hq, hb⟩ := start_bounds (τ := τ) x y
  rw [hq] at hs
  exact hs _ _ hb

/-- Acceptance of the compiled automaton (ordinary or P-edge) is sound, for any valuation of
encoded trees with sound tables (Proposition (soundness) of v1362 §3). -/
theorem compile_accepts_safe (side : Side) (x y : Fin n) (path : List (Fin d))
    (h : ForwardCapAutomaton.Accepts (compile D POL side x y) path) : Safe side (τ x) (τ y) path := by
  obtain ⟨q, hq, hb⟩ := start_bounds (τ := τ) x y
  rcases h with h | h
  · obtain ⟨r, hr, hf⟩ := (ForwardCapAutomaton.ordinary_accepts _ path).mp h
    apply raw_accepts_safe hτ side x y path
    refine ⟨start x y, (stateEquiv n).symm r, rfl, ?_, hf⟩
    simpa only [compile, Equiv.symm_apply_apply] using decode_run D POL side x y hr
  · obtain ⟨anchor, tail, q0, src, root, k, rfl, ha, _hf, hr, hp, ht⟩ := h
    have hr' := (compile_runs_iff D POL side x y _ _ root).mp hr
    have hs := pedge_safe hτ side root tail k hr' hp ht
    have ha' := (compile_runs_iff D POL side x y _ _ anchor).mp ha
    have hstart : (stateEquiv n).symm (compile D POL side x y).start = start x y := by
      simp [compile]
    rw [hstart] at ha'
    rw [ha'] at hs
    have hl := run_lift hτ side (start x y) anchor tail hs
    rw [hq] at hl
    exact hl _ _ hb

end Valuation

/-! ## Soundness for constraint queries -/

/-- **Soundness (v1362 §3 Proposition).** If the side automaton of `Q` accepts `w`, then `w`
is safe on that side in EVERY solution over arbitrary contravariant trees. -/
theorem accepts_sound (Q : Query n d) (side : Side) (w : List (Fin d))
    (h : ForwardCapAutomaton.Accepts (automaton POL Q side) w) : QuerySafe POL Q side w := by
  intro ρ hρ
  rw [csafe_iff_safe]
  exact compile_accepts_safe (encSound_of_satisfies Q.constraints ρ hρ) side Q.left Q.right w h

theorem accepts_regular_sound (Q : Query n d) (side : Side) (w : List (Fin d))
    (h : ForwardCapAutomaton.Accepts (automaton POL Q side) w) : RegularQuerySafe POL Q side w :=
  querySafe_regular (accepts_sound Q side w h)

theorem accepts_finite_sound (Q : Query n d) (side : Side) (w : List (Fin d))
    (h : ForwardCapAutomaton.Accepts (automaton POL Q side) w) : FiniteQuerySafe POL Q side w :=
  querySafe_finite (accepts_sound Q side w h)

theorem universal_entails (Q : Query n d)
    (hl : ForwardCapAutomaton.Universal (automaton POL Q .left))
    (hr : ForwardCapAutomaton.Universal (automaton POL Q .right)) :
    Entails (treeConstructor POL) Q := by
  apply (entails_iff_all_safe Q).mpr
  intro side w
  cases side with
  | left => exact accepts_sound Q .left w (hl w)
  | right => exact accepts_sound Q .right w (hr w)

/-- Positive answers of the Part II decision on both sides are genuine entailments over
arbitrary, regular and finite contravariant trees. -/
theorem decideBothSides_sound (Q : Query n d) (h : decideBothSides POL Q = true) :
    Entails (treeConstructor POL) Q := by
  obtain ⟨hl, hr⟩ := (decideBothSides_correct POL Q).mp h
  exact universal_entails Q hl hr

theorem decideBothSides_regular_sound (Q : Query n d) (h : decideBothSides POL Q = true) :
    RegularEntails POL Q :=
  regularEntails_of_entails Q (decideBothSides_sound Q h)

theorem decideBothSides_finite_sound (Q : Query n d) (h : decideBothSides POL Q = true) :
    Entails (finiteConstructor POL) Q :=
  finiteEntails_of_regularEntails Q (decideBothSides_regular_sound Q h)

/-- The candidate decision of v1365 §2: unsatisfiable, or both sides universal. Its positive
answers are sound (for every tree kind); the converse (completeness) is stage S4. -/
def decideEntails (POL : Polarity d) (Q : Query n d) : Bool :=
  !ContraSatisfiability.decideSatisfiable POL Q.constraints || decideBothSides POL Q

theorem decideEntails_sound (Q : Query n d) (h : decideEntails POL Q = true) :
    Entails (treeConstructor POL) Q := by
  simp only [decideEntails, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · exact ContraSatisfiability.entails_of_decide_false Q h
  · exact decideBothSides_sound Q h

theorem decideEntails_regular_sound (Q : Query n d) (h : decideEntails POL Q = true) :
    RegularEntails POL Q :=
  regularEntails_of_entails Q (decideEntails_sound Q h)

theorem decideEntails_finite_sound (Q : Query n d) (h : decideEntails POL Q = true) :
    Entails (finiteConstructor POL) Q :=
  finiteEntails_of_regularEntails Q (decideEntails_regular_sound Q h)

/-! ## Interface for S4 (completeness) -/

/-- The state of the side automaton of `Q` after a word (ordinary runs are deterministic). -/
def stateAt (POL : Polarity d) (Q : Query n d) (w : List (Fin d)) : State n :=
  run (tables POL Q.constraints) POL (start Q.left Q.right) w

/-- Ordinary acceptance of the compiled side automaton is finality of `stateAt`. -/
theorem ordinary_accepts_iff (Q : Query n d) (side : Side) (w : List (Fin d)) :
    (ForwardCapAutomaton.ordinary (automaton POL Q side)).Accepts w ↔
      Final (tables POL Q.constraints) side (stateAt POL Q w) := by
  rw [ForwardCapAutomaton.ordinary_accepts]
  constructor
  · rintro ⟨r, hr, hf⟩
    have := (compile_runs_iff _ POL side _ _ _ _ w).mp hr
    have hstart : (stateEquiv n).symm (automaton POL Q side).start = start Q.left Q.right := by
      simp [automaton, compile]
    rw [hstart] at this
    change Final _ side ((stateEquiv n).symm r) at hf
    rwa [this] at hf
  · intro h
    refine ⟨stateEquiv n (stateAt POL Q w), ?_, ?_⟩
    · apply (compile_runs_iff _ POL side _ _ _ _ w).mpr
      simp [automaton, compile, stateAt]
    · change Final _ side ((stateEquiv n).symm (stateEquiv n _))
      simpa only [Equiv.symm_apply_apply] using h

/-- P-edge acceptance of the compiled side automaton, unfolded to `stateAt`/`run`. -/
theorem capped_iff (Q : Query n d) (side : Side) (w : List (Fin d)) :
    ForwardCapAutomaton.Capped (automaton POL Q side) w ↔
      ∃ anchor tail root k, w = anchor ++ tail ∧
        Final (tables POL Q.constraints) side (stateAt POL Q anchor) ∧
        PEdge (tables POL Q.constraints) side
          (run (tables POL Q.constraints) POL (stateAt POL Q anchor) root) (stateAt POL Q anchor) ∧
        tail <+: Language.wordPower root k := by
  have hstart : (stateEquiv n).symm (automaton POL Q side).start = start Q.left Q.right := by
    simp [automaton, compile]
  constructor
  · rintro ⟨anchor, tail, q, src, root, k, he, ha, hf, hr, hp, ht⟩
    have ha' := (compile_runs_iff _ POL side _ _ _ _ anchor).mp ha
    rw [hstart] at ha'
    have hr' := (compile_runs_iff _ POL side _ _ _ _ root).mp hr
    change Final _ side ((stateEquiv n).symm q) at hf
    change PEdge _ side ((stateEquiv n).symm src) ((stateEquiv n).symm q) at hp
    rw [ha'] at hr' hf hp
    rw [hr'] at hp
    exact ⟨anchor, tail, root, k, he, hf, hp, ht⟩
  · rintro ⟨anchor, tail, root, k, he, hf, hp, ht⟩
    refine ⟨anchor, tail, stateEquiv n (stateAt POL Q anchor),
      stateEquiv n (run (tables POL Q.constraints) POL (stateAt POL Q anchor) root), root, k, he,
      ?_, ?_, ?_, ?_, ht⟩
    · apply (compile_runs_iff _ POL side _ _ _ _ anchor).mpr
      simp [automaton, compile, stateAt]
    · change Final _ side ((stateEquiv n).symm (stateEquiv n _))
      simpa only [Equiv.symm_apply_apply] using hf
    · apply (compile_runs_iff _ POL side _ _ _ _ root).mpr
      simp [automaton, compile]
    · change PEdge _ side ((stateEquiv n).symm (stateEquiv n _)) ((stateEquiv n).symm (stateEquiv n _))
      simpa only [Equiv.symm_apply_apply] using hp

/-- The meaning of `stateAt` in every solution over arbitrary contravariant trees: the
reached triple bounds the encoded subtrees of `x` and `y` at `w`, and its polarity bit is
`pathPol POL w` (v1362 §3 "meaning", v1364 §1 notation). -/
theorem stateAt_meaning (Q : Query n d) (ρ : Fin n → CTree POL)
    (hρ : Satisfies (treeConstructor POL) Q.constraints ρ) (w : List (Fin d)) {r : Triple n}
    (h : stateAt POL Q w = some r) :
    Bounds (fun x => E POL (ρ x)) r (project (E POL (ρ Q.left)) w) (project (E POL (ρ Q.right)) w) ∧
      r.2.2 = pathPol POL w :=
  meaning (encSound_of_satisfies Q.constraints ρ hρ) Q.left Q.right w h

/-- The S4 target, stated: rejection yields a countermodel on that side. Together with
`accepts_sound` it makes `decideEntails` a decision for arbitrary (and regular) trees. Not
proved here. -/
def Complete (POL : Polarity d) (Q : Query n d) (side : Side) : Prop :=
  ∀ w, QuerySafe POL Q side w → ForwardCapAutomaton.Accepts (automaton POL Q side) w

theorem accepts_iff_safe_of_complete (Q : Query n d) (side : Side) (hc : Complete POL Q side)
    (w : List (Fin d)) :
    ForwardCapAutomaton.Accepts (automaton POL Q side) w ↔ QuerySafe POL Q side w :=
  ⟨accepts_sound Q side w, hc w⟩

/-- With completeness of both sides (S4) and satisfiability (S2), `decideEntails` decides
arbitrary-tree entailment. -/
theorem decideEntails_correct_of_complete (Q : Query n d) (hl : Complete POL Q .left)
    (hr : Complete POL Q .right) :
    decideEntails POL Q = true ↔ Entails (treeConstructor POL) Q := by
  refine ⟨decideEntails_sound Q, fun h => ?_⟩
  simp only [decideEntails, Bool.or_eq_true, Bool.not_eq_true']
  apply Or.inr
  apply (decideBothSides_correct POL Q).mpr
  have hs := (entails_iff_all_safe Q).mp h
  exact ⟨fun w => hl w (hs .left w), fun w => hr w (hs .right w)⟩

end NSSE.ContraSoundness
