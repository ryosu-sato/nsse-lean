import NSSE.ContraGadget

/-! # Support of the terminal gadget: the class table and the explicit support (stage S4, part 2)

notes_v1364 §2 (Lemma A.0, Lemma A), §3 (Theorem B).

For a gadget `Θ` (`NSSE.ContraGadget`), positions `(r,k)` are out- or in-positions by
`pol(w[:k]) = r`. The PATH SET of a position is read off the deterministic set-token automaton of
S3 (`st k`, its state after `w[:k]`): `PSet r k z` holds iff some token `t` of rail `r` at `w[:k]`
has `t ≤s_φ z` (out-position) resp. `z ≤s_φ t` (in-position); when the automaton has already
escaped (`ALL`) the set is everything. These are v1364's `Out(p)`, `In(p)` for on-path
positions: `Path^U(x,q)` on the x-rail, `Path^L(y,q)` on the y-rail, closed under support in the
direction of the position (`pset_up`, `pset_down`), and paths compose (`pset_move_upper`,
`pset_move_lower`).

`Zip` is the zipper of v1364 §3 on on-path positions: base pairs (out-position, in-position)
with `z ≤s_φ z'` between their path sets, closed under the zipping rule along a common letter
(order swapped at a contravariant letter).

**Theorem B (inclusion)** `support_inv`: every support pair of `Θ` is in
```
Inv = Δ ∪ {(B_, b) | b ∉ L} ∪ {(a, T_) | a ∉ R} ∪ ≤s_φ ∪ RO ∪ tok(ZIP)
```
with `RO` the crossings `(tok p, z)`, `z ∈ PSet p` (out `p`) and `(z, tok p)`, `z ∈ PSet p`
(in `p`). The fill pairs are kept coarse (every pair `(B_, b)` with `b` not in class `L`, and
dually): this is all the completeness proof needs, and it is closed under the rules.

**Lemma A (class table)** `support_class`: a support pair of `Θ` between distinct tokens never has
its left token in class `R` or its right token in class `L`; and `support_orig`: old-to-old
support is original.
-/

namespace NSSE.ContraGadget

open SubtypeConstraints (Constraints Query BoundLiteral)
open AbsorbingSubtypeTrees
open ContraTrees ContraConstraints ContraSupport ContraClashes ContraAutomaton ContraSoundness
open ForwardTableAutomaton (Side)

variable {n d : Nat}

namespace Setup

variable (g : Setup n d)

/-! ## Path sets read from the automaton -/

abbrev D : Tables n d := tables g.POL g.φ

/-- The automaton state at the prefix `w[:k]`. -/
def st (k : Nat) : State n := run g.D g.POL (start g.x g.y) (g.w.take k)

/-- The tokens of rail `r` (`S_x` for `X`, `S_y` for `Y`). -/
def tokSet (r : Bool) (q : Triple n) : TokenSet n := if r then q.2.1 else q.1

/-- The path set of the position `(r,k)`, closed under support in its direction. -/
def PSet (r : Bool) (k : Nat) (z : Fin n) : Prop :=
  match g.st k with
  | none => True
  | some q => ∃ t, tokSet r q t = true ∧
      (if g.out r k = true then Support g.POL g.φ t z else Support g.POL g.φ z t)

theorem st_zero : g.st 0 = start g.x g.y := by simp [st]

theorem st_sigma {k : Nat} {q : Triple n} (h : g.st k = some q) : q.2.2 = g.sig k :=
  start_sigma g.D g.POL h

theorem st_succ {k : Nat} {i : Fin d} (h : g.w[k]? = some i) :
    g.st (k + 1) = delta g.D g.POL (g.st k) i := by
  simp only [st, List.take_succ, h, Option.toList_some, run_append, run_cons, run_nil]

theorem st_drop (k : Nat) : g.st g.N = run g.D g.POL (g.st k) (g.w.drop k) := by
  simp only [st, List.take_length]
  rw [← run_append, List.take_append_drop]

theorem pset_zero_x (z : Fin n) : g.PSet false 0 z ↔ Support g.POL g.φ g.x z := by
  simp only [PSet, g.st_zero, start, tokSet, out_zero, Bool.not_false, if_true]
  constructor
  · rintro ⟨t, ht, hs⟩; simp at ht; subst ht; simpa using hs
  · intro h; exact ⟨g.x, by simp, by simpa using h⟩

theorem pset_zero_y (z : Fin n) : g.PSet true 0 z ↔ Support g.POL g.φ z g.y := by
  simp only [PSet, g.st_zero, start, tokSet, out_zero, Bool.not_true, if_true]
  constructor
  · rintro ⟨t, ht, hs⟩; simp at ht; subst ht; simpa using hs
  · intro h; exact ⟨g.y, by simp, by simpa using h⟩

theorem pset_up {r : Bool} {k : Nat} (ho : g.out r k = true) {z z' : Fin n} (h : g.PSet r k z)
    (hs : Support g.POL g.φ z z') : g.PSet r k z' := by
  unfold PSet at h ⊢
  cases hst : g.st k with
  | none => trivial
  | some q =>
    rw [hst] at h
    obtain ⟨t, ht, h⟩ := h
    rw [if_pos ho] at h
    exact ⟨t, ht, by rw [if_pos ho]; exact h.trans hs⟩

theorem pset_down {r : Bool} {k : Nat} (ho : g.out r k = false) {z z' : Fin n}
    (hs : Support g.POL g.φ z' z) (h : g.PSet r k z) : g.PSet r k z' := by
  unfold PSet at h ⊢
  cases hst : g.st k with
  | none => trivial
  | some q =>
    rw [hst] at h
    obtain ⟨t, ht, h⟩ := h
    have hn : ¬ g.out r k = true := by simp [ho]
    rw [if_neg hn] at h
    exact ⟨t, ht, by rw [if_neg hn]; exact hs.trans h⟩

theorem tokSet_next (q : Triple n) (i : Fin d) (r : Bool) (z : Fin n) :
    tokSet r (next g.D g.POL q i) z = true ↔
      ∃ t, tokSet r q t = true ∧
        (if q.2.2 = r then g.D.upper t i z else g.D.lower t i z) = true := by
  cases r <;> cases hσ : q.2.2 <;> simp [tokSet, next, xMove, yMove, hσ]

/-- Paths compose: an out-position moves along an upper literal. -/
theorem pset_move_upper {r : Bool} {k : Nat} {i : Fin d} (ho : g.out r k = true)
    (hi : g.w[k]? = some i) {a : BoundLiteral n d} (ha : a ∈ g.φ.upper) (hp : g.PSet r k a.1) :
    g.PSet r (k + 1) (a.2 i) := by
  unfold PSet at hp ⊢
  rw [g.st_succ hi]
  cases hst : g.st k with
  | none => simp
  | some q =>
      rw [hst] at hp
      by_cases he : Escape g.D q
      · rw [delta_escape _ _ he]; trivial
      · rw [delta_proper _ _ he]
        refine ⟨a.2 i, ?_, by split_ifs <;> exact .refl _⟩
        obtain ⟨t, ht, hs⟩ := hp
        rw [if_pos ho] at hs
        have hσ : q.2.2 = r := by
          rw [g.st_sigma hst]; simpa [out] using ho
        refine (g.tokSet_next q i r _).mpr ⟨t, ht, ?_⟩
        rw [if_pos hσ, upper_correct]
        exact ⟨a, ha, hs, by unfold SupportAt; split_ifs <;> exact .refl _⟩

/-- Paths compose: an in-position moves along a lower literal. -/
theorem pset_move_lower {r : Bool} {k : Nat} {i : Fin d} (ho : g.out r k = false)
    (hi : g.w[k]? = some i) {a : BoundLiteral n d} (ha : a ∈ g.φ.lower) (hp : g.PSet r k a.1) :
    g.PSet r (k + 1) (a.2 i) := by
  unfold PSet at hp ⊢
  rw [g.st_succ hi]
  cases hst : g.st k with
  | none => simp
  | some q =>
      rw [hst] at hp
      by_cases he : Escape g.D q
      · rw [delta_escape _ _ he]; trivial
      · rw [delta_proper _ _ he]
        refine ⟨a.2 i, ?_, by split_ifs <;> exact .refl _⟩
        obtain ⟨t, ht, hs⟩ := hp
        rw [if_neg (by simp [ho])] at hs
        have hσ : q.2.2 ≠ r := by
          rw [g.st_sigma hst]; simpa [out] using ho
        refine (g.tokSet_next q i r _).mpr ⟨t, ht, ?_⟩
        rw [if_neg hσ, lower_correct]
        exact ⟨a, ha, by unfold SupportAt; split_ifs <;> exact .refl _, hs⟩

/-! ## The zipper -/

/-- The zipper of v1364 §3 on on-path positions; the first position is an out-position, the
second an in-position (`zip_wf`). -/
inductive Zip (g : Setup n d) : Bool → Nat → Bool → Nat → Prop
  | base {r1 k1 r2 k2 : _} (z z' : Fin n) (h1 : k1 ≤ g.N) (h2 : k2 ≤ g.N)
      (o1 : g.out r1 k1 = true) (o2 : g.out r2 k2 = false) (hz : g.PSet r1 k1 z)
      (hz' : g.PSet r2 k2 z') (hs : Support g.POL g.φ z z') : Zip g r1 k1 r2 k2
  | cov {r1 k1 r2 k2 : _} {i : Fin d} (h : Zip g r1 k1 r2 k2) (e1 : g.w[k1]? = some i)
      (e2 : g.w[k2]? = some i) (hi : g.POL i = false) : Zip g r1 (k1 + 1) r2 (k2 + 1)
  | con {r1 k1 r2 k2 : _} {i : Fin d} (h : Zip g r1 k1 r2 k2) (e1 : g.w[k1]? = some i)
      (e2 : g.w[k2]? = some i) (hi : g.POL i = true) : Zip g r2 (k2 + 1) r1 (k1 + 1)

theorem zip_wf {r1 k1 r2 k2} (h : g.Zip r1 k1 r2 k2) :
    k1 ≤ g.N ∧ k2 ≤ g.N ∧ g.out r1 k1 = true ∧ g.out r2 k2 = false := by
  induction h with
  | base z z' h1 h2 o1 o2 => exact ⟨h1, h2, o1, o2⟩
  | @cov r1 k1 r2 k2 i h e1 e2 hi ih =>
      refine ⟨g.lt_of_getElem? e1, g.lt_of_getElem? e2, ?_, ?_⟩
      · rw [g.out_succ e1, ih.2.2.1, hi]; rfl
      · rw [g.out_succ e2, ih.2.2.2, hi]; rfl
  | @con r1 k1 r2 k2 i h e1 e2 hi ih =>
      refine ⟨g.lt_of_getElem? e2, g.lt_of_getElem? e1, ?_, ?_⟩
      · rw [g.out_succ e2, ih.2.2.2, hi]; rfl
      · rw [g.out_succ e1, ih.2.2.1, hi]; rfl

theorem zip_base_of_zero {r1 k1 r2 k2} (h : g.Zip r1 k1 r2 k2) (h0 : k1 = 0 ∨ k2 = 0) :
    ∃ z z', g.PSet r1 k1 z ∧ g.PSet r2 k2 z' ∧ Support g.POL g.φ z z' := by
  cases h with
  | base z z' _ _ _ _ hz hz' hs => exact ⟨z, z', hz, hz', hs⟩
  | cov => omega
  | con => omega

/-! ## Classes (v1364 §1) -/

inductive Cls
  | O | L | R
  deriving DecidableEq

/-- `O` original, `L` fresh tokens with a lower literal (and `B_`), `R` fresh tokens with an
upper literal (and `T_`). -/
def cls : Tok n g.N → Cls
  | .orig _ => .O
  | .bt => .L
  | .tt => .R
  | .rail r k => if g.out r (k.1 + 1) then .L else .R

theorem cls_tokP {r : Bool} {k : Nat} (h0 : k ≠ 0) (hk : k ≤ g.N) :
    g.cls (g.tokP r k) = if g.out r k then .L else .R := by
  rw [g.tokP_pos h0 hk]
  simp only [cls, show k - 1 + 1 = k by omega]

theorem cls_tokP_out {r : Bool} {k : Nat} (hk : k ≤ g.N) (ho : g.out r k = true) :
    g.cls (g.tokP r k) ≠ .R := by
  by_cases h0 : k = 0
  · subst h0; simp [tokP_zero, cls]
  · rw [g.cls_tokP h0 hk, ho]; simp

theorem cls_tokP_in {r : Bool} {k : Nat} (hk : k ≤ g.N) (ho : g.out r k = false) :
    g.cls (g.tokP r k) ≠ .L := by
  by_cases h0 : k = 0
  · subst h0; simp [tokP_zero, cls]
  · rw [g.cls_tokP h0 hk, ho]; simp

/-- Lemma A.0 for a lower literal at an out-position. -/
theorem cls_children_lower {r : Bool} {k : Nat} (_hk : k ≤ g.N) (ho : g.out r k = true) (i : Fin d) :
    (g.POL i = false → g.cls (g.children r k i) ≠ .R) ∧
      (g.POL i = true → g.cls (g.children r k i) ≠ .L) := by
  by_cases hw : g.w[k]? = some i
  · rw [g.children_rail hw]
    have hk' := g.lt_of_getElem? hw
    have := g.out_succ hw r
    rw [ho] at this
    refine ⟨fun hp => g.cls_tokP_out (by omega) (by rw [this, hp]; rfl),
      fun hp => g.cls_tokP_in (by omega) (by rw [this, hp]; rfl)⟩
  · rw [g.children_fill hw, ho]
    constructor <;> intro hp <;> simp [fill, hp, cls]

/-- Lemma A.0 for an upper literal at an in-position. -/
theorem cls_children_upper {r : Bool} {k : Nat} (_hk : k ≤ g.N) (ho : g.out r k = false) (i : Fin d) :
    (g.POL i = false → g.cls (g.children r k i) ≠ .L) ∧
      (g.POL i = true → g.cls (g.children r k i) ≠ .R) := by
  by_cases hw : g.w[k]? = some i
  · rw [g.children_rail hw]
    have hk' := g.lt_of_getElem? hw
    have := g.out_succ hw r
    rw [ho] at this
    refine ⟨fun hp => g.cls_tokP_in (by omega) (by rw [this, hp]; rfl),
      fun hp => g.cls_tokP_out (by omega) (by rw [this, hp]; rfl)⟩
  · rw [g.children_fill hw, ho]
    constructor <;> intro hp <;> simp [fill, hp, cls]

/-! ## The explicit relation (Theorem B, right-hand side) -/

/-- `Δ ∪ fills ∪ ≤s_φ ∪ RO ∪ tok(ZIP)`. -/
def Inv (a b : Tok n g.N) : Prop :=
  a = b ∨
  (a = .bt ∧ g.cls b ≠ .L) ∨
  (b = .tt ∧ g.cls a ≠ .R) ∨
  (∃ u v, a = .orig u ∧ b = .orig v ∧ Support g.POL g.φ u v) ∨
  (∃ r k z, k ≤ g.N ∧ g.out r k = true ∧ a = g.tokP r k ∧ b = .orig z ∧ g.PSet r k z) ∨
  (∃ r k z, k ≤ g.N ∧ g.out r k = false ∧ b = g.tokP r k ∧ a = .orig z ∧ g.PSet r k z) ∨
  (∃ r1 k1 r2 k2, g.Zip r1 k1 r2 k2 ∧ a = g.tokP r1 k1 ∧ b = g.tokP r2 k2)

theorem inv_to_L {a c : Tok n g.N} (hc : g.cls c = .L) (h : g.Inv a c) : a = c := by
  rcases h with h | ⟨_, h⟩ | ⟨rfl, _⟩ | ⟨_, v, _, rfl, _⟩ | ⟨_, _, z, _, _, _, rfl, _⟩ |
    ⟨r, k, _, hk, ho, rfl, _, _⟩ | ⟨_, _, r2, k2, hz, _, rfl⟩
  · exact h
  · exact absurd hc h
  · simp [cls] at hc
  · simp [cls] at hc
  · simp [cls] at hc
  · exact absurd hc (g.cls_tokP_in hk ho)
  · have := g.zip_wf hz
    exact absurd hc (g.cls_tokP_in this.2.1 this.2.2.2)

theorem inv_from_R {c b : Tok n g.N} (hc : g.cls c = .R) (h : g.Inv c b) : b = c := by
  rcases h with h | ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨u, _, rfl, _, _⟩ | ⟨r, k, _, hk, ho, rfl, _, _⟩ |
    ⟨_, _, z, _, _, _, rfl, _⟩ | ⟨r1, k1, _, _, hz, rfl, _⟩
  · exact h.symm
  · simp [cls] at hc
  · exact absurd hc h
  · simp [cls] at hc
  · exact absurd hc (g.cls_tokP_out hk ho)
  · simp [cls] at hc
  · have := g.zip_wf hz
    exact absurd hc (g.cls_tokP_out this.1 this.2.2.1)

/-- Everything below an original token. -/
theorem inv_to_orig {a : Tok n g.N} {v : Fin n} : g.Inv a (.orig v) ↔
    a = .bt ∨ (∃ u, a = .orig u ∧ Support g.POL g.φ u v) ∨
      (∃ r k, k ≠ 0 ∧ k ≤ g.N ∧ g.out r k = true ∧ a = g.tokP r k ∧ g.PSet r k v) := by
  constructor
  · rintro (rfl | ⟨rfl, _⟩ | ⟨h, _⟩ | ⟨u, v', rfl, hv, hs⟩ | ⟨r, k, z, hk, ho, rfl, hz, hp⟩ |
      ⟨r, k, z, hk, ho, hv, rfl, hp⟩ | ⟨r1, k1, r2, k2, hz, rfl, hv⟩)
    · exact Or.inr (Or.inl ⟨v, rfl, .refl _⟩)
    · exact Or.inl rfl
    · exact Tok.noConfusion h
    · cases hv; exact Or.inr (Or.inl ⟨u, rfl, hs⟩)
    · cases hz
      by_cases h0 : k = 0
      · subst h0
        have hr : r = false := by simpa using ho
        subst hr
        refine Or.inr (Or.inl ⟨g.x, by simp [tokP_zero], (g.pset_zero_x v).mp hp⟩)
      · exact Or.inr (Or.inr ⟨r, k, h0, hk, ho, rfl, hp⟩)
    · obtain ⟨h0, hv'⟩ := g.tokP_eq_orig hk hv.symm
      subst h0
      have hr : r = true := by simpa using ho
      subst hr
      simp only [if_true] at hv'
      subst hv'
      exact Or.inr (Or.inl ⟨z, rfl, (g.pset_zero_y z).mp hp⟩)
    · have hwf := g.zip_wf hz
      obtain ⟨h0, hv'⟩ := g.tokP_eq_orig hwf.2.1 hv.symm
      subst h0
      have hr : r2 = true := by simpa using hwf.2.2.2
      subst hr
      simp only [if_true] at hv'
      subst hv'
      obtain ⟨z, z', hz1, hz2, hs⟩ := g.zip_base_of_zero hz (Or.inr rfl)
      have hzy := (g.pset_zero_y z').mp hz2
      by_cases h0 : k1 = 0
      · subst h0
        have hr : r1 = false := by simpa using hwf.2.2.1
        subst hr
        exact Or.inr (Or.inl ⟨g.x, by simp [tokP_zero],
          (((g.pset_zero_x z).mp hz1).trans hs).trans hzy⟩)
      · exact Or.inr (Or.inr ⟨r1, k1, h0, hwf.1, hwf.2.2.1, rfl,
          g.pset_up hwf.2.2.1 hz1 (hs.trans hzy)⟩)
  · rintro (rfl | ⟨u, rfl, hs⟩ | ⟨r, k, _, hk, ho, rfl, hp⟩)
    · exact Or.inr (Or.inl ⟨rfl, by simp [cls]⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨u, v, rfl, rfl, hs⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, v, hk, ho, rfl, rfl, hp⟩))))

/-- Everything above an original token. -/
theorem inv_from_orig {b : Tok n g.N} {v : Fin n} : g.Inv (.orig v) b ↔
    b = .tt ∨ (∃ u, b = .orig u ∧ Support g.POL g.φ v u) ∨
      (∃ r k, k ≠ 0 ∧ k ≤ g.N ∧ g.out r k = false ∧ b = g.tokP r k ∧ g.PSet r k v) := by
  constructor
  · rintro (rfl | ⟨h, _⟩ | ⟨rfl, _⟩ | ⟨v', u, hv, rfl, hs⟩ | ⟨r, k, z, hk, ho, hv, rfl, hp⟩ |
      ⟨r, k, z, hk, ho, rfl, hz, hp⟩ | ⟨r1, k1, r2, k2, hz, hv, rfl⟩)
    · exact Or.inr (Or.inl ⟨v, rfl, .refl _⟩)
    · exact Tok.noConfusion h
    · exact Or.inl rfl
    · cases hv; exact Or.inr (Or.inl ⟨u, rfl, hs⟩)
    · obtain ⟨h0, hv'⟩ := g.tokP_eq_orig hk hv.symm
      subst h0
      have hr : r = false := by simpa using ho
      subst hr
      simp only [Bool.false_eq_true, if_false] at hv'
      subst hv'
      exact Or.inr (Or.inl ⟨z, rfl, (g.pset_zero_x z).mp hp⟩)
    · cases hz
      by_cases h0 : k = 0
      · subst h0
        have hr : r = true := by simpa using ho
        subst hr
        refine Or.inr (Or.inl ⟨g.y, by simp [tokP_zero], (g.pset_zero_y v).mp hp⟩)
      · exact Or.inr (Or.inr ⟨r, k, h0, hk, ho, rfl, hp⟩)
    · have hwf := g.zip_wf hz
      obtain ⟨h0, hv'⟩ := g.tokP_eq_orig hwf.1 hv.symm
      subst h0
      have hr : r1 = false := by simpa using hwf.2.2.1
      subst hr
      simp only [Bool.false_eq_true, if_false] at hv'
      subst hv'
      obtain ⟨z, z', hz1, hz2, hs⟩ := g.zip_base_of_zero hz (Or.inl rfl)
      have hxz := (g.pset_zero_x z).mp hz1
      by_cases h0 : k2 = 0
      · subst h0
        have hr : r2 = true := by simpa using hwf.2.2.2
        subst hr
        exact Or.inr (Or.inl ⟨g.y, by simp [tokP_zero],
          (hxz.trans hs).trans ((g.pset_zero_y z').mp hz2)⟩)
      · exact Or.inr (Or.inr ⟨r2, k2, h0, hwf.2.1, hwf.2.2.2, rfl,
          g.pset_down hwf.2.2.2 (hxz.trans hs) hz2⟩)
  · rintro (rfl | ⟨u, rfl, hs⟩ | ⟨r, k, _, hk, ho, rfl, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by simp [cls]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, u, rfl, rfl, hs⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, v, hk, ho, rfl, rfl, hp⟩)))))

/-- Transitivity (the `L? O* R?` shape of Corollary A.1). -/
theorem inv_trans {a b c : Tok n g.N} (h1 : g.Inv a c) (h2 : g.Inv c b) : g.Inv a b := by
  rcases c with v | _ | _ | ⟨r, k⟩
  · rcases g.inv_to_orig.mp h1 with rfl | ⟨u, rfl, hu⟩ | ⟨r1, k1, h01, hk1, ho1, rfl, hp1⟩ <;>
    rcases g.inv_from_orig.mp h2 with rfl | ⟨u', rfl, hu'⟩ | ⟨r2, k2, h02, hk2, ho2, rfl, hp2⟩
    · exact Or.inr (Or.inl ⟨rfl, by simp [cls]⟩)
    · exact Or.inr (Or.inl ⟨rfl, by simp [cls]⟩)
    · exact Or.inr (Or.inl ⟨rfl, g.cls_tokP_in hk2 ho2⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, by simp [cls]⟩))
    · exact g.inv_to_orig.mpr (Or.inr (Or.inl ⟨u, rfl, hu.trans hu'⟩))
    · exact g.inv_from_orig.mpr (Or.inr (Or.inr ⟨r2, k2, h02, hk2, ho2, rfl, g.pset_down ho2 hu hp2⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, g.cls_tokP_out hk1 ho1⟩))
    · exact g.inv_to_orig.mpr (Or.inr (Or.inr ⟨r1, k1, h01, hk1, ho1, rfl, g.pset_up ho1 hp1 hu'⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨r1, k1, r2, k2, .base v v hk1 hk2 ho1 ho2 hp1 hp2 (.refl _), rfl, rfl⟩)))))
  · have := g.inv_to_L (by simp [cls]) h1; subst this; exact h2
  · have := g.inv_from_R (by simp [cls]) h2; subst this; exact h1
  · by_cases hc : g.cls (.rail r k) = .L
    · have := g.inv_to_L hc h1; subst this; exact h2
    · have hc' : g.cls (.rail r k) = .R := by
        simp only [cls] at hc ⊢; split_ifs at hc ⊢ <;> simp_all
      have := g.inv_from_R hc' h2; subst this; exact h1

/-! ### Views on positions -/

theorem inv_orig_orig {u v : Fin n} (h : g.Inv (.orig u) (.orig v)) : Support g.POL g.φ u v := by
  rcases g.inv_to_orig.mp h with h | ⟨u', hu, hs⟩ | ⟨r, k, h0, hk, _, he, _⟩
  · exact Tok.noConfusion h
  · cases hu; exact hs
  · exact absurd (g.tokP_eq_orig hk he.symm).1 h0

theorem inv_pos_orig {r : Bool} {k : Nat} {v : Fin n} (hk : k ≤ g.N) (ho : g.out r k = true)
    (h : g.Inv (g.tokP r k) (.orig v)) : g.PSet r k v := by
  by_cases h0 : k = 0
  · subst h0
    have hr : r = false := by simpa using ho
    subst hr
    rw [tokP_zero] at h
    exact (g.pset_zero_x v).mpr (g.inv_orig_orig (by simpa using h))
  · rcases g.inv_to_orig.mp h with h | ⟨u, hu, _⟩ | ⟨r', k', h0', hk', _, he, hp⟩
    · exact absurd h (g.tokP_ne_bt hk)
    · exact absurd (g.tokP_eq_orig hk hu).1 h0
    · obtain ⟨rfl, rfl⟩ := g.tokP_inj h0 hk hk' he
      exact hp

theorem inv_orig_pos {r : Bool} {k : Nat} {u : Fin n} (hk : k ≤ g.N) (ho : g.out r k = false)
    (h : g.Inv (.orig u) (g.tokP r k)) : g.PSet r k u := by
  by_cases h0 : k = 0
  · subst h0
    have hr : r = true := by simpa using ho
    subst hr
    rw [tokP_zero] at h
    exact (g.pset_zero_y u).mpr (g.inv_orig_orig (by simpa using h))
  · rcases g.inv_from_orig.mp h with h | ⟨v, hv, _⟩ | ⟨r', k', h0', hk', _, he, hp⟩
    · exact absurd h (g.tokP_ne_tt hk)
    · exact absurd (g.tokP_eq_orig hk hv).1 h0
    · obtain ⟨rfl, rfl⟩ := g.tokP_inj h0 hk hk' he
      exact hp

theorem inv_pos_pos {r1 r2 : Bool} {k1 k2 : Nat} (hk1 : k1 ≤ g.N) (hk2 : k2 ≤ g.N)
    (o1 : g.out r1 k1 = true) (o2 : g.out r2 k2 = false)
    (h : g.Inv (g.tokP r1 k1) (g.tokP r2 k2)) : g.Zip r1 k1 r2 k2 := by
  by_cases h01 : k1 = 0
  · subst h01
    have hr : r1 = false := by simpa using o1
    subst hr
    have hx : g.tokP false 0 = .orig g.x := by simp [tokP_zero]
    rw [hx] at h
    by_cases h02 : k2 = 0
    · subst h02
      have hr : r2 = true := by simpa using o2
      subst hr
      have hy : g.tokP true 0 = .orig g.y := by simp [tokP_zero]
      rw [hy] at h
      exact .base g.x g.y hk1 hk2 o1 o2 ((g.pset_zero_x _).mpr (.refl _))
        ((g.pset_zero_y _).mpr (.refl _)) (g.inv_orig_orig h)
    · exact .base g.x g.x hk1 hk2 o1 o2 ((g.pset_zero_x _).mpr (.refl _))
        (g.inv_orig_pos hk2 o2 h) (.refl _)
  · by_cases h02 : k2 = 0
    · subst h02
      have hr : r2 = true := by simpa using o2
      subst hr
      have hy : g.tokP true 0 = .orig g.y := by simp [tokP_zero]
      rw [hy] at h
      exact .base g.y g.y hk1 hk2 o1 o2 (g.inv_pos_orig hk1 o1 h)
        ((g.pset_zero_y _).mpr (.refl _)) (.refl _)
    · rcases h with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨u, _, h, _⟩ | ⟨_, _, z, _, _, _, h, _⟩ |
        ⟨_, _, z, _, _, _, h, _⟩ | ⟨r1', k1', r2', k2', hz, he1, he2⟩
      · obtain ⟨rfl, rfl⟩ := g.tokP_inj h01 hk1 hk2 h
        rw [o1] at o2; exact Bool.noConfusion o2
      · exact absurd h (g.tokP_ne_bt hk1)
      · exact absurd h (g.tokP_ne_tt hk2)
      · exact absurd (g.tokP_eq_orig hk1 h).1 h01
      · exact absurd (g.tokP_eq_orig hk2 h).1 h02
      · exact absurd (g.tokP_eq_orig hk1 h).1 h01
      · have hwf := g.zip_wf hz
        obtain ⟨rfl, rfl⟩ := g.tokP_inj h01 hk1 hwf.1 he1
        obtain ⟨rfl, rfl⟩ := g.tokP_inj h02 hk2 hwf.2.1 he2
        exact hz

/-! ### Closure under decomposition -/

theorem inv_bt {b : Tok n g.N} (h : g.cls b ≠ .L) : g.Inv .bt b := Or.inr (Or.inl ⟨rfl, h⟩)
theorem inv_tt {a : Tok n g.N} (h : g.cls a ≠ .R) : g.Inv a .tt := Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))

theorem inv_out {r : Bool} {k : Nat} {z : Fin n} (hk : k ≤ g.N) (ho : g.out r k = true)
    (hp : g.PSet r k z) : g.Inv (g.tokP r k) (.orig z) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, z, hk, ho, rfl, rfl, hp⟩))))

theorem inv_in {r : Bool} {k : Nat} {z : Fin n} (hk : k ≤ g.N) (ho : g.out r k = false)
    (hp : g.PSet r k z) : g.Inv (.orig z) (g.tokP r k) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, k, z, hk, ho, rfl, rfl, hp⟩)))))

theorem inv_zip {r1 k1 r2 k2} (h : g.Zip r1 k1 r2 k2) : g.Inv (g.tokP r1 k1) (g.tokP r2 k2) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r1, k1, r2, k2, h, rfl, rfl⟩)))))

theorem inv_orig {u v : Fin n} (h : Support g.POL g.φ u v) : g.Inv (.orig u) (.orig v) :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨u, v, rfl, rfl, h⟩)))

/-- The child relation of a decomposition step at position `i`. -/
def InvAt (i : Fin d) (a b : Tok n g.N) : Prop :=
  (g.POL i = false → g.Inv a b) ∧ (g.POL i = true → g.Inv b a)

/-- A rail lower literal at an out-position against an original upper literal. -/
theorem decomp_rail_orig {r : Bool} {k : Nat} (_hk : k ≤ g.N) (ho : g.out r k = true)
    {b : BoundLiteral n d} (hb : b ∈ g.φ.upper) (hp : g.PSet r k b.1) (i : Fin d) :
    g.InvAt i (g.children r k i) (.orig (b.2 i)) := by
  by_cases hw : g.w[k]? = some i
  · rw [g.children_rail hw]
    have hk' := g.lt_of_getElem? hw
    have hp' := g.pset_move_upper ho hw hb hp
    have hs := g.out_succ hw r
    rw [ho] at hs
    constructor
    · intro hi; exact g.inv_out (by omega) (by rw [hs, hi]; rfl) hp'
    · intro hi; exact g.inv_in (by omega) (by rw [hs, hi]; rfl) hp'
  · rw [g.children_fill hw, ho]
    constructor
    · intro hi; simp only [fill, hi, if_true]; exact g.inv_bt (by simp [cls])
    · intro hi; simp only [fill, hi, if_true]; exact g.inv_tt (by simp [cls])

/-- An original lower literal against a rail upper literal at an in-position. -/
theorem decomp_orig_rail {r : Bool} {k : Nat} (_hk : k ≤ g.N) (ho : g.out r k = false)
    {a : BoundLiteral n d} (ha : a ∈ g.φ.lower) (hp : g.PSet r k a.1) (i : Fin d) :
    g.InvAt i (.orig (a.2 i)) (g.children r k i) := by
  by_cases hw : g.w[k]? = some i
  · rw [g.children_rail hw]
    have hk' := g.lt_of_getElem? hw
    have hp' := g.pset_move_lower ho hw ha hp
    have hs := g.out_succ hw r
    rw [ho] at hs
    constructor
    · intro hi; exact g.inv_in (by omega) (by rw [hs, hi]; rfl) hp'
    · intro hi; exact g.inv_out (by omega) (by rw [hs, hi]; rfl) hp'
  · rw [g.children_fill hw, ho]
    constructor
    · intro hi; simp only [fill, hi, Bool.false_eq_true, if_false]; exact g.inv_tt (by simp [cls])
    · intro hi; simp only [fill, hi, if_true, Bool.false_eq_true, if_false]
      exact g.inv_bt (by simp [cls])

/-- Two rail literals: zipping, or a fill. -/
theorem decomp_rail_rail {r1 r2 : Bool} {k1 k2 : Nat} (hk1 : k1 ≤ g.N) (hk2 : k2 ≤ g.N)
    (o1 : g.out r1 k1 = true) (o2 : g.out r2 k2 = false) (hz : g.Zip r1 k1 r2 k2) (i : Fin d) :
    g.InvAt i (g.children r1 k1 i) (g.children r2 k2 i) := by
  have cl := g.cls_children_lower hk1 o1 i
  have cu := g.cls_children_upper hk2 o2 i
  by_cases h1 : g.w[k1]? = some i
  · by_cases h2 : g.w[k2]? = some i
    · rw [g.children_rail h1, g.children_rail h2]
      constructor
      · intro hi; exact g.inv_zip (.cov hz h1 h2 hi)
      · intro hi; exact g.inv_zip (.con hz h1 h2 hi)
    · have hf : g.children r2 k2 i = g.fill false i := by rw [g.children_fill h2, o2]
      constructor
      · intro hi
        rw [hf]; simp only [fill, hi, Bool.false_eq_true, if_false]
        exact g.inv_tt (cl.1 hi)
      · intro hi
        rw [hf]; simp only [fill, hi, if_true, Bool.false_eq_true, if_false]
        exact g.inv_bt (cl.2 hi)
  · have hf : g.children r1 k1 i = g.fill true i := by rw [g.children_fill h1, o1]
    constructor
    · intro hi
      rw [hf]; simp only [fill, hi, if_true, Bool.false_eq_true, if_false]
      exact g.inv_bt (cu.1 hi)
    · intro hi
      rw [hf]; simp only [fill, hi, if_true]
      exact g.inv_tt (cu.2 hi)

/-- **Closure of `Inv` under polarity decomposition** (the decomposition half of Theorem B). -/
theorem inv_decomp {l u : Tok n g.N × (Fin d → Tok n g.N)} (hl : l ∈ g.tokLower)
    (hu : u ∈ g.tokUpper) (h : g.Inv l.1 u.1) (i : Fin d) : g.InvAt i (l.2 i) (u.2 i) := by
  rcases (g.mem_tokLower l).mp hl with ⟨a, ha, rfl⟩ | ⟨r1, k1, hk1, o1, _, rfl⟩ <;>
  rcases (g.mem_tokUpper u).mp hu with ⟨b, hb, rfl⟩ | ⟨r2, k2, hk2, o2, _, rfl⟩
  · have hs := g.inv_orig_orig h
    have hd := Support.decomp ha hb hs i
    unfold SupportAt at hd
    constructor
    · intro hi; rw [if_neg (by simp [hi])] at hd; exact g.inv_orig hd
    · intro hi; rw [if_pos hi] at hd; exact g.inv_orig hd
  · exact g.decomp_orig_rail hk2 o2 ha (g.inv_orig_pos hk2 o2 h) i
  · exact g.decomp_rail_orig hk1 o1 hb (g.inv_pos_orig hk1 o1 h) i
  · exact g.decomp_rail_rail hk1 hk2 o1 o2 (g.inv_pos_pos hk1 hk2 o1 o2 h) i

/-! ## Theorem B (inclusion) and Lemma A -/

/-- **Theorem B** (`≤s_Θ ⊆ R`): every support pair of the gadget lies in the explicit relation. -/
theorem support_inv {a b : Fin (size n g.N)} (h : Support g.POL g.theta a b) :
    g.Inv (dec a) (dec b) := by
  induction h with
  | refl a => exact Or.inl rfl
  | trans _ _ ih₁ ih₂ => exact g.inv_trans ih₁ ih₂
  | @decompCov a b ha hb _ i hi ih =>
      obtain ⟨l, hl, rfl⟩ := g.mem_theta_lower.mp ha
      obtain ⟨u, hu, rfl⟩ := g.mem_theta_upper.mp hb
      simp only [encLit, dec_enc] at ih ⊢
      exact (g.inv_decomp hl hu ih i).1 hi
  | @decompCon a b ha hb _ i hi ih =>
      obtain ⟨l, hl, rfl⟩ := g.mem_theta_lower.mp ha
      obtain ⟨u, hu, rfl⟩ := g.mem_theta_upper.mp hb
      simp only [encLit, dec_enc] at ih ⊢
      exact (g.inv_decomp hl hu ih i).2 hi

theorem support_inv_enc {a b : Tok n g.N} (h : Support g.POL g.theta (enc a) (enc b)) :
    g.Inv a b := by
  simpa using g.support_inv h

theorem inv_class {a b : Tok n g.N} (h : g.Inv a b) (hne : a ≠ b) :
    g.cls a ≠ .R ∧ g.cls b ≠ .L := by
  rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨u, v, rfl, rfl, _⟩ | ⟨r, k, z, hk, ho, rfl, rfl, _⟩ |
    ⟨r, k, z, hk, ho, rfl, rfl, _⟩ | ⟨r1, k1, r2, k2, hz, rfl, rfl⟩
  · exact absurd h hne
  · exact ⟨by simp [cls], h⟩
  · exact ⟨h, by simp [cls]⟩
  · exact ⟨by simp [cls], by simp [cls]⟩
  · exact ⟨g.cls_tokP_out hk ho, by simp [cls]⟩
  · exact ⟨by simp [cls], g.cls_tokP_in hk ho⟩
  · have := g.zip_wf hz
    exact ⟨g.cls_tokP_out this.1 this.2.2.1, g.cls_tokP_in this.2.1 this.2.2.2⟩

/-- **Lemma A (class table)**: `O → L`, `R → O`, `L → L`, `R → R` are impossible except by
reflexivity; the possible classes of a support pair of distinct tokens are `(O,O), (O,R),
(L,O), (L,R)`. -/
theorem support_class {a b : Fin (size n g.N)} (h : Support g.POL g.theta a b) (hne : a ≠ b) :
    g.cls (dec a) ≠ .R ∧ g.cls (dec b) ≠ .L := by
  exact g.inv_class (g.support_inv h) (fun he => hne (dec_injective he))

/-- **Lemma A, old-to-old part**: support of `Θ` between original variables is original. -/
theorem support_orig {u v : Fin n}
    (h : Support g.POL g.theta (enc (Tok.orig u : Tok n g.N)) (enc (Tok.orig v))) :
    Support g.POL g.φ u v :=
  g.inv_orig_orig (g.support_inv_enc h)

/-- Conservativity: `≤s_Θ` restricted to the original variables is exactly `≤s_φ`. -/
theorem support_orig_iff (u v : Fin n) :
    Support g.POL g.theta (enc (Tok.orig u : Tok n g.N)) (enc (Tok.orig v)) ↔
      Support g.POL g.φ u v :=
  ⟨g.support_orig, g.support_lift⟩

end Setup

end NSSE.ContraGadget
