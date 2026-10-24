import NSSE.ContraCompleteness
import NSSE.ContraFiniteSatisfiability

/-! # Lemma F2: the terminal gadget does not change the signed C4 test (stage S6, part 2)

notes_v1366 §3. For every `(φ, w, side)` the signed pair graph `G_Θ` of the terminal gadget has a
cycle iff `G_φ` has one (`signedC4_theta_iff`).

(⇐) `φ ⊆ Θ` and `≤s_φ ⊆ ≤s_Θ` (`Setup.support_lift`).

(⇒) Vertices of `G_Θ` are classified by their decoded tokens: FILL vertices (a component is
`B_` or `T_`), FRESH vertices (no fill, some rail token) and OLD vertices (both original). The
proof is v1366's three claims, read through the explicit support of v1364 Theorem B
(`support_inv`):

* Claim 1 (`fill_no_step`): a fill vertex has no outgoing edge;
* Claim 2 (`fresh_step`): an edge out of a fresh vertex leads to a fill vertex or to a fresh vertex
  of strictly larger level `μ` (the larger rail level of the two components) — the edge must use
  the rail literal of a component of maximal level;
* Claim 3 (`old_step`): an edge out of an old vertex either uses two original literals, is then an
  edge of `G_φ` (old-to-old support is original), or leads to a fill or fresh vertex.

Hence a cycle of `G_Θ` never visits a fresh or fill vertex, and is a cycle of `G_φ`.
-/

namespace NSSE.ContraGadget

open SubtypeConstraints (Constraints Query BoundLiteral)
open ContraTrees ContraConstraints ContraSupport ContraClashes ContraSatisfiability
open ContraFiniteCycles

variable {n d : Nat}

/-- Token kinds. -/
def isFill {N : Nat} : Tok n N → Bool
  | .bt => true
  | .tt => true
  | _ => false

def isRail {N : Nat} : Tok n N → Bool
  | .rail _ _ => true
  | _ => false

/-- The rail level of a token (`0` for non-rail tokens). -/
def lvl {N : Nat} : Tok n N → Nat
  | .rail _ k => k.1 + 1
  | _ => 0

theorem tok_kinds {N : Nat} (t : Tok n N) : isFill t = true ∨ isRail t = true ∨ ∃ v, t = .orig v := by
  rcases t with v | _ | _ | ⟨r, k⟩ <;> simp [isFill, isRail]

theorem lvl_pos_rail {N : Nat} {t : Tok n N} (h : 0 < lvl t) : isRail t = true := by
  rcases t with v | _ | _ | ⟨r, k⟩ <;> simp_all [lvl, isRail]

namespace Setup

variable (g : Setup n d)

theorem lvl_tokP {r : Bool} {k : Nat} (hk : k ≤ g.N) : lvl (g.tokP r k) = k := by
  by_cases h0 : k = 0
  · subst h0; simp [tokP_zero, lvl]
  · rw [g.tokP_pos h0 hk]; simp [lvl]; omega

theorem cls_rail (r : Bool) (k : Fin g.N) : g.cls (.rail r k) = .L ∨ g.cls (.rail r k) = .R := by
  simp only [cls]; split_ifs <;> simp

/-- The children of a rail literal are fills or rail tokens one level deeper. -/
theorem children_kind {r : Bool} {k : Nat} (i : Fin d) :
    isFill (g.children r k i) = true ∨
      (isRail (g.children r k i) = true ∧ k < lvl (g.children r k i)) := by
  by_cases hw : g.w[k]? = some i
  · rw [g.children_rail hw]
    have hk := g.lt_of_getElem? hw
    right
    rw [g.tokP_pos (by omega) (by omega)]
    simp [isRail, lvl]
  · rw [g.children_fill hw]
    left
    cases g.out r k <;> cases hp : g.POL i <;> simp [fill, isFill, hp]

/-- A lower literal of `Θ` is original, or a rail literal whose children are fills or deeper
rail tokens. -/
theorem lower_cases {l : Tok n g.N × (Fin d → Tok n g.N)} (hl : l ∈ g.tokLower) :
    (∃ a ∈ g.φ.lower, l = origLit a) ∨
      ∀ i, isFill (l.2 i) = true ∨ (isRail (l.2 i) = true ∧ lvl l.1 < lvl (l.2 i)) := by
  rcases (g.mem_tokLower l).mp hl with h | ⟨r, k, hk, _, _, rfl⟩
  · exact Or.inl h
  · right; intro i
    simp only [g.lvl_tokP hk]
    exact g.children_kind i

theorem upper_cases {l : Tok n g.N × (Fin d → Tok n g.N)} (hl : l ∈ g.tokUpper) :
    (∃ a ∈ g.φ.upper, l = origLit a) ∨
      ∀ i, isFill (l.2 i) = true ∨ (isRail (l.2 i) = true ∧ lvl l.1 < lvl (l.2 i)) := by
  rcases (g.mem_tokUpper l).mp hl with h | ⟨r, k, hk, _, _, rfl⟩
  · exact Or.inl h
  · right; intro i
    simp only [g.lvl_tokP hk]
    exact g.children_kind i

theorem lower_parent_not_fill {l : Tok n g.N × (Fin d → Tok n g.N)} (hl : l ∈ g.tokLower) :
    isFill l.1 = false := by
  rcases (g.mem_tokLower l).mp hl with ⟨a, _, rfl⟩ | ⟨r, k, hk, _, _, rfl⟩
  · rfl
  · by_cases h0 : k = 0
    · subst h0; simp [tokP_zero, isFill]
    · simp only; rw [g.tokP_pos h0 hk]; rfl

theorem upper_parent_not_fill {l : Tok n g.N × (Fin d → Tok n g.N)} (hl : l ∈ g.tokUpper) :
    isFill l.1 = false := by
  rcases (g.mem_tokUpper l).mp hl with ⟨a, _, rfl⟩ | ⟨r, k, hk, _, _, rfl⟩
  · rfl
  · by_cases h0 : k = 0
    · subst h0; simp [tokP_zero, isFill]
    · simp only; rw [g.tokP_pos h0 hk]; rfl

theorem lower_rail_parent {l : Tok n g.N × (Fin d → Tok n g.N)} (hl : l ∈ g.tokLower)
    (hr : isRail l.1 = true) (i : Fin d) :
    isFill (l.2 i) = true ∨ (isRail (l.2 i) = true ∧ lvl l.1 < lvl (l.2 i)) := by
  rcases g.lower_cases hl with ⟨a, _, rfl⟩ | h
  · simp [origLit, isRail] at hr
  · exact h i

theorem upper_rail_parent {l : Tok n g.N × (Fin d → Tok n g.N)} (hl : l ∈ g.tokUpper)
    (hr : isRail l.1 = true) (i : Fin d) :
    isFill (l.2 i) = true ∨ (isRail (l.2 i) = true ∧ lvl l.1 < lvl (l.2 i)) := by
  rcases g.upper_cases hl with ⟨a, _, rfl⟩ | h
  · simp [origLit, isRail] at hr
  · exact h i

/-! ## Vertex classes -/

/-- A fill vertex. -/
def VFill (p : Vertex (size n g.N)) : Prop := isFill (dec p.1) = true ∨ isFill (dec p.2) = true

/-- A fresh vertex. -/
def VFresh (p : Vertex (size n g.N)) : Prop :=
  ¬ g.VFill p ∧ (isRail (dec p.1) = true ∨ isRail (dec p.2) = true)

/-- The level of a vertex. -/
def mu (p : Vertex (size n g.N)) : Nat := max (lvl (dec p.1)) (lvl (dec p.2))

/-- The unpacked form of an edge of `G_Θ`. -/
theorem step_unpack {p q : Vertex (size n g.N)} (h : PairStep g.POL g.theta p q) :
    ∃ i, ∃ lt ∈ g.tokLower, ∃ ut ∈ g.tokUpper,
      g.Inv (dec p.1) (dec p.2) ∧ g.Inv lt.1 (dec p.1) ∧ g.Inv (dec p.2) ut.1 ∧
      q = if g.POL i = true then (enc (ut.2 i), enc (lt.2 i)) else (enc (lt.2 i), enc (ut.2 i)) := by
  obtain ⟨hs, i, la, hla, ub, hub, h1, h2, hq⟩ := h
  obtain ⟨lt, hlt, rfl⟩ := g.mem_theta_lower.mp hla
  obtain ⟨ut, hut, rfl⟩ := g.mem_theta_upper.mp hub
  refine ⟨i, lt, hlt, ut, hut, g.support_inv hs, ?_, ?_, hq⟩
  · simpa [encLit] using g.support_inv h1
  · simpa [encLit] using g.support_inv h2

theorem dec_q {q : Vertex (size n g.N)} {i : Fin d} {c1 c2 : Tok n g.N}
    (hq : q = if g.POL i = true then (enc c2, enc c1) else (enc c1, enc c2)) :
    (dec q.1 = c1 ∧ dec q.2 = c2) ∨ (dec q.1 = c2 ∧ dec q.2 = c1) := by
  split_ifs at hq <;> subst hq <;> simp

/-- A vertex with a fill or rail component is a fill or fresh vertex. -/
theorem fill_or_fresh {q : Vertex (size n g.N)} {c : Tok n g.N}
    (hc : dec q.1 = c ∨ dec q.2 = c) (hk : isFill c = true ∨ isRail c = true) :
    g.VFill q ∨ g.VFresh q := by
  by_cases hf : g.VFill q
  · exact Or.inl hf
  · right
    refine ⟨hf, ?_⟩
    rcases hk with hk | hk
    · exact absurd (by rcases hc with hc | hc <;> rw [← hc] at hk <;> simp [VFill, hk]) hf
    · rcases hc with hc | hc <;> rw [← hc] at hk <;> simp [hk]

/-- **Claim 1**: a fill vertex has no outgoing edge. -/
theorem fill_no_step {p q : Vertex (size n g.N)} (hp : g.VFill p) : ¬ PairStep g.POL g.theta p q := by
  intro h
  obtain ⟨i, lt, hlt, ut, hut, hab, hla, hbu, _⟩ := g.step_unpack h
  have nl := g.lower_parent_not_fill hlt
  have nu := g.upper_parent_not_fill hut
  rcases hp with hp | hp
  · have : dec p.1 = .bt ∨ dec p.1 = .tt := by
      cases hx : dec p.1 <;> simp_all [isFill]
    rcases this with ha | ha
    · rw [ha] at hla; rw [g.inv_bt_right hla] at nl; simp [isFill] at nl
    · rw [ha] at hab; have hb := g.inv_tt_left hab
      rw [hb] at hbu; rw [g.inv_tt_left hbu] at nu; simp [isFill] at nu
  · have : dec p.2 = .bt ∨ dec p.2 = .tt := by
      cases hx : dec p.2 <;> simp_all [isFill]
    rcases this with hb | hb
    · rw [hb] at hab; have ha := g.inv_bt_right hab
      rw [ha] at hla; rw [g.inv_bt_right hla] at nl; simp [isFill] at nl
    · rw [hb] at hbu; rw [g.inv_tt_left hbu] at nu; simp [isFill] at nu

/-- The component of maximal level of a fresh vertex has its own rail literal used. -/
theorem fresh_advance {p q : Vertex (size n g.N)} (hp : g.VFresh p)
    (h : PairStep g.POL g.theta p q) :
    ∃ c, (dec q.1 = c ∨ dec q.2 = c) ∧ (isFill c = true ∨ (isRail c = true ∧ g.mu p < lvl c)) := by
  obtain ⟨i, lt, hlt, ut, hut, hab, hla, hbu, hq⟩ := g.step_unpack h
  have hq' := g.dec_q hq
  have h1 : dec q.1 = lt.2 i ∨ dec q.2 = lt.2 i := by
    rcases hq' with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have h2 : dec q.1 = ut.2 i ∨ dec q.2 = ut.2 i := by
    rcases hq' with ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inr h
    · exact Or.inl h
  -- using the lower literal of the component `a`
  have useL : lt.1 = dec p.1 → isRail (dec p.1) = true → lvl (dec p.2) ≤ lvl (dec p.1) →
      ∃ c, (dec q.1 = c ∨ dec q.2 = c) ∧ (isFill c = true ∨ (isRail c = true ∧ g.mu p < lvl c)) := by
    intro he hr hle
    rw [← he] at hr
    refine ⟨lt.2 i, h1, ?_⟩
    rcases g.lower_rail_parent hlt hr i with hf | ⟨hr', hl⟩
    · exact Or.inl hf
    · right; refine ⟨hr', ?_⟩; simp only [mu]; rw [← he] at hle ⊢; omega
  have useU : ut.1 = dec p.2 → isRail (dec p.2) = true → lvl (dec p.1) ≤ lvl (dec p.2) →
      ∃ c, (dec q.1 = c ∨ dec q.2 = c) ∧ (isFill c = true ∨ (isRail c = true ∧ g.mu p < lvl c)) := by
    intro he hr hle
    rw [← he] at hr
    refine ⟨ut.2 i, h2, ?_⟩
    rcases g.upper_rail_parent hut hr i with hf | ⟨hr', hl⟩
    · exact Or.inl hf
    · right; refine ⟨hr', ?_⟩; simp only [mu]; rw [← he] at hle ⊢; omega
  rcases Nat.le_total (lvl (dec p.2)) (lvl (dec p.1)) with hle | hle
  · -- `a` has maximal level, hence is a rail token
    have hra : isRail (dec p.1) = true := by
      rcases hp.2 with hr | hr
      · exact hr
      · apply lvl_pos_rail
        have : 0 < lvl (dec p.2) := by
          cases hb : dec p.2 <;> simp_all [isRail, lvl]
        omega
    obtain ⟨r, k, hrk⟩ : ∃ r k, dec p.1 = .rail r k := by
      cases ha : dec p.1 <;> simp_all [isRail]
    rcases g.cls_rail r k with hc | hc
    · rw [← hrk] at hc
      exact useL (g.inv_to_L hc hla) hra hle
    · rw [← hrk] at hc
      have hb := g.inv_from_R hc hab
      have hu := g.inv_from_R (by rw [hb]; exact hc) hbu
      exact useU hu (by rw [hb]; exact hra) (by rw [hb])
  · have hrb : isRail (dec p.2) = true := by
      rcases hp.2 with hr | hr
      · apply lvl_pos_rail
        have : 0 < lvl (dec p.1) := by
          cases ha : dec p.1 <;> simp_all [isRail, lvl]
        omega
      · exact hr
    obtain ⟨r, k, hrk⟩ : ∃ r k, dec p.2 = .rail r k := by
      cases hb : dec p.2 <;> simp_all [isRail]
    rcases g.cls_rail r k with hc | hc
    · rw [← hrk] at hc
      have ha := g.inv_to_L hc hab
      have hl := g.inv_to_L (by rw [ha]; exact hc) hla
      exact useL hl (by rw [ha]; exact hrb) (by rw [ha])
    · rw [← hrk] at hc
      exact useU (g.inv_from_R hc hbu) hrb hle

/-- **Claim 2**: edges out of fresh vertices go to fill vertices or strictly up in level. -/
theorem fresh_step {p q : Vertex (size n g.N)} (hp : g.VFresh p) (h : PairStep g.POL g.theta p q) :
    g.VFill q ∨ (g.VFresh q ∧ g.mu p < g.mu q) := by
  obtain ⟨c, hc, hk⟩ := g.fresh_advance hp h
  rcases hk with hf | ⟨hr, hl⟩
  · left; rcases hc with hc | hc <;> rw [← hc] at hf <;> simp [VFill, hf]
  · by_cases hF : g.VFill q
    · exact Or.inl hF
    · right
      refine ⟨⟨hF, by rcases hc with hc | hc <;> rw [← hc] at hr <;> simp [hr]⟩, ?_⟩
      simp only [mu] at hl ⊢
      rcases hc with hc | hc <;> rw [hc] <;> omega

/-- **Claim 3**: edges out of old vertices. -/
theorem old_step {p q : Vertex (size n g.N)} {a0 b0 : Fin n} (ha : dec p.1 = .orig a0)
    (hb : dec p.2 = .orig b0) (h : PairStep g.POL g.theta p q) :
    (∃ c0 d0, dec q.1 = .orig c0 ∧ dec q.2 = .orig d0 ∧ PairStep g.POL g.φ (a0, b0) (c0, d0)) ∨
      g.VFill q ∨ g.VFresh q := by
  obtain ⟨i, lt, hlt, ut, hut, hab, hla, hbu, hq⟩ := g.step_unpack h
  have hq' := g.dec_q hq
  rcases g.lower_cases hlt with ⟨a, ha', rfl⟩ | hl
  · rcases g.upper_cases hut with ⟨b, hb', rfl⟩ | hu
    · left
      rw [ha, hb] at hab
      rw [ha] at hla
      rw [hb] at hbu
      have s1 := g.inv_orig_orig hab
      have s2 := g.inv_orig_orig (by simpa [origLit] using hla)
      have s3 := g.inv_orig_orig (by simpa [origLit] using hbu)
      refine ⟨if g.POL i = true then b.2 i else a.2 i, if g.POL i = true then a.2 i else b.2 i,
        ?_, ?_, s1, i, a, ha', b, hb', s2, s3, by split_ifs <;> rfl⟩ <;>
        split_ifs at hq with hi <;> subst hq <;> simp [origLit, hi]
    · right
      exact g.fill_or_fresh (c := ut.2 i)
        (by rcases hq' with ⟨_, h⟩ | ⟨h, _⟩; exact Or.inr h; exact Or.inl h)
        (by rcases hu i with h | h; exact Or.inl h; exact Or.inr h.1)
  · right
    exact g.fill_or_fresh (c := lt.2 i)
      (by rcases hq' with ⟨h, _⟩ | ⟨_, h⟩; exact Or.inl h; exact Or.inr h)
      (by rcases hl i with h | h; exact Or.inl h; exact Or.inr h.1)

theorem fresh_path {p q : Vertex (size n g.N)} (h : Relation.TransGen (PairStep g.POL g.theta) p q)
    (hp : g.VFresh p) : g.VFill q ∨ (g.VFresh q ∧ g.mu p < g.mu q) := by
  induction h with
  | single h => exact g.fresh_step hp h
  | tail _ hs ih =>
      rcases ih with hf | ⟨hf, hl⟩
      · exact absurd hs (g.fill_no_step hf)
      · rcases g.fresh_step hf hs with h' | ⟨h', hl'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨h', by omega⟩

theorem old_path {p q : Vertex (size n g.N)} (h : Relation.TransGen (PairStep g.POL g.theta) p q)
    {a0 b0 : Fin n} (ha : dec p.1 = .orig a0) (hb : dec p.2 = .orig b0) :
    (∃ c0 d0, dec q.1 = .orig c0 ∧ dec q.2 = .orig d0 ∧
        Relation.TransGen (PairStep g.POL g.φ) (a0, b0) (c0, d0)) ∨ g.VFill q ∨ g.VFresh q := by
  induction h with
  | single h =>
      rcases g.old_step ha hb h with ⟨c0, d0, h1, h2, hs⟩ | h'
      · exact Or.inl ⟨c0, d0, h1, h2, .single hs⟩
      · exact Or.inr h'
  | tail _ hs ih =>
      rcases ih with ⟨c0, d0, h1, h2, hp⟩ | hf | hf
      · rcases g.old_step h1 h2 hs with ⟨e0, f0, h3, h4, hs'⟩ | h'
        · exact Or.inl ⟨e0, f0, h3, h4, hp.tail hs'⟩
        · exact Or.inr h'
      · exact absurd hs (g.fill_no_step hf)
      · rcases g.fresh_step hf hs with h' | ⟨h', _⟩
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr h')

/-- **Lemma F2 (⇒)**: a cycle of `G_Θ` is a cycle of `G_φ`. -/
theorem signedC4_of_theta (h : SignedC4 g.POL g.theta) : SignedC4 g.POL g.φ := by
  obtain ⟨p, hp⟩ := h
  rcases tok_kinds (dec p.1) with hf1 | hr1 | ⟨a0, ha⟩
  · rcases Relation.TransGen.head'_iff.mp hp with ⟨q, hq, _⟩
    exact absurd hq (g.fill_no_step (Or.inl hf1))
  · by_cases hF : g.VFill p
    · rcases Relation.TransGen.head'_iff.mp hp with ⟨q, hq, _⟩
      exact absurd hq (g.fill_no_step hF)
    · rcases g.fresh_path hp ⟨hF, Or.inl hr1⟩ with h | ⟨_, h⟩
      · exact absurd h hF
      · omega
  · rcases tok_kinds (dec p.2) with hf2 | hr2 | ⟨b0, hb⟩
    · rcases Relation.TransGen.head'_iff.mp hp with ⟨q, hq, _⟩
      exact absurd hq (g.fill_no_step (Or.inr hf2))
    · by_cases hF : g.VFill p
      · rcases Relation.TransGen.head'_iff.mp hp with ⟨q, hq, _⟩
        exact absurd hq (g.fill_no_step hF)
      · rcases g.fresh_path hp ⟨hF, Or.inr hr2⟩ with h | ⟨_, h⟩
        · exact absurd h hF
        · omega
    · rcases g.old_path hp ha hb with ⟨c0, d0, h1, h2, hc⟩ | hf | hf
      · rw [ha] at h1; rw [hb] at h2
        cases h1; cases h2
        exact ⟨_, hc⟩
      · rcases hf with hf | hf
        · rw [ha] at hf; exact Bool.noConfusion hf
        · rw [hb] at hf; exact Bool.noConfusion hf
      · rcases hf.2 with hf | hf
        · rw [ha] at hf; exact Bool.noConfusion hf
        · rw [hb] at hf; exact Bool.noConfusion hf

/-- **Lemma F2 (⇐)**: `G_φ ⊆ G_Θ`. -/
theorem signedC4_theta_of (h : SignedC4 g.POL g.φ) : SignedC4 g.POL g.theta := by
  obtain ⟨p, hp⟩ := h
  let e : Vertex n → Vertex (size n g.N) := fun p => (enc (Tok.orig p.1), enc (Tok.orig p.2))
  refine ⟨e p, Relation.TransGen.lift e (fun p q hpq => ?_) hp⟩
  obtain ⟨hs, i, a, ha, b, hb, h1, h2, hq⟩ := hpq
  refine ⟨g.support_lift hs, i, _, g.origLit_lower ha, _, g.origLit_upper hb,
    g.support_lift h1, g.support_lift h2, ?_⟩
  subst hq
  split_ifs <;> rfl

/-- **Lemma F2** (v1366 §3). -/
theorem signedC4_theta_iff : SignedC4 g.POL g.theta ↔ SignedC4 g.POL g.φ :=
  ⟨g.signedC4_of_theta, g.signedC4_theta_of⟩

end Setup

end NSSE.ContraGadget
