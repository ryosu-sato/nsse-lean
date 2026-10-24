import NSSE.ContraGadgetSupport
import NSSE.CommonSuffixPeriod

/-! # Completeness of the set-token automaton (stage S4, part 3)

notes_v1364 §4 (Lemma C), §5 (Theorem D), with Lemma E (`NSSE.ContraGadget`) and v1362 Theorem 7
(S2, the two-set model).

* **Lemma C** (`accepts_of_clash`): for `d > 0` and a clash-free `φ`, every clash of the gadget
  `Θ(φ, w, side)` gives an acceptance of `w` by the side automaton. The case split is on the
  sources of the two clash tokens (original literal, or the rail), read through the explicit
  support of Theorem B (`support_inv`):
  - a crossing at an out-position into an original bot variable, or at an in-position from an
    original top variable, is an escape (`xBot`/`yTop`) at that prefix (`acc_out_bot`,
    `acc_in_top`);
  - the leaf token against an original upper (lower) parent is a tracked move at `w`
    (`acc_track_upper`, `acc_track_lower`; this is where `d > 0` is used);
  - a zipped pair through the leaf position is a support escape (equal base levels) or a P-edge
    with anchor the shallower base position, root the zipped period and the tail `w[j:]`
    (`acc_zip`; the eight rows of the P-edge table are `pedge_rows`).
* **Theorem D** (`theta_clash_free`): if the side automaton rejects `w`, then `Θ` is clash-free.
* **Completeness** (`rejected_countermodel`): if `φ` is satisfiable and the side automaton
  rejects `w`, the two-set model of `Θ`, restricted to the original variables, is a REGULAR
  solution of `φ` that fails `side`-safety at `w`. Hence `complete_of_satisfiable`.

The hypothesis `0 < d` is necessary for `Complete` (with `d = 0` the system `{f ≤ y}` makes `ε`
right-safe for `x ≤ y` while no tracked move exists); the hypothesis that `φ` is satisfiable is
necessary because `Complete` is false for unsatisfiable systems (every word is vacuously safe).
-/

namespace NSSE.ContraGadget

open SubtypeConstraints (Constraints Query BoundLiteral)
open AbsorbingSubtypeTrees
open ContraTrees ContraRegularTrees ContraConstraints ContraSupport ContraClashes ContraAutomaton
open ContraSoundness
open ForwardTableAutomaton (Side)

variable {n d : Nat}

namespace Setup

variable (g : Setup n d)

/-- The query of the setup. -/
def query : Query n d := ⟨g.φ, g.x, g.y⟩

/-- Acceptance of `w` by the side automaton. -/
def Acc : Prop := ForwardCapAutomaton.Accepts (automaton g.POL g.query g.side) g.w

theorem st_eq_stateAt (k : Nat) : g.st k = stateAt g.POL g.query (g.w.take k) := rfl

theorem stN_eq : g.st g.N = stateAt g.POL g.query g.w := by
  simp [st_eq_stateAt]

/-! ## Acceptance from finality, escapes and tracked moves -/

theorem acc_final (h : Final g.D g.side (g.st g.N)) : g.Acc :=
  Or.inl ((ordinary_accepts_iff g.query g.side g.w).mpr (by rw [← stN_eq]; exact h))

theorem acc_none {k : Nat} (h : g.st k = none) : g.Acc := by
  apply g.acc_final
  rw [g.st_drop k, h, run_all]
  trivial

theorem acc_escape {k : Nat} {q : Triple n} (hq : g.st k = some q)
    (he : Escape g.D q) : g.Acc := by
  apply g.acc_final
  rw [g.st_drop k, hq]
  cases hw : g.w.drop k with
  | nil => exact Or.inl he
  | cons i rest => rw [run_cons, delta_escape _ _ he, run_all]; trivial

theorem st_some (k : Nat) (hN : g.st g.N ≠ none) : ∃ q, g.st k = some q := by
  cases h : g.st k with
  | none => exact absurd (by rw [g.st_drop k, h, run_all]) hN
  | some q => exact ⟨q, rfl⟩

theorem tokSet_eq_tracked (q : Triple n) : tokSet g.leaf q = tracked g.side q := by
  rw [tracked_eq]; rfl

/-- A crossing at an out-position into an original bot variable is an escape. -/
theorem acc_out_bot {r : Bool} {k : Nat} (_hk : k ≤ g.N) (ho : g.out r k = true) {b : Fin n}
    (hp : g.PSet r k b) (hb : b ∈ g.φ.bot) : g.Acc := by
  cases hst : g.st k with
  | none => exact g.acc_none hst
  | some q =>
      unfold PSet at hp
      rw [hst] at hp
      obtain ⟨t, ht, hs⟩ := hp
      rw [if_pos ho] at hs
      have hσ : q.2.2 = r := by rw [g.st_sigma hst]; simpa [out] using ho
      have hbot : g.D.bot t = true := (bot_correct _ _).mpr ⟨b, hb, hs⟩
      refine g.acc_escape hst ?_
      cases r
      · exact Or.inl ⟨t, ht, by simp [xBot, hσ, hbot]⟩
      · exact Or.inr (Or.inl ⟨t, ht, by simp [yTop, hσ, hbot]⟩)

/-- A crossing at an in-position from an original top variable is an escape. -/
theorem acc_in_top {r : Bool} {k : Nat} (_hk : k ≤ g.N) (ho : g.out r k = false) {t0 : Fin n}
    (hp : g.PSet r k t0) (ht0 : t0 ∈ g.φ.top) : g.Acc := by
  cases hst : g.st k with
  | none => exact g.acc_none hst
  | some q =>
      unfold PSet at hp
      rw [hst] at hp
      obtain ⟨t, ht, hs⟩ := hp
      rw [if_neg (by simp [ho])] at hs
      have hσ : q.2.2 = !r := by
        rw [g.st_sigma hst]; revert ho; simp only [out]; cases g.sig k <;> cases r <;> simp
      have htop : g.D.top t = true := (top_correct _ _).mpr ⟨t0, ht0, hs⟩
      refine g.acc_escape hst ?_
      cases r
      · exact Or.inl ⟨t, ht, by simp [xBot, hσ, htop]⟩
      · exact Or.inr (Or.inl ⟨t, ht, by simp [yTop, hσ, htop]⟩)

/-- The leaf token (out-position) against an original upper parent: a tracked move at `w`. -/
theorem acc_track_upper (hd : 0 < d) (ho : g.out g.leaf g.N = true) {a : BoundLiteral n d}
    (ha : a ∈ g.φ.upper) (hp : g.PSet g.leaf g.N a.1) : g.Acc := by
  cases hst : g.st g.N with
  | none => exact g.acc_none hst
  | some q =>
      unfold PSet at hp
      rw [hst] at hp
      obtain ⟨t, ht, hs⟩ := hp
      rw [if_pos ho] at hs
      have hσ : q.2.2 = g.leaf := by rw [g.st_sigma hst]; simpa [out] using ho
      let i : Fin d := ⟨0, hd⟩
      have hup : g.D.upper t i (a.2 i) = true :=
        (upper_correct _ _ _ _).mpr ⟨a, ha, hs, by unfold SupportAt; split_ifs <;> exact .refl _⟩
      apply g.acc_final
      rw [hst]
      refine Or.inr ⟨t, i, a.2 i, by rw [← g.tokSet_eq_tracked]; exact ht, ?_⟩
      cases hs' : g.side <;> simp [leaf, hs', leafRail] at hσ <;>
        simp [trackedMove, xMove, yMove, hσ, hup]

/-- The leaf token (in-position) against an original lower parent: a tracked move at `w`. -/
theorem acc_track_lower (hd : 0 < d) (ho : g.out g.leaf g.N = false) {a : BoundLiteral n d}
    (ha : a ∈ g.φ.lower) (hp : g.PSet g.leaf g.N a.1) : g.Acc := by
  cases hst : g.st g.N with
  | none => exact g.acc_none hst
  | some q =>
      unfold PSet at hp
      rw [hst] at hp
      obtain ⟨t, ht, hs⟩ := hp
      rw [if_neg (by simp [ho])] at hs
      have hσ : q.2.2 = !g.leaf := by
        rw [g.st_sigma hst]; revert ho; simp only [out]; cases g.sig g.N <;> cases g.leaf <;> simp
      let i : Fin d := ⟨0, hd⟩
      have hlo : g.D.lower t i (a.2 i) = true :=
        (lower_correct _ _ _ _).mpr ⟨a, ha, by unfold SupportAt; split_ifs <;> exact .refl _, hs⟩
      apply g.acc_final
      rw [hst]
      refine Or.inr ⟨t, i, a.2 i, by rw [← g.tokSet_eq_tracked]; exact ht, ?_⟩
      cases hs' : g.side <;> simp [leaf, hs', leafRail] at hσ <;>
        simp [trackedMove, xMove, yMove, hσ, hlo]

/-! ## The zipped case -/

/-- A base pair of positions: out-position, in-position, related path sets. -/
def Base (ra : Bool) (ja : Nat) (rb : Bool) (jb : Nat) : Prop :=
  g.out ra ja = true ∧ g.out rb jb = false ∧
    ∃ z z', g.PSet ra ja z ∧ g.PSet rb jb z' ∧ Support g.POL g.φ z z'

theorem take_succ_drop {j t : Nat} {i : Fin d} (h : g.w[j + t]? = some i) :
    (g.w.drop j).take (t + 1) = (g.w.drop j).take t ++ [i] := by
  rw [List.take_succ, List.getElem?_drop, h]; rfl

/-- Explicit form of a zipper pair: a base pair shifted along a common factor. -/
theorem zip_data {r1 k1 r2 k2} (h : g.Zip r1 k1 r2 k2) :
    ∃ ra ja rb jb t, g.Base ra ja rb jb ∧ ja + t ≤ g.N ∧ jb + t ≤ g.N ∧
      (g.w.drop ja).take t = (g.w.drop jb).take t ∧
      ((r1 = ra ∧ k1 = ja + t ∧ r2 = rb ∧ k2 = jb + t) ∨
        (r1 = rb ∧ k1 = jb + t ∧ r2 = ra ∧ k2 = ja + t)) := by
  induction h with
  | @base r1 k1 r2 k2 z z' h1 h2 o1 o2 hz hz' hs =>
      exact ⟨r1, k1, r2, k2, 0, ⟨o1, o2, z, z', hz, hz', hs⟩, by omega, by omega, by simp,
        Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  | @cov r1 k1 r2 k2 i _ e1 e2 _ ih =>
      obtain ⟨ra, ja, rb, jb, t, hb, h1, h2, he, ho⟩ := ih
      have l1 := g.lt_of_getElem? e1
      have l2 := g.lt_of_getElem? e2
      rcases ho with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · refine ⟨r1, ja, r2, jb, t + 1, hb, by omega, by omega, ?_, Or.inl ⟨rfl, by omega, rfl, by omega⟩⟩
        rw [g.take_succ_drop e1, g.take_succ_drop e2, he]
      · refine ⟨r2, ja, r1, jb, t + 1, hb, by omega, by omega, ?_, Or.inr ⟨rfl, by omega, rfl, by omega⟩⟩
        rw [g.take_succ_drop e1, g.take_succ_drop e2, he]
  | @con r1 k1 r2 k2 i _ e1 e2 _ ih =>
      obtain ⟨ra, ja, rb, jb, t, hb, h1, h2, he, ho⟩ := ih
      have l1 := g.lt_of_getElem? e1
      have l2 := g.lt_of_getElem? e2
      rcases ho with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · refine ⟨r1, ja, r2, jb, t + 1, hb, by omega, by omega, ?_, Or.inr ⟨rfl, by omega, rfl, by omega⟩⟩
        rw [g.take_succ_drop e1, g.take_succ_drop e2, he]
      · refine ⟨r2, ja, r1, jb, t + 1, hb, by omega, by omega, ?_, Or.inl ⟨rfl, by omega, rfl, by omega⟩⟩
        rw [g.take_succ_drop e1, g.take_succ_drop e2, he]

/-- Equal base levels: a support escape. -/
theorem escape_base {ra rb : Bool} {j : Nat} (oa : g.out ra j = true) (ob : g.out rb j = false)
    {q : Triple n} (hq : g.st j = some q) {ta tb : Fin n} (hta : tokSet ra q ta = true)
    (htb : tokSet rb q tb = true) (hs : Support g.POL g.φ ta tb) : Escape g.D q := by
  have hσ := g.st_sigma hq
  have hle : g.D.le ta tb = true := (le_correct _ _ _).mpr hs
  simp only [out, beq_iff_eq, beq_eq_false_iff_ne] at oa ob
  refine Or.inr (Or.inr ?_)
  cases ra <;> cases rb
  · exact absurd oa ob
  · refine ⟨ta, tb, hta, htb, ?_⟩
    simp only [LeS, hσ, oa, Bool.false_eq_true, if_false]; exact hle
  · refine ⟨tb, ta, htb, hta, ?_⟩
    simp only [LeS, hσ, oa, if_true]; exact hle
  · exact absurd oa ob

/-- The eight rows of the P-edge table (v1362 §3), as forced by the zipped clash (v1364 §4):
the post-root position is the leaf position. -/
theorem pedge_rows {jO jL : Nat} {rO : Bool} {q s : Triple n} (hq : g.st jO = some q)
    (hs : g.st jL = some s) {tO tL : Fin n} (htO : tokSet rO q tO = true)
    (htL : tokSet g.leaf s tL = true)
    (hdir : if g.out g.leaf jL = true then Support g.POL g.φ tL tO else Support g.POL g.φ tO tL)
    (hopp : g.out rO jO = !g.out g.leaf jL) :
    PEdge g.D g.side (some s) (some q) := by
  have hσq := g.st_sigma hq
  have hσs := g.st_sigma hs
  have hle : ∀ a b, Support g.POL g.φ a b → g.D.le a b = true := fun a b h => (le_correct _ _ _).mpr h
  unfold leaf at htL hdir hopp
  simp only [out] at hdir hopp
  cases hside : g.side <;> simp only [hside, leafRail] at htL hdir hopp <;>
    cases rO <;> simp only [tokSet, if_true, if_false, Bool.false_eq_true] at htO htL <;>
    simp only [PEdge, hσq, hσs, LeS]
  · -- left, anchor on the x-rail: odd row
    have hx : xor (g.sig jO) (g.sig jL) = true := by
      revert hopp; cases g.sig jO <;> cases g.sig jL <;> simp
    rw [if_pos hx]
    refine ⟨tO, tL, htO, htL, ?_⟩
    revert hdir; cases g.sig jL <;> intro hdir <;> simp at hdir ⊢ <;> exact hle _ _ hdir
  · -- left, anchor on the y-rail: even row
    have hx : g.sig jO = g.sig jL := by
      revert hopp; cases g.sig jO <;> cases g.sig jL <;> simp
    rw [hx, if_neg (by simp)]
    refine ⟨tL, tO, htL, htO, ?_⟩
    revert hdir; cases g.sig jL <;> intro hdir <;> simp at hdir ⊢ <;> exact hle _ _ hdir
  · -- right, anchor on the x-rail: even row
    have hx : g.sig jO = g.sig jL := by
      revert hopp; cases g.sig jO <;> cases g.sig jL <;> simp
    rw [hx, if_neg (by simp)]
    refine ⟨tO, tL, htO, htL, ?_⟩
    revert hdir; cases g.sig jL <;> intro hdir <;> simp at hdir ⊢ <;> exact hle _ _ hdir
  · -- right, anchor on the y-rail: odd row
    have hx : xor (g.sig jO) (g.sig jL) = true := by
      revert hopp; cases g.sig jO <;> cases g.sig jL <;> simp
    rw [if_pos hx]
    refine ⟨tL, tO, htL, htO, ?_⟩
    revert hdir; cases g.sig jL <;> intro hdir <;> simp at hdir ⊢ <;> exact hle _ _ hdir

/-- The core of the zipped case: a base pair between the leaf position `(leaf, jL)` and a
shallower position `(rO, jO)` whose shifted copies end at the leaf position. -/
theorem acc_leaf_base {jL jO : Nat} {rO : Bool}
    (hb : g.Base g.leaf jL rO jO ∨ g.Base rO jO g.leaf jL) (hle : jO ≤ jL) (hL : jL ≤ g.N)
    (hpre : g.w.drop jL <+: g.w.drop jO) : g.Acc := by
  by_cases hN : g.st g.N = none
  · exact g.acc_none hN
  obtain ⟨q, hq⟩ := g.st_some jO hN
  obtain ⟨s, hs⟩ := g.st_some jL hN
  have hL' : jL ≤ g.w.length := hL
  -- tokens and the directed relation between them
  obtain ⟨tO, tL, htO, htL, hdir, hopp⟩ : ∃ tO tL, tokSet rO q tO = true ∧ tokSet g.leaf s tL = true ∧
      (if g.out g.leaf jL = true then Support g.POL g.φ tL tO else Support g.POL g.φ tO tL) ∧
      g.out rO jO = !g.out g.leaf jL := by
    rcases hb with ⟨oa, ob, z, z', hz, hz', hzz⟩ | ⟨oa, ob, z, z', hz, hz', hzz⟩
    · unfold PSet at hz hz'
      rw [hs] at hz; rw [hq] at hz'
      obtain ⟨tL, htL, h1⟩ := hz
      obtain ⟨tO, htO, h2⟩ := hz'
      rw [if_pos oa] at h1; rw [if_neg (by simp [ob])] at h2
      exact ⟨tO, tL, htO, htL, by rw [if_pos oa]; exact (h1.trans hzz).trans h2, by rw [ob, oa]; rfl⟩
    · unfold PSet at hz hz'
      rw [hq] at hz; rw [hs] at hz'
      obtain ⟨tO, htO, h1⟩ := hz
      obtain ⟨tL, htL, h2⟩ := hz'
      rw [if_pos oa] at h1; rw [if_neg (by simp [ob])] at h2
      exact ⟨tO, tL, htO, htL, by rw [if_neg (by simp [ob])]; exact (h1.trans hzz).trans h2,
        by rw [ob, oa]; rfl⟩
  rcases Nat.lt_or_ge jO jL with hlt | hge
  · -- a P-edge with anchor `w[:jO]`, root `w[jO:jL]`, tail `w[jO:]`
    set root := (g.w.drop jO).take (jL - jO) with hroot
    have hrun : run g.D g.POL (g.st jO) root = g.st jL := by
      simp only [st, root]
      rw [← run_append, ← List.take_add, Nat.add_sub_cancel' hle]
    have hrlen : root.length = jL - jO := by
      simp only [root, List.length_take, List.length_drop]; omega
    have hne : root ≠ [] := by
      intro h; rw [h] at hrlen; simp at hrlen; omega
    have hsplit : g.w.drop jO = root ++ g.w.drop jL := by
      rw [← List.take_append_drop (jL - jO) (g.w.drop jO), List.drop_drop, Nat.add_sub_cancel' hle]
    have hover : g.w.drop jL <+: root ++ g.w.drop jL := by rw [← hsplit]; exact hpre
    obtain ⟨k, hk⟩ := CommonSuffixPeriod.self_overlap_power root (g.w.drop jL) hne hover
    have hfin : Final g.D g.side (g.st jO) := by
      have htr : TrackedNonempty g.side (run g.D g.POL (g.st jO) root) := by
        rw [hrun, hs]; exact ⟨tL, by rw [← g.tokSet_eq_tracked]; exact htL⟩
      exact (tracked_run g.D g.POL g.side (g.st jO) root htr).2 hne
    have hpe : PEdge g.D g.side (run g.D g.POL (g.st jO) root) (g.st jO) := by
      rw [hrun, hs, hq]; exact g.pedge_rows hq hs htO htL hdir hopp
    refine Or.inr ((capped_iff g.query g.side g.w).mpr ⟨g.w.take jO, g.w.drop jO, root, k,
      (List.take_append_drop _ _).symm, hfin, hpe, ?_⟩)
    rw [hsplit]; exact hk
  · -- equal levels: a support escape
    have hj : jO = jL := le_antisymm hle hge
    subst hj
    refine g.acc_escape hq ?_
    have hs' := hs; rw [hq] at hs'; cases hs'
    split at hdir
    · rename_i ho
      exact g.escape_base ho (by rw [hopp, ho]; rfl) hq htL htO hdir
    · rename_i ho
      have ho' : g.out g.leaf jO = false := by simpa using ho
      exact g.escape_base (by rw [hopp, ho']; rfl) ho' hq htO htL hdir

/-- **The zipped case of Lemma C**: a zipper pair through the leaf position gives acceptance. -/
theorem acc_zip {r1 k1 r2 k2} (h : g.Zip r1 k1 r2 k2)
    (hleaf : (r1 = g.leaf ∧ k1 = g.N) ∨ (r2 = g.leaf ∧ k2 = g.N)) : g.Acc := by
  obtain ⟨ra, ja, rb, jb, t, hb, h1, h2, he, ho⟩ := g.zip_data h
  have hfull : ∀ j, j + t = g.N → (g.w.drop j).take t = g.w.drop j := fun j hj => by
    have hj' : j + t = g.w.length := hj
    exact List.take_of_length_le (by simp only [List.length_drop]; omega)
  rcases ho with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    rcases hleaf with ⟨hr, hk⟩ | ⟨hr, hk⟩ <;> subst hr
  · exact g.acc_leaf_base (Or.inl hb) (by omega) (by omega)
      (by rw [← hfull ja hk, he]; exact List.take_prefix _ _)
  · exact g.acc_leaf_base (Or.inr hb) (by omega) (by omega)
      (by rw [← hfull jb hk, ← he]; exact List.take_prefix _ _)
  · exact g.acc_leaf_base (Or.inr hb) (by omega) (by omega)
      (by rw [← hfull jb hk, ← he]; exact List.take_prefix _ _)
  · exact g.acc_leaf_base (Or.inl hb) (by omega) (by omega)
      (by rw [← hfull ja hk, he]; exact List.take_prefix _ _)

/-! ## Lemma C and Theorem D -/

theorem inv_tt_left {b : Tok n g.N} (h : g.Inv .tt b) : b = .tt := g.inv_from_R (by simp [cls]) h
theorem inv_bt_right {a : Tok n g.N} (h : g.Inv a .bt) : a = .bt := g.inv_to_L (by simp [cls]) h

/-- **Lemma C** (v1364 §4): every clash of `Θ` is an acceptance clause of the side automaton. -/
theorem accepts_of_clash (hd : 0 < d) (hφ : ¬ Clash g.POL g.φ) (h : Clash g.POL g.theta) :
    g.Acc := by
  have hNl : g.N ≤ g.N := le_rfl
  rcases h with ⟨a, ha, b, hb, hs⟩ | ⟨a, ha, l, hl, hs⟩ | ⟨l, hl, b, hb, hs⟩
  · -- C1: top variable ≤s bot variable
    obtain ⟨ta, hta, rfl⟩ := g.mem_theta_top.mp ha
    obtain ⟨tb, htb, rfl⟩ := g.mem_theta_bot.mp hb
    have hi := g.support_inv_enc hs
    rcases (g.mem_tokTop ta).mp hta with ⟨v, hv, rfl⟩ | rfl | ⟨ho, rfl⟩ <;>
    rcases (g.mem_tokBot tb).mp htb with ⟨v', hv', rfl⟩ | rfl | ⟨ho', rfl⟩
    · exact absurd (Or.inl ⟨v, hv, v', hv', g.inv_orig_orig hi⟩) hφ
    · exact Tok.noConfusion (g.inv_bt_right hi)
    · exact g.acc_in_top hNl ho' (g.inv_orig_pos hNl ho' hi) hv
    · exact Tok.noConfusion (g.inv_tt_left hi)
    · exact Tok.noConfusion (g.inv_tt_left hi)
    · exact absurd (g.inv_tt_left hi) (g.tokP_ne_tt hNl)
    · exact g.acc_out_bot hNl ho (g.inv_pos_orig hNl ho hi) hv'
    · exact absurd (g.inv_bt_right hi) (g.tokP_ne_bt hNl)
    · rw [ho] at ho'; exact Bool.noConfusion ho'
  · -- C2: top variable ≤s upper parent
    obtain ⟨ta, hta, rfl⟩ := g.mem_theta_top.mp ha
    obtain ⟨u, hu, rfl⟩ := g.mem_theta_upper.mp hl
    have hi := g.support_inv_enc hs
    rcases (g.mem_tokTop ta).mp hta with ⟨v, hv, rfl⟩ | rfl | ⟨ho, rfl⟩ <;>
    rcases (g.mem_tokUpper u).mp hu with ⟨c, hc, rfl⟩ | ⟨r, k, hk, ho', _, rfl⟩
    · exact absurd (Or.inr (Or.inl ⟨v, hv, c, hc, g.inv_orig_orig hi⟩)) hφ
    · exact g.acc_in_top hk ho' (g.inv_orig_pos hk ho' hi) hv
    · exact Tok.noConfusion (g.inv_tt_left hi)
    · exact absurd (g.inv_tt_left hi) (g.tokP_ne_tt hk)
    · exact g.acc_track_upper hd ho hc (g.inv_pos_orig hNl ho hi)
    · exact g.acc_zip (g.inv_pos_pos hNl hk ho ho' hi) (Or.inl ⟨rfl, rfl⟩)
  · -- C3: lower parent ≤s bot variable
    obtain ⟨u, hu, rfl⟩ := g.mem_theta_lower.mp hl
    obtain ⟨tb, htb, rfl⟩ := g.mem_theta_bot.mp hb
    have hi := g.support_inv_enc hs
    rcases (g.mem_tokLower u).mp hu with ⟨c, hc, rfl⟩ | ⟨r, k, hk, ho, _, rfl⟩ <;>
    rcases (g.mem_tokBot tb).mp htb with ⟨v', hv', rfl⟩ | rfl | ⟨ho', rfl⟩
    · exact absurd (Or.inr (Or.inr ⟨c, hc, v', hv', g.inv_orig_orig hi⟩)) hφ
    · exact Tok.noConfusion (g.inv_bt_right hi)
    · exact g.acc_track_lower hd ho' hc (g.inv_orig_pos hNl ho' hi)
    · exact g.acc_out_bot hk ho (g.inv_pos_orig hk ho hi) hv'
    · exact absurd (g.inv_bt_right hi) (g.tokP_ne_bt hk)
    · exact g.acc_zip (g.inv_pos_pos hk hNl ho ho' hi) (Or.inr ⟨rfl, rfl⟩)

/-- **Theorem D** (v1364 §5): if the side automaton rejects `w`, the gadget is clash-free. -/
theorem theta_clash_free (hd : 0 < d) (hφ : ¬ Clash g.POL g.φ) (hrej : ¬ g.Acc) :
    ¬ Clash g.POL g.theta :=
  fun h => hrej (g.accepts_of_clash hd hφ h)

/-! ## The countermodel -/

/-- The two-set model of `Θ` restricted to the original variables. -/
def countermodel (v : Fin n) : CTree g.POL :=
  ContraSatisfiability.model g.POL g.theta (enc (Tok.orig v))

theorem countermodel_regular (v : Fin n) : CRegular (g.countermodel v) :=
  ContraSatisfiability.model_regular _ _

/-- A clash-free gadget yields a regular solution of `φ` failing `side`-safety at `w`. -/
theorem countermodel_spec (hθ : ¬ Clash g.POL g.theta) :
    Satisfies (treeConstructor g.POL) g.φ g.countermodel ∧
      ¬ CSafe g.POL g.side (g.countermodel g.x) (g.countermodel g.y) g.w := by
  have hm := ContraSatisfiability.model_satisfies g.theta hθ
  exact ⟨g.theta_satisfies_restrict _ _ hm, g.failure hm⟩

/-- Conversely a clash of `Θ` excludes every solution of `Θ`; with Lemma E: `Θ` is clash-free iff
some solution of `φ` fails `side`-safety at `w` through `Θ`. -/
theorem clash_free_iff (hd : 0 < d) (hφ : ¬ Clash g.POL g.φ) :
    ¬ Clash g.POL g.theta ↔ ¬ g.Acc := by
  refine ⟨fun hθ hacc => ?_, g.theta_clash_free hd hφ⟩
  obtain ⟨hs, hf⟩ := g.countermodel_spec hθ
  exact hf (accepts_sound g.query g.side g.w hacc _ hs)

end Setup

/-! ## Completeness for queries -/

/-- The setup of a query, a side and a word. -/
def ofQuery (POL : Polarity d) (Q : Query n d) (side : Side) (w : List (Fin d)) : Setup n d :=
  ⟨POL, Q.constraints, Q.left, Q.right, w, side⟩

theorem ofQuery_acc (POL : Polarity d) (Q : Query n d) (side : Side) (w : List (Fin d)) :
    (ofQuery POL Q side w).Acc ↔ ForwardCapAutomaton.Accepts (automaton POL Q side) w := Iff.rfl

variable {POL : Polarity d}

/-- **Completeness** (v1364 Theorem D with v1362 Theorem 7 and Lemma E): if `φ` is satisfiable and
the side automaton rejects `w`, there is a REGULAR solution of `φ` (in the original coinductive
order) failing `side`-safety at `w`. -/
theorem rejected_countermodel (hd : 0 < d) (Q : Query n d)
    (hsat : Satisfiable (treeConstructor POL) Q.constraints) {side : Side} {w : List (Fin d)}
    (hrej : ¬ ForwardCapAutomaton.Accepts (automaton POL Q side) w) :
    ∃ ρ : Fin n → CTree POL, (∀ v, CRegular (ρ v)) ∧
      Satisfies (treeConstructor POL) Q.constraints ρ ∧ ¬ CSafe POL side (ρ Q.left) (ρ Q.right) w := by
  let g := ofQuery POL Q side w
  have hθ := g.theta_clash_free hd (no_clash_of_satisfiable hsat) hrej
  exact ⟨g.countermodel, g.countermodel_regular, g.countermodel_spec hθ⟩

/-- `Complete` (the S3 target) holds for every satisfiable query. -/
theorem complete_of_satisfiable (hd : 0 < d) (Q : Query n d)
    (hsat : Satisfiable (treeConstructor POL) Q.constraints) (side : Side) : Complete POL Q side := by
  intro w hs
  by_contra hrej
  obtain ⟨ρ, _, hρ, hf⟩ := rejected_countermodel hd Q hsat hrej
  exact hf (hs ρ hρ)

/-- Regular completeness: regular safety already forces acceptance. -/
theorem regular_complete_of_satisfiable (hd : 0 < d) (Q : Query n d)
    (hsat : Satisfiable (treeConstructor POL) Q.constraints) (side : Side) (w : List (Fin d))
    (hs : RegularQuerySafe POL Q side w) : ForwardCapAutomaton.Accepts (automaton POL Q side) w := by
  by_contra hrej
  obtain ⟨ρ, hr, hρ, hf⟩ := rejected_countermodel hd Q hsat hrej
  exact hf (hs ρ hr hρ)

/-- For a satisfiable query, acceptance is exactly safety, over arbitrary and over regular trees. -/
theorem accepts_iff_querySafe (hd : 0 < d) (Q : Query n d)
    (hsat : Satisfiable (treeConstructor POL) Q.constraints) (side : Side) (w : List (Fin d)) :
    ForwardCapAutomaton.Accepts (automaton POL Q side) w ↔ QuerySafe POL Q side w :=
  ⟨accepts_sound Q side w, complete_of_satisfiable hd Q hsat side w⟩

theorem accepts_iff_regularQuerySafe (hd : 0 < d) (Q : Query n d)
    (hsat : Satisfiable (treeConstructor POL) Q.constraints) (side : Side) (w : List (Fin d)) :
    ForwardCapAutomaton.Accepts (automaton POL Q side) w ↔ RegularQuerySafe POL Q side w :=
  ⟨accepts_regular_sound Q side w, regular_complete_of_satisfiable hd Q hsat side w⟩

end NSSE.ContraGadget
