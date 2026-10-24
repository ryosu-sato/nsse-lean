import NSSE.UniformWordLowering

/-!
# Reversed two-block recognition with a column-local guarded switch

The shared phase reads the common suffix backwards. Its switch tests the
predecessors on the SAME column, using fixed defaults for padded tapes.
-/

namespace NSSE.GuardedBlockRelation

open CanonicalConvolution
local notation "decodeCols" => CanonicalConvolution.decode

universe u v
variable {D : Type u} {Q : Type v}

theorem runs_nil_iff (T : NSSE.NFA D Q) (q r : Q) : T.Runs q [] r ↔ q = r := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil q

theorem runs_append_iff (T : NSSE.NFA D Q) (q r : Q) (x y : List D) :
    T.Runs q (x ++ y) r ↔ ∃ s, T.Runs q x s ∧ T.Runs s y r := by
  constructor
  · intro h
    induction x generalizing q with
    | nil => exact ⟨q, .nil q, h⟩
    | cons a x ih =>
        cases h with
        | cons hs ht =>
            obtain ⟨s, hx, hy⟩ := ih _ ht
            exact ⟨s, .cons hs hx, hy⟩
  · rintro ⟨s, hx, hy⟩
    exact hx.append T hy

theorem runs_append_singleton (T : NSSE.NFA D Q) (q r : Q) (w : List D) (a : D) :
    T.Runs q (w ++ [a]) r ↔ ∃ s, T.Runs q w s ∧ T.step s a r := by
  rw [runs_append_iff]
  apply exists_congr
  intro s
  constructor
  · rintro ⟨hw, h⟩
    cases h with
    | cons hstep hnil => cases hnil; exact ⟨hw, hstep⟩
  · rintro ⟨hw, hstep⟩
    exact ⟨hw, .cons hstep (.nil r)⟩

def BackStep (T : NSSE.NFA D Q) (q : Q) (a : Option D) (r : Q) : Prop :=
  match a with
  | none => r = q
  | some x => T.step r x q

theorem reverse_decode_cons (T : NSSE.NFA D Q) (q r : Q)
    (c : Column D 2) (w : List (Column D 2)) (i : Fin 2) :
    T.Runs q (decodeCols (c :: w) i).reverse r ↔
      ∃ s, T.Runs q (decodeCols w i).reverse s ∧ BackStep T r (c i) s := by
  cases hci : c i with
  | none => simp [CanonicalConvolution.decode, List.filterMap_cons, hci, BackStep]
  | some x =>
      simp only [CanonicalConvolution.decode, List.filterMap_cons, hci, List.reverse_cons, BackStep]
      exact runs_append_singleton T q r _ x

def AcceptFrom {A X : Type*} (T : NSSE.NFA A X) (q : X) (w : List A) : Prop :=
  ∃ r, T.Runs q w r ∧ T.accept r

theorem acceptFrom_nil {A X : Type*} (T : NSSE.NFA A X) (q : X) :
    AcceptFrom T q [] ↔ T.accept q := by simp [AcceptFrom, runs_nil_iff]

theorem acceptFrom_cons {A X : Type*} (T : NSSE.NFA A X) (q : X) (a : A) (w : List A) :
    AcceptFrom T q (a :: w) ↔ ∃ r, T.step q a r ∧ AcceptFrom T r w := by
  constructor
  · rintro ⟨t, h, ht⟩
    cases h with
    | cons hstep hrest => exact ⟨_, hstep, t, hrest, ht⟩
  · rintro ⟨r, hstep, t, hrest, ht⟩
    exact ⟨t, .cons hstep hrest, ht⟩

abbrev PairState (Q : Type*) := Q × Q
abbrev State (Q : Type*) := Bool × PairState Q

/-- Only data paths occur in T; the two marker relations are independent. -/
structure Data (D : Type u) (Q : Type v) where
  T : NSSE.NFA D Q
  left : Q → Q → Prop
  right : Q → Q → Prop
  guard : D → D → Prop
  leftDefault : D
  rightDefault : D
  leftStart : Q
  rightStart : Q
  finish : PairState Q → Prop

namespace Data

def prefixMeaning (G : Data D Q) (q : PairState Q) (x y : List D) : Prop :=
  G.T.Runs G.leftStart x.reverse q.1 ∧ G.T.Runs G.rightStart y.reverse q.2

def marked (G : Data D Q) (marker : Q → Q → Prop) (start finish : Q)
    (pref shared : List D) : Prop :=
  ∃ z b, G.T.Runs start pref.reverse z ∧ marker z b ∧ G.T.Runs b shared.reverse finish

def core (G : Data D Q) (q : PairState Q) (x y : List D) : Prop :=
  ∃ shared px py : List D, x = shared ++ px ∧ y = shared ++ py ∧
    G.guard (px.head?.getD G.leftDefault) (py.head?.getD G.rightDefault) ∧
    G.marked G.left G.leftStart q.1 px shared ∧
    G.marked G.right G.rightStart q.2 py shared

def backward (G : Data D Q) (q : PairState Q) (c : Column D 2) (r : PairState Q) : Prop :=
  BackStep G.T q.1 (c 0) r.1 ∧ BackStep G.T q.2 (c 1) r.2

def sharedStep (G : Data D Q) (q : PairState Q) (c : Column D 2) (r : PairState Q) : Prop :=
  (∃ x, c 0 = some x ∧ c 1 = some x) ∧ G.backward q c r

def switch (G : Data D Q) (q : PairState Q) (c : Column D 2) (r : PairState Q) : Prop :=
  G.guard ((c 0).getD G.leftDefault) ((c 1).getD G.rightDefault) ∧
    ∃ z : PairState Q, G.left z.1 q.1 ∧ G.right z.2 q.2 ∧ G.backward z c r

def endSwitch (G : Data D Q) (q : PairState Q) : Prop :=
  G.left G.leftStart q.1 ∧ G.right G.rightStart q.2 ∧ G.guard G.leftDefault G.rightDefault

def automaton (G : Data D Q) : NSSE.NFA (Column D 2) (State Q) where
  start q := q.1 = false ∧ G.finish q.2
  accept q := if q.1 then q.2 = (G.leftStart, G.rightStart) else G.endSwitch q.2
  step q c r := match q.1, r.1 with
    | false, false => G.sharedStep q.2 c r.2
    | false, true => G.switch q.2 c r.2
    | true, true => G.backward q.2 c r.2
    | true, false => False

theorem prefixMeaning_nil (G : Data D Q) (q : PairState Q) :
    G.prefixMeaning q [] [] ↔ q = (G.leftStart, G.rightStart) := by
  simp only [prefixMeaning, List.reverse_nil, runs_nil_iff, Prod.ext_iff]
  exact and_congr eq_comm eq_comm

theorem core_nil (G : Data D Q) (q : PairState Q) : G.core q [] [] ↔ G.endSwitch q := by
  unfold core
  constructor
  · rintro ⟨s, px, py, hx, hy, hg, hl, hr⟩
    obtain ⟨rfl, rfl⟩ := List.nil_eq_append_iff.mp hx
    have hpy : py = [] := by simpa using hy.symm
    subst py
    simp [marked, runs_nil_iff] at hl hr
    exact ⟨hl, hr, hg⟩
  · rintro ⟨hl, hr, hg⟩
    exact ⟨[], [], [], rfl, rfl, hg,
      ⟨G.leftStart, q.1, .nil _, hl, .nil _⟩,
      ⟨G.rightStart, q.2, .nil _, hr, .nil _⟩⟩

theorem prefixMeaning_cons (G : Data D Q) (q : PairState Q)
    (c : Column D 2) (w : List (Column D 2)) :
    G.prefixMeaning q (decodeCols (c :: w) 0) (decodeCols (c :: w) 1) ↔
      ∃ r, G.backward q c r ∧ G.prefixMeaning r (decodeCols w 0) (decodeCols w 1) := by
  simp only [prefixMeaning, reverse_decode_cons, backward]
  constructor
  · rintro ⟨⟨r, hr, hrs⟩, ⟨s, hs, hss⟩⟩
    exact ⟨(r, s), ⟨hrs, hss⟩, hr, hs⟩
  · rintro ⟨⟨r, s⟩, ⟨hrs, hss⟩, hr, hs⟩
    exact ⟨⟨r, hr, hrs⟩, ⟨s, hs, hss⟩⟩

theorem marked_nil (G : Data D Q) (marker : Q → Q → Prop) (start finish : Q) (pref : List D) :
    G.marked marker start finish pref [] ↔ ∃ z, G.T.Runs start pref.reverse z ∧ marker z finish := by
  simp [marked, runs_nil_iff]

theorem marked_cons (G : Data D Q) (marker : Q → Q → Prop) (start finish : Q)
    (pref shared : List D) (x : D) :
    G.marked marker start finish pref (x :: shared) ↔
      ∃ r, G.marked marker start r pref shared ∧ G.T.step r x finish := by
  simp only [marked, List.reverse_cons, runs_append_singleton]
  constructor
  · rintro ⟨z, b, hp, hm, r, hs, hd⟩
    exact ⟨r, ⟨z, b, hp, hm, hs⟩, hd⟩
  · rintro ⟨r, ⟨z, b, hp, hm, hs⟩, hd⟩
    exact ⟨z, b, hp, hm, r, hs, hd⟩

/-- All common-suffix choices are retained. The empty shared suffix is
the column-local switch; a nonempty one is one shared backward step. -/
theorem core_cons (G : Data D Q) (q : PairState Q)
    (c : Column D 2) (w : List (Column D 2)) (hw : Canonical (c :: w)) :
    G.core q (decodeCols (c :: w) 0) (decodeCols (c :: w) 1) ↔
      (∃ r, G.sharedStep q c r ∧ G.core r (decodeCols w 0) (decodeCols w 1)) ∨
      (∃ r, G.switch q c r ∧ G.prefixMeaning r (decodeCols w 0) (decodeCols w 1)) := by
  constructor
  · rintro ⟨shared, px, py, hx, hy, hg, hl, hr⟩
    cases shared with
    | nil =>
        simp only [List.nil_append] at hx hy
        obtain ⟨z, hp, hm⟩ := (G.marked_nil _ _ _ _).mp hl
        obtain ⟨z', hp', hm'⟩ := (G.marked_nil _ _ _ _).mp hr
        have hpref : G.prefixMeaning (z, z') (decodeCols (c :: w) 0) (decodeCols (c :: w) 1) :=
          ⟨by rwa [hx], by rwa [hy]⟩
        obtain ⟨r, hback, hrest⟩ := (G.prefixMeaning_cons (z, z') c w).mp hpref
        refine Or.inr ⟨r, ⟨?_, (z, z'), hm, hm', hback⟩, hrest⟩
        rwa [← hx, ← hy, head_decode hw, head_decode hw] at hg
    | cons x shared =>
        have hc₀ : c 0 = some x := by
          rw [← head_decode hw, hx]
          rfl
        have hc₁ : c 1 = some x := by
          rw [← head_decode hw, hy]
          rfl
        have hx' : decodeCols w 0 = shared ++ px := by
          rw [← tail_decode hw, hx]
          rfl
        have hy' : decodeCols w 1 = shared ++ py := by
          rw [← tail_decode hw, hy]
          rfl
        obtain ⟨r, hl, hstep⟩ := (G.marked_cons _ _ _ _ _ x).mp hl
        obtain ⟨r', hr, hstep'⟩ := (G.marked_cons _ _ _ _ _ x).mp hr
        refine Or.inl ⟨(r, r'), ⟨⟨x, hc₀, hc₁⟩, ?_⟩, shared, px, py, hx', hy', hg, hl, hr⟩
        simpa only [backward, BackStep, hc₀, hc₁] using And.intro hstep hstep'
  · rintro (⟨r, ⟨⟨x, hc₀, hc₁⟩, hback⟩, shared, px, py, hx, hy, hg, hl, hr⟩ |
      ⟨r, ⟨hg, z, hm, hm', hback⟩, hpref⟩)
    · have hsteps : G.T.step r.1 x q.1 ∧ G.T.step r.2 x q.2 := by
        simpa only [backward, BackStep, hc₀, hc₁] using hback
      refine ⟨x :: shared, px, py, ?_, ?_, hg,
        (G.marked_cons _ _ _ _ _ x).mpr ⟨r.1, hl, hsteps.1⟩,
        (G.marked_cons _ _ _ _ _ x).mpr ⟨r.2, hr, hsteps.2⟩⟩
      · simp only [CanonicalConvolution.decode, List.filterMap_cons, hc₀]
        change x :: decodeCols w 0 = (x :: shared) ++ px
        rw [hx]
        rfl
      · simp only [CanonicalConvolution.decode, List.filterMap_cons, hc₁]
        change x :: decodeCols w 1 = (x :: shared) ++ py
        rw [hy]
        rfl
    · have hwhole := (G.prefixMeaning_cons z c w).mpr ⟨r, hback, hpref⟩
      refine ⟨[], decodeCols (c :: w) 0, decodeCols (c :: w) 1, rfl, rfl, ?_,
        (G.marked_nil _ _ _ _).mpr ⟨z.1, hwhole.1, hm⟩,
        (G.marked_nil _ _ _ _).mpr ⟨z.2, hwhole.2, hm'⟩⟩
      simpa only [head_decode hw] using hg

def meaning (G : Data D Q) (q : State Q) (w : List (Column D 2)) : Prop :=
  if q.1 then G.prefixMeaning q.2 (decodeCols w 0) (decodeCols w 1)
  else G.core q.2 (decodeCols w 0) (decodeCols w 1)

/-- The invariant holds at every phase and state, so it preserves all
endpoint choices and all common suffixes, not one selected representative. -/
theorem acceptFrom_correct (G : Data D Q) (w : List (Column D 2)) (hw : Canonical w)
    (q : State Q) : AcceptFrom G.automaton q w ↔ G.meaning q w := by
  induction w generalizing q with
  | nil =>
      rw [acceptFrom_nil]
      rcases q with ⟨b, q⟩
      cases b
      · exact (G.core_nil q).symm
      · exact (G.prefixMeaning_nil q).symm
  | cons c w ih =>
      have htail : Canonical w := validFrom_mono hw.2.2 (by intros; rfl)
      rw [acceptFrom_cons]
      rcases q with ⟨b, q⟩
      cases b
      · change (∃ r : State Q, G.automaton.step (false, q) c r ∧ AcceptFrom G.automaton r w) ↔
          G.core q (decodeCols (c :: w) 0) (decodeCols (c :: w) 1)
        rw [G.core_cons q c w hw]
        constructor
        · rintro ⟨⟨b, r⟩, hs, hr⟩
          cases b
          · exact Or.inl ⟨r, hs, (ih htail (false, r)).mp hr⟩
          · exact Or.inr ⟨r, hs, (ih htail (true, r)).mp hr⟩
        · rintro (⟨r, hs, hr⟩ | ⟨r, hs, hr⟩)
          · exact ⟨(false, r), hs, (ih htail (false, r)).mpr hr⟩
          · exact ⟨(true, r), hs, (ih htail (true, r)).mpr hr⟩
      · change (∃ r : State Q, G.automaton.step (true, q) c r ∧ AcceptFrom G.automaton r w) ↔
          G.prefixMeaning q (decodeCols (c :: w) 0) (decodeCols (c :: w) 1)
        rw [G.prefixMeaning_cons q c w]
        constructor
        · rintro ⟨⟨b, r⟩, hs, hr⟩
          cases b
          · exact False.elim hs
          · exact ⟨r, hs, (ih htail (true, r)).mp hr⟩
        · rintro ⟨r, hs, hr⟩
          exact ⟨(true, r), hs, (ih htail (true, r)).mpr hr⟩

theorem accepts_correct (G : Data D Q) (w : List (Column D 2)) (hw : Canonical w) :
    G.automaton.Accepts w ↔
      ∃ q, G.finish q ∧ G.core q (decodeCols w 0) (decodeCols w 1) := by
  constructor
  · rintro ⟨⟨b, q⟩, r, ⟨hb, hq⟩, hrun, hr⟩
    change b = false at hb
    subst b
    exact ⟨q, hq, (G.acceptFrom_correct w hw (false, q)).mp ⟨r, hrun, hr⟩⟩
  · rintro ⟨q, hq, hc⟩
    obtain ⟨r, hrun, hr⟩ := (G.acceptFrom_correct w hw (false, q)).mpr hc
    exact ⟨(false, q), r, ⟨rfl, hq⟩, hrun, hr⟩

end Data

def mapInput {A B X : Type*} (T : NSSE.NFA A X) (f : B → A) : NSSE.NFA B X where
  start := T.start
  step q a r := T.step q (f a) r
  accept := T.accept

theorem mapInput_runs {A B X : Type*} (T : NSSE.NFA A X) (f : B → A)
    (w : List B) (q r : X) : (mapInput T f).Runs q w r ↔ T.Runs q (w.map f) r := by
  induction w generalizing q with
  | nil => exact (runs_nil_iff _ _ _).trans (runs_nil_iff _ _ _).symm
  | cons a w ih =>
      constructor
      · intro h
        cases h with
        | cons hs ht => exact .cons hs ((ih _).mp ht)
      · intro h
        cases h with
        | cons hs ht => exact .cons hs ((ih _).mpr ht)

theorem mapInput_accepts {A B X : Type*} (T : NSSE.NFA A X) (f : B → A) (w : List B) :
    (mapInput T f).Accepts w ↔ T.Accepts (w.map f) := by
  simp only [NSSE.NFA.Accepts, mapInput_runs]
  rfl

end NSSE.GuardedBlockRelation
