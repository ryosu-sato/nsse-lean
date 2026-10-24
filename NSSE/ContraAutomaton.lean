import NSSE.ForwardTableAutomaton
import NSSE.ContraSupport
import Mathlib.Algebra.BigOperators.Fin

/-! # The deterministic polarity-bit set-token automaton (contravariant NSSE, stage S3)

notes_v1362 §3 (with the set-token correction of v1363 §5), v1365 §1.

States: `ALL` (`none`) and triples `(S_x, S_y, σ)` with token sets `S_x, S_y ⊆ Vars`
(as Boolean masks `Fin n → Bool`) and a polarity bit `σ` (`false = +`, `true = −`). The
initial state is `({x}, {y}, +)`. All data are read from the S2 tables
`ContraSupport.Tables` (support `le`, child bounds `upper`/`lower`, `bot`, `top`), which
are computed from the constraint syntax by `ContraSupport.tables`.

* x-tokens are upper bounds at `+` and lower bounds at `−`; y-tokens the other way round.
  A move of an x-token therefore uses `upper` at `+` and `lower` at `−` (`xMove`), a move of
  a y-token uses `lower` at `+` and `upper` at `−` (`yMove`); the polarity of the child is
  `σ xor POL i`. (The child kind flip at a contravariant position is already inside the
  S2 tables, `SupportedUpper/Lower` use `SupportAt`.)
* Escape (final; every letter goes to `ALL`): at `+` some `u ∈ S_x` with `bot u`, some
  `v ∈ S_y` with `top v`, or `u ≤s v`; at `−`: `top u`, `bot v`, or `v ≤s u`
  (`xBot`, `yTop`, `LeS`).
* Finals: escapes, and on the right side a move of some y-token, on the left side a move of
  some x-token (`TrackedMove`).
* P-edges `(source, target)` (the eight rows of the v1362 §3 table, which depend only on the
  two states and on the root parity `σ xor σ'`): see `PEdge`.

The automaton is compiled into the covariant `ForwardCapAutomaton.Input` interface, and the
two structural facts of v1365 §1 are proved for it: gap universality (Lemma N1,
`compile_gap`) and strict cap (Lemma N2, `compile_strict`). Hence Part II
(`ForwardCapNormalization.decideUniversal`) decides universality of each side
(`decideUniversal_correct`), with no caller-supplied certificate.

The semantic meaning (soundness) is in `NSSE.ContraSoundness`.
-/

namespace NSSE.ContraAutomaton

open GuardedBlockRelation
open SubtypeConstraints (Constraints Query)
open ContraTrees ContraSupport
open ForwardTableAutomaton (Side)

variable {n d : Nat}

/-- A token set, as a Boolean mask. -/
abbrev TokenSet (n : Nat) := Fin n → Bool

/-- A proper state `(S_x, S_y, σ)`. -/
abbrev Triple (n : Nat) := TokenSet n × TokenSet n × Bool

/-- `none` is the absorbing accepting state `ALL`. -/
abbrev State (n : Nat) := Option (Triple n)

section Tables

variable (D : Tables n d)

/-- `u ≤s v` at `+`, `v ≤s u` at `−`. -/
def LeS (σ : Bool) (u v : Fin n) : Bool := if σ then D.le v u else D.le u v

/-- Move of an x-token: upper child bound at `+`, lower child bound at `−`. -/
def xMove (σ : Bool) (u : Fin n) (i : Fin d) (z : Fin n) : Bool :=
  if σ then D.lower u i z else D.upper u i z

/-- Move of a y-token: lower child bound at `+`, upper child bound at `−`. -/
def yMove (σ : Bool) (v : Fin n) (i : Fin d) (z : Fin n) : Bool :=
  if σ then D.upper v i z else D.lower v i z

/-- The x-side escape: `bot u` at `+`, `top u` at `−`. -/
def xBot (σ : Bool) (u : Fin n) : Bool := if σ then D.top u else D.bot u

/-- The y-side escape: `top v` at `+`, `bot v` at `−`. -/
def yTop (σ : Bool) (v : Fin n) : Bool := if σ then D.bot v else D.top v

def Escape (q : Triple n) : Prop :=
  (∃ u, q.1 u = true ∧ xBot D q.2.2 u = true) ∨
  (∃ v, q.2.1 v = true ∧ yTop D q.2.2 v = true) ∨
  (∃ u v, q.1 u = true ∧ q.2.1 v = true ∧ LeS D q.2.2 u v = true)

/-- The tracked token set: `S_x` on the left side, `S_y` on the right side. -/
def tracked : Side → Triple n → TokenSet n
  | .left, q => q.1
  | .right, q => q.2.1

/-- The tracked move used by the tracked side at polarity `σ`. -/
def trackedMove : Side → Bool → Fin n → Fin d → Fin n → Bool
  | .left, σ => xMove D σ
  | .right, σ => yMove D σ

/-- A child move of some tracked token (left: `x(p)` is not a real ⊤ in plabels;
right: `y(p)` is not a real ⊥ in plabels). -/
def TrackedMove (side : Side) (q : Triple n) : Prop :=
  ∃ v i z, tracked side q v = true ∧ trackedMove D side q.2.2 v i z = true

def Final (side : Side) : State n → Prop
  | none => True
  | some q => Escape D q ∨ TrackedMove D side q

/-- The transition of a non-escape triple. -/
def next (POL : Polarity d) (q : Triple n) (i : Fin d) : Triple n :=
  (fun z => decide (∃ u, q.1 u = true ∧ xMove D q.2.2 u i z = true),
   fun z => decide (∃ v, q.2.1 v = true ∧ yMove D q.2.2 v i z = true),
   xor q.2.2 (POL i))

instance escapeDecision (q : Triple n) : Decidable (Escape D q) := by
  unfold Escape; infer_instance

instance trackedMoveDecision (side : Side) (q : Triple n) : Decidable (TrackedMove D side q) := by
  unfold TrackedMove; infer_instance

instance finalDecision (side : Side) : DecidablePred (Final D side) := by
  intro q
  cases q with
  | none => exact isTrue trivial
  | some q => dsimp [Final]; infer_instance

/-- The deterministic transition function. -/
def delta (POL : Polarity d) : State n → Fin d → State n
  | none, _ => none
  | some q, i => if Escape D q then none else some (next D POL q i)

/-- The deterministic run. -/
def run (POL : Polarity d) : State n → List (Fin d) → State n
  | q, [] => q
  | q, i :: w => run POL (delta D POL q i) w

/-- The eight-row P-edge table of v1362 §3 for a source `(S_x', S_y', σ')` (the state after
the root) and a target `(S_x, S_y, σ)` (the final anchor state). The root parity is
`σ xor σ'`. -/
def PEdge (side : Side) : State n → State n → Prop
  | some s, some q =>
      match side with
      | .right =>
          if xor q.2.2 s.2.2 then
            ∃ v' l, s.2.1 v' = true ∧ q.2.1 l = true ∧ LeS D s.2.2 l v' = true
          else
            ∃ u v', q.1 u = true ∧ s.2.1 v' = true ∧ LeS D q.2.2 u v' = true
      | .left =>
          if xor q.2.2 s.2.2 then
            ∃ u u', q.1 u = true ∧ s.1 u' = true ∧ LeS D s.2.2 u' u = true
          else
            ∃ u' l, s.1 u' = true ∧ q.2.1 l = true ∧ LeS D q.2.2 u' l = true
  | _, _ => False

instance pedgeDecision (side : Side) : ∀ s q : State n, Decidable (PEdge D side s q) := by
  intro s q
  cases s with
  | none => cases q <;> exact isFalse id
  | some s =>
      cases q with
      | none => exact isFalse id
      | some q => cases side <;> dsimp [PEdge] <;> infer_instance

/-- The initial state `({x}, {y}, +)`. -/
def start (x y : Fin n) : State n := some (fun u => decide (u = x), fun v => decide (v = y), false)

def rawNFA (POL : Polarity d) (side : Side) (x y : Fin n) : NSSE.NFA (Fin d) (State n) where
  start q := q = start x y
  step q i r := r = delta D POL q i
  accept := Final D side

end Tables

/-! ## Structural lemmas -/

section Structure

variable (D : Tables n d) (POL : Polarity d)

@[simp] theorem delta_none (i : Fin d) : delta D POL none i = none := rfl

theorem delta_escape {q : Triple n} (h : Escape D q) (i : Fin d) : delta D POL (some q) i = none := by
  simp [delta, h]

theorem delta_proper {q : Triple n} (h : ¬ Escape D q) (i : Fin d) :
    delta D POL (some q) i = some (next D POL q i) := by
  simp [delta, h]

@[simp] theorem run_nil (q : State n) : run D POL q [] = q := rfl
@[simp] theorem run_cons (q : State n) (i : Fin d) (w : List (Fin d)) :
    run D POL q (i :: w) = run D POL (delta D POL q i) w := rfl

theorem run_append (q : State n) (v w : List (Fin d)) :
    run D POL q (v ++ w) = run D POL (run D POL q v) w := by
  induction v generalizing q with
  | nil => rfl
  | cons i v ih => exact ih _

@[simp] theorem run_all (w : List (Fin d)) : run D POL (none : State n) w = none := by
  induction w with
  | nil => rfl
  | cons i w ih => exact ih

theorem runs_iff (side : Side) (x y : Fin n) (q r : State n) (w : List (Fin d)) :
    (rawNFA D POL side x y).Runs q w r ↔ r = run D POL q w := by
  constructor
  · intro h
    induction h with
    | nil q => rfl
    | cons hs _ ih => rw [ih, run_cons, ← hs]
  · intro h
    subst h
    induction w generalizing q with
    | nil => exact .nil _
    | cons i w ih => exact .cons rfl (ih _)

theorem accepts_iff (side : Side) (x y : Fin n) (w : List (Fin d)) :
    (rawNFA D POL side x y).Accepts w ↔ Final D side (run D POL (start x y) w) := by
  constructor
  · rintro ⟨q, r, hq, hr, hf⟩
    have hq' : q = start x y := hq
    subst hq'
    rwa [(runs_iff D POL side x y _ _ w).mp hr] at hf
  · intro h
    exact ⟨start x y, _, rfl, (runs_iff D POL side x y _ _ w).mpr rfl, h⟩

/-- Along a proper (non-`ALL`) run the polarity bit is the polarity of the word. -/
theorem run_sigma {q r : Triple n} {w : List (Fin d)} (h : run D POL (some q) w = some r) :
    r.2.2 = xor q.2.2 (pathPol POL w) := by
  induction w generalizing q with
  | nil =>
      simp only [run_nil, Option.some.injEq] at h
      subst h; simp
  | cons i w ih =>
      rw [run_cons] at h
      by_cases he : Escape D q
      · rw [delta_escape D POL he, run_all] at h; exact Option.noConfusion h
      · rw [delta_proper D POL he] at h
        rw [ih h, pathPol_cons]
        simp only [next, Bool.xor_assoc]

theorem start_sigma {x y : Fin n} {w : List (Fin d)} {r : Triple n}
    (h : run D POL (start x y) w = some r) : r.2.2 = pathPol POL w := by
  simpa [start] using run_sigma D POL h

/-- (v1365 (M1)) a non-final triple has an empty tracked set after every letter. -/
theorem tracked_next_empty (side : Side) {q : Triple n} (hn : ¬ TrackedMove D side q) (i : Fin d)
    (z : Fin n) : tracked side (next D POL q i) z = false := by
  cases side with
  | left =>
      simp only [tracked, next, decide_eq_false_iff_not]
      rintro ⟨u, hu, hm⟩
      exact hn ⟨u, i, z, hu, hm⟩
  | right =>
      simp only [tracked, next, decide_eq_false_iff_not]
      rintro ⟨v, hv, hm⟩
      exact hn ⟨v, i, z, hv, hm⟩

theorem not_trackedMove_of_empty (side : Side) {q : Triple n} (h : ∀ z, tracked side q z = false) :
    ¬ TrackedMove D side q := by
  rintro ⟨v, i, z, hv, _⟩
  rw [h v] at hv
  exact Bool.false_ne_true hv

/-- A nonempty tracked set after a letter comes from a tracked move (so the source is final). -/
theorem trackedMove_of_next (side : Side) {q : Triple n} {i : Fin d} {z : Fin n}
    (h : tracked side (next D POL q i) z = true) : TrackedMove D side q := by
  by_contra hn
  rw [tracked_next_empty D POL side hn i z] at h
  exact Bool.false_ne_true h

theorem escape_universal (side : Side) (x y : Fin n) {q : Triple n} (h : Escape D q)
    (w : List (Fin d)) : AcceptFrom (rawNFA D POL side x y) (some q) w := by
  refine ⟨run D POL (some q) w, (runs_iff D POL side x y _ _ w).mpr rfl, ?_⟩
  cases w with
  | nil => exact Or.inl h
  | cons i w => rw [run_cons, delta_escape D POL h, run_all]; trivial

/-- Raw form of v1365 Lemma N1 (gap universality). -/
theorem raw_gap (side : Side) (x y : Fin n) (q r : State n) (i : Fin d)
    (hn : ¬ Final D side q) (hs : r = delta D POL q i) (hf : Final D side r) (w : List (Fin d)) :
    AcceptFrom (rawNFA D POL side x y) r w := by
  cases q with
  | none => exact False.elim (hn trivial)
  | some q =>
      have he : ¬ Escape D q := fun h => hn (Or.inl h)
      have hm : ¬ TrackedMove D side q := fun h => hn (Or.inr h)
      rw [delta_proper D POL he] at hs
      subst hs
      rcases hf with hf | hf
      · exact escape_universal D POL side x y hf w
      · exact False.elim (not_trackedMove_of_empty D side (tracked_next_empty D POL side hm i) hf)

def TrackedNonempty (side : Side) : State n → Prop
  | none => False
  | some q => ∃ z, tracked side q z = true

theorem tracked_step (side : Side) (q : State n) (i : Fin d)
    (h : TrackedNonempty side (delta D POL q i)) : TrackedNonempty side q ∧ Final D side q := by
  cases q with
  | none => exact False.elim h
  | some q =>
      by_cases he : Escape D q
      · rw [delta_escape D POL he] at h; exact False.elim h
      · rw [delta_proper D POL he] at h
        obtain ⟨z, hz⟩ := h
        obtain ⟨v, j, z', hv, hm⟩ := trackedMove_of_next D POL side hz
        exact ⟨⟨v, hv⟩, Or.inr ⟨v, j, z', hv, hm⟩⟩

theorem tracked_run (side : Side) (q : State n) (w : List (Fin d))
    (h : TrackedNonempty side (run D POL q w)) :
    TrackedNonempty side q ∧ (w ≠ [] → Final D side q) := by
  induction w generalizing q with
  | nil => exact ⟨h, fun h => False.elim (h rfl)⟩
  | cons i w ih =>
      have h1 := ih _ h
      have h2 := tracked_step D POL side q i h1.1
      exact ⟨h2.1, fun _ => h2.2⟩

/-- (v1365 (M2)) every P-edge source has a nonempty tracked set. -/
theorem pedge_tracked (side : Side) (s q : State n) (h : PEdge D side s q) : TrackedNonempty side s := by
  cases s with
  | none => cases q <;> exact False.elim h
  | some s =>
      cases q with
      | none => exact False.elim h
      | some q =>
          cases side with
          | right =>
              simp only [PEdge] at h
              split at h
              · obtain ⟨v', _, hv', _⟩ := h; exact ⟨v', hv'⟩
              · obtain ⟨_, v', _, hv', _⟩ := h; exact ⟨v', hv'⟩
          | left =>
              simp only [PEdge] at h
              split at h
              · obtain ⟨_, u', _, hu', _⟩ := h; exact ⟨u', hu'⟩
              · obtain ⟨u', _, hu', _⟩ := h; exact ⟨u', hu'⟩

end Structure

/-! ## Compilation into the covariant cap-automaton interface (Part II input) -/

/-- Explicit computable state numbering. -/
def maskEquiv (n : Nat) : TokenSet n ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

def stateCount (n : Nat) : Nat := 2 ^ n * (2 ^ n * 2) + 1

def stateEquiv (n : Nat) : State n ≃ Fin (stateCount n) :=
  (Equiv.optionCongr ((Equiv.prodCongr (maskEquiv n)
      ((Equiv.prodCongr (maskEquiv n) finTwoEquiv.symm).trans finProdFinEquiv)).trans
    finProdFinEquiv)).trans (finSuccEquiv _).symm

section Compile

variable (D : Tables n d) (POL : Polarity d)

def compile (side : Side) (x y : Fin n) : ForwardCapAutomaton.Input (Fin d) where
  count := stateCount n
  start := stateEquiv n (start x y)
  step q i r := (stateEquiv n).symm r = delta D POL ((stateEquiv n).symm q) i
  final q := Final D side ((stateEquiv n).symm q)
  pedge q r := PEdge D side ((stateEquiv n).symm q) ((stateEquiv n).symm r)
  stepDecision := fun _ _ _ => inferInstance
  finalDecision := fun _ => inferInstance
  pedgeDecision := fun _ _ => inferInstance

theorem decode_run (side : Side) (x y : Fin n) {q r} {w : List (Fin d)}
    (h : (ForwardCapAutomaton.ordinary (compile D POL side x y)).Runs q w r) :
    (rawNFA D POL side x y).Runs ((stateEquiv n).symm q) w ((stateEquiv n).symm r) := by
  induction h with
  | nil q => exact .nil _
  | cons hs _ ih => exact .cons hs ih

theorem encode_run (side : Side) (x y : Fin n) {q r : State n} {w : List (Fin d)}
    (h : (rawNFA D POL side x y).Runs q w r) :
    (ForwardCapAutomaton.ordinary (compile D POL side x y)).Runs (stateEquiv n q) w
      (stateEquiv n r) := by
  induction h with
  | nil q => exact .nil _
  | cons hs _ ih =>
      refine .cons ?_ ih
      change (stateEquiv n).symm (stateEquiv n _) = delta D POL ((stateEquiv n).symm (stateEquiv n _)) _
      simpa only [Equiv.symm_apply_apply] using hs

theorem compile_runs_iff (side : Side) (x y : Fin n) (q r : Fin (stateCount n)) (w : List (Fin d)) :
    (ForwardCapAutomaton.ordinary (compile D POL side x y)).Runs q w r ↔
      (stateEquiv n).symm r = run D POL ((stateEquiv n).symm q) w := by
  constructor
  · intro h
    exact (runs_iff D POL side x y _ _ w).mp (decode_run D POL side x y h)
  · intro h
    have := encode_run D POL side x y ((runs_iff D POL side x y _ _ w).mpr h)
    simpa only [Equiv.apply_symm_apply] using this

/-- v1365 Lemma N1 (gap universality) for the compiled automaton. -/
theorem compile_gap (side : Side) (x y : Fin n) :
    ForwardCapAutomaton.GapUniversal (compile D POL side x y) := by
  intro q i r hn hs hf w
  obtain ⟨s, hrun, hfinal⟩ :=
    raw_gap D POL side x y ((stateEquiv n).symm q) ((stateEquiv n).symm r) i hn hs hf w
  refine ⟨stateEquiv n s, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using encode_run D POL side x y hrun
  · change Final D side ((stateEquiv n).symm (stateEquiv n s))
    simpa only [Equiv.symm_apply_apply] using hfinal

/-- v1365 Lemma N2 (strict cap) for the compiled automaton. -/
theorem compile_strict (side : Side) (x y : Fin n) :
    ForwardCapAutomaton.StrictCap (compile D POL side x y) := by
  intro q source target w hne hrun hp
  have hr := (compile_runs_iff D POL side x y q source w).mp hrun
  have ht := pedge_tracked D side _ _ hp
  rw [hr] at ht
  exact (tracked_run D POL side _ w ht).2 hne

/-- Part II decides universality of each side, with no external certificate. -/
def decideUniversal (side : Side) (x y : Fin n) : Bool :=
  ForwardCapNormalization.decideUniversal (finEnumeration d) (compile D POL side x y)

theorem decideUniversal_correct (side : Side) (x y : Fin n) :
    decideUniversal D POL side x y = true ↔ ForwardCapAutomaton.Universal (compile D POL side x y) :=
  ForwardCapNormalization.decideUniversal_correct (finEnumeration d) (compile D POL side x y)
    (compile_gap D POL side x y) (compile_strict D POL side x y)

end Compile

/-! ## The automaton of a constraint query -/

/-- The side automaton of a query, computed from the constraint syntax by the S2 tables. -/
def automaton (POL : Polarity d) (Q : Query n d) (side : Side) : ForwardCapAutomaton.Input (Fin d) :=
  compile (tables POL Q.constraints) POL side Q.left Q.right

theorem automaton_gap (POL : Polarity d) (Q : Query n d) (side : Side) :
    ForwardCapAutomaton.GapUniversal (automaton POL Q side) :=
  compile_gap _ POL side _ _

theorem automaton_strict (POL : Polarity d) (Q : Query n d) (side : Side) :
    ForwardCapAutomaton.StrictCap (automaton POL Q side) :=
  compile_strict _ POL side _ _

/-- Both sides universal, decided by Part II. -/
def decideBothSides (POL : Polarity d) (Q : Query n d) : Bool :=
  decideUniversal (tables POL Q.constraints) POL .left Q.left Q.right &&
    decideUniversal (tables POL Q.constraints) POL .right Q.left Q.right

theorem decideBothSides_correct (POL : Polarity d) (Q : Query n d) : decideBothSides POL Q = true ↔
    ForwardCapAutomaton.Universal (automaton POL Q .left) ∧
    ForwardCapAutomaton.Universal (automaton POL Q .right) := by
  simp only [decideBothSides, Bool.and_eq_true, decideUniversal_correct]
  rfl

end NSSE.ContraAutomaton
