import NSSE.ForwardCapNormalization

/-! # The literal forward automaton table satisfies the needed restrictions

This is journal Table 3 (preprint Table 1), over any finite path alphabet.
The finite Boolean tables are the syntactic-support data used by that table;
this module does not replace their derivation from constraints by an oracle.
It proves the structural facts independently of their logical interpretation.
-/

namespace NSSE.ForwardTableAutomaton

open GuardedBlockRelation

inductive Side | left | right
  deriving DecidableEq

abbrev Token (n : Nat) := Option (Fin n)
abbrev State (n : Nat) := Option (Token n × Token n)

/-- `upper u i v` denotes the table for u <= i(v), and `lower v i u`
the table for i(u) <= v. bot/top already include supported inequalities. -/
structure Tables (n d : Nat) where
  queryLeft : Fin n
  queryRight : Fin n
  upper : Fin n → Fin d → Fin n → Bool
  lower : Fin n → Fin d → Fin n → Bool
  bot : Fin n → Bool
  top : Fin n → Bool
  le : Fin n → Fin n → Bool

variable {n d : Nat}

def upperMove (D : Tables n d) : Token n → Fin d → Token n → Prop
  | some u, i, some v => D.upper u i v = true
  | _, _, _ => False

def lowerMove (D : Tables n d) : Token n → Fin d → Token n → Prop
  | some v, i, some u => D.lower v i u = true
  | _, _, _ => False

def escape (D : Tables n d) (u v : Token n) : Prop :=
  (∃ x, u = some x ∧ D.bot x = true) ∨
  (∃ y, v = some y ∧ D.top y = true) ∨
  (∃ x y, u = some x ∧ v = some y ∧ D.le x y = true)

def final (D : Tables n d) (side : Side) : State n → Prop
  | none => True
  | some (u,v) => escape D u v ∨ match side with
    | .left => ∃ i r, upperMove D u i r
    | .right => ∃ i r, lowerMove D v i r

def step (D : Tables n d) : State n → Fin d → State n → Prop
  | none, _, none => True
  | none, _, some _ => False
  | some (u,v), _, none => escape D u v
  | some (u,v), i, some (u',v') =>
      (upperMove D u i u' ∧ v' = none) ∨
      (u' = none ∧ lowerMove D v i v') ∨
      (upperMove D u i u' ∧ lowerMove D v i v')

def pedge : Side → State n → State n → Prop
  | .left, some (some u,_), some (some _,some u') => u' = u
  | .right, some (_,some v), some (some v',some _) => v' = v
  | _, _, _ => False

instance upperDecision (D : Tables n d) (u : Token n) (i : Fin d) (v : Token n) :
    Decidable (upperMove D u i v) := by cases u <;> cases v <;> dsimp [upperMove] <;> infer_instance
instance lowerDecision (D : Tables n d) (u : Token n) (i : Fin d) (v : Token n) :
    Decidable (lowerMove D u i v) := by cases u <;> cases v <;> dsimp [lowerMove] <;> infer_instance
instance escapeDecision (D : Tables n d) (u v : Token n) : Decidable (escape D u v) := by
  unfold escape
  infer_instance
instance finalDecision (D : Tables n d) (side : Side) : DecidablePred (final D side) := by
  intro q
  cases q with
  | none => exact isTrue trivial
  | some q => cases q; cases side <;> dsimp [final] <;> infer_instance
instance stepDecision (D : Tables n d) : ∀ q i r, Decidable (step D q i r) := by
  intro q i r
  cases q <;> cases r <;> dsimp [step] <;> infer_instance
instance pedgeDecision (side : Side) : ∀ q r : State n, Decidable (pedge side q r) := by
  intro q r
  cases side <;> cases q with
  | none => cases r <;> dsimp [pedge] <;> infer_instance
  | some q =>
      rcases q with ⟨u,v⟩
      cases r with
      | none => cases u <;> cases v <;> dsimp [pedge] <;> infer_instance
      | some r =>
          rcases r with ⟨u',v'⟩
          cases u <;> cases v <;> cases u' <;> cases v' <;> dsimp [pedge] <;> infer_instance

def rawNFA (D : Tables n d) (side : Side) : NSSE.NFA (Fin d) (State n) where
  start q := q = some (some D.queryLeft, some D.queryRight)
  step := step D
  accept := final D side

def tracked (side : Side) : State n → Token n
  | none => none
  | some (u,v) => match side with | .left => u | .right => v

theorem upper_source (D : Tables n d) {u v : Token n} {i : Fin d}
    (h : upperMove D u i v) : u ≠ none := by
  cases u with
  | none => cases v <;> exact False.elim h
  | some u => exact Option.noConfusion

theorem lower_source (D : Tables n d) {u v : Token n} {i : Fin d}
    (h : lowerMove D u i v) : u ≠ none := by
  cases u with
  | none => cases v <;> exact False.elim h
  | some u => exact Option.noConfusion

/-- A letter edge whose target still carries the tracked variable must
have used the corresponding descend rule; its source is final. -/
theorem tracked_step (D : Tables n d) (side : Side) (q r : State n) (i : Fin d)
    (hs : step D q i r) (hr : tracked side r ≠ none) :
    tracked side q ≠ none ∧ final D side q := by
  cases q with
  | none => cases r <;> simp_all [step, tracked]
  | some q =>
      rcases q with ⟨u,v⟩
      cases r with
      | none => exact False.elim (hr rfl)
      | some r =>
          rcases r with ⟨u',v'⟩
          cases side with
          | left =>
              rcases hs with ⟨hu, rfl⟩ | ⟨rfl, hv⟩ | ⟨hu, hv⟩
              · exact ⟨upper_source D hu, Or.inr ⟨i, u', hu⟩⟩
              · exact False.elim (hr rfl)
              · exact ⟨upper_source D hu, Or.inr ⟨i, u', hu⟩⟩
          | right =>
              rcases hs with ⟨hu, rfl⟩ | ⟨rfl, hv⟩ | ⟨hu, hv⟩
              · exact False.elim (hr rfl)
              · exact ⟨lower_source D hv, Or.inr ⟨i, v', hv⟩⟩
              · exact ⟨lower_source D hv, Or.inr ⟨i, v', hv⟩⟩

theorem all_runs (D : Tables n d) (side : Side) (xs : List (Fin d)) :
    (rawNFA D side).Runs none xs none := by
  induction xs with
  | nil => exact .nil _
  | cons x xs ih => exact .cons (show (rawNFA D side).step none x none from trivial) ih

theorem escape_universal (D : Tables n d) (side : Side) (u v : Token n)
    (h : escape D u v) (xs : List (Fin d)) : AcceptFrom (rawNFA D side) (some (u,v)) xs := by
  cases xs with
  | nil => exact (acceptFrom_nil _ _).mpr (Or.inl h)
  | cons x xs => exact ⟨none,
      .cons (show (rawNFA D side).step (some (u,v)) x none from h) (all_runs D side xs), trivial⟩

theorem missing_tracked_universal (D : Tables n d) (side : Side) (q : State n)
    (ht : tracked side q = none) (hf : final D side q) (xs : List (Fin d)) :
    AcceptFrom (rawNFA D side) q xs := by
  cases q with
  | none => exact ⟨none, all_runs D side xs, trivial⟩
  | some q =>
      rcases q with ⟨u,v⟩
      apply escape_universal D side u v _ xs
      cases side with
      | left =>
          rcases hf with he | ⟨i, r, hr⟩
          · exact he
          · exact False.elim (upper_source D hr ht)
      | right =>
          rcases hf with he | ⟨i, r, hr⟩
          · exact he
          · exact False.elim (lower_source D hr ht)

theorem raw_gap (D : Tables n d) (side : Side) (q r : State n) (i : Fin d)
    (hn : ¬ final D side q) (hs : step D q i r) (hf : final D side r)
    (xs : List (Fin d)) : AcceptFrom (rawNFA D side) r xs := by
  have ht : tracked side r = none := by
    by_contra hne
    exact hn (tracked_step D side q r i hs hne).2
  exact missing_tracked_universal D side r ht hf xs

theorem tracked_run (D : Tables n d) (side : Side) {q r : State n} {xs : List (Fin d)}
    (h : (rawNFA D side).Runs q xs r) (hr : tracked side r ≠ none) :
    tracked side q ≠ none ∧ (xs ≠ [] → final D side q) := by
  induction h with
  | nil q => exact ⟨hr, fun h => False.elim (h rfl)⟩
  | @cons q s r i xs hs hrest ih =>
      have hq := tracked_step D side q s i hs (ih hr).1
      exact ⟨hq.1, fun _ => hq.2⟩

theorem pedge_tracked (side : Side) (q r : State n) (h : pedge side q r) : tracked side q ≠ none := by
  cases side <;> cases q with
  | none => cases r <;> exact False.elim h
  | some q =>
      rcases q with ⟨u,v⟩
      cases r with
      | none => cases u <;> cases v <;> exact False.elim h
      | some r =>
          rcases r with ⟨u',v'⟩
          cases u <;> cases v <;> cases u' <;> cases v' <;>
            simp_all [pedge, tracked]

/-- Explicit finite state equivalence: underscore tokens and all are
ordinary option constructors, not a choice of an ordering of a finite set. -/
def stateEquiv (n : Nat) : State n ≃ Fin ((n + 1) * (n + 1) + 1) :=
  (Equiv.optionCongr ((Equiv.prodCongr (finSuccEquiv n).symm (finSuccEquiv n).symm).trans
    finProdFinEquiv)).trans (finSuccEquiv _).symm

def compile (D : Tables n d) (side : Side) : ForwardCapAutomaton.Input (Fin d) where
  count := (n + 1) * (n + 1) + 1
  start := stateEquiv n (some (some D.queryLeft, some D.queryRight))
  step q i r := step D ((stateEquiv n).symm q) i ((stateEquiv n).symm r)
  final q := final D side ((stateEquiv n).symm q)
  pedge q r := pedge side ((stateEquiv n).symm q) ((stateEquiv n).symm r)
  stepDecision := fun _ _ _ => inferInstance
  finalDecision := fun _ => inferInstance
  pedgeDecision := fun _ _ => inferInstance

theorem decode_run (D : Tables n d) (side : Side) {q r} {xs : List (Fin d)}
    (h : (ForwardCapAutomaton.ordinary (compile D side)).Runs q xs r) :
    (rawNFA D side).Runs ((stateEquiv n).symm q) xs ((stateEquiv n).symm r) := by
  induction h with
  | nil q => exact .nil _
  | cons hs _ ih => exact .cons hs ih

theorem encode_run (D : Tables n d) (side : Side) {q r : State n} {xs : List (Fin d)}
    (h : (rawNFA D side).Runs q xs r) :
    (ForwardCapAutomaton.ordinary (compile D side)).Runs (stateEquiv n q) xs (stateEquiv n r) := by
  induction h with
  | nil q => exact .nil _
  | cons hs _ ih =>
      refine .cons ?_ ih
      change step D ((stateEquiv n).symm (stateEquiv n _)) _ ((stateEquiv n).symm (stateEquiv n _))
      simpa only [Equiv.symm_apply_apply] using hs

theorem compile_gap (D : Tables n d) (side : Side) : ForwardCapAutomaton.GapUniversal (compile D side) := by
  intro q i r hn hs hf xs
  obtain ⟨s, hrun, hfinal⟩ := raw_gap D side ((stateEquiv n).symm q) ((stateEquiv n).symm r) i hn hs hf xs
  refine ⟨stateEquiv n s, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using encode_run D side hrun
  · change final D side ((stateEquiv n).symm (stateEquiv n s))
    simpa only [Equiv.symm_apply_apply] using hfinal

theorem compile_strict (D : Tables n d) (side : Side) : ForwardCapAutomaton.StrictCap (compile D side) := by
  intro q source target xs hne hrun hp
  exact (tracked_run D side (decode_run D side hrun)
    (pedge_tracked side ((stateEquiv n).symm source) ((stateEquiv n).symm target) hp)).2 hne

/-- Both concrete table-built side automata enter the complete cap decision
without a caller-supplied gap/strict-cap certificate. -/
def decideUniversal (D : Tables n d) (side : Side) : Bool :=
  ForwardCapNormalization.decideUniversal (finEnumeration d) (compile D side)

theorem decideUniversal_correct (D : Tables n d) (side : Side) :
    decideUniversal D side = true ↔ ForwardCapAutomaton.Universal (compile D side) :=
  ForwardCapNormalization.decideUniversal_correct (finEnumeration d) (compile D side)
    (compile_gap D side) (compile_strict D side)

end NSSE.ForwardTableAutomaton
