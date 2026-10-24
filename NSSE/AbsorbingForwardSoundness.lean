import NSSE.AbsorbingSubtypeSafety
import NSSE.ConstraintForwardTables

/-! # All forward acceptance is sound for original arbitrary-tree constraints

Ordinary and P-edge runs are interpreted under every original satisfying
valuation. No satisfiability, recognition, or support-completeness oracle
is used. This proves the positive implication for the actual Boolean;
the converse and satisfiability algorithm are separate remaining tasks.
-/

namespace NSSE.AbsorbingForwardSoundness

open AbsorbingSubtypeTrees AbsorbingSubtypeSafety RegularSubtypeTrees
open SubtypeConstraints ForwardTableAutomaton ConstraintForwardTables

theorem prefix_root_self {α : Type*} (root tail : List α) (k : Nat)
    (hp : tail <+: Language.wordPower root k) : tail <+: root ++ tail := by
  have h₁ : tail <+: Language.wordPower root (k + 1) := hp.trans (by
    rw [Language.wordPower_succ_right]
    exact List.prefix_append _ _)
  have h₂ : root ++ tail <+: Language.wordPower root (k + 1) := by
    rw [Language.wordPower_succ]
    exact (List.prefix_append_right_inj root).mpr hp
  exact List.prefix_of_prefix_length_le h₁ h₂ (by simp)

variable {n d : Nat}

def leftToken (ρ : Fin n → Tree d) : Token n → Tree d
  | none => ⊤
  | some x => ρ x

def rightToken (ρ : Fin n → Tree d) : Token n → Tree d
  | none => ⊥
  | some x => ρ x

def StateSafe (ρ : Fin n → Tree d) (side : Side) : State n → List (Fin d) → Prop
  | none, _ => True
  | some (u,v), path => Safe side (leftToken ρ u) (rightToken ρ v) path

section Valuation

variable (Q : Query n d) (ρ : Fin n → Tree d)
variable (hρ : Satisfies (constructor d) Q.constraints ρ)
include hρ

theorem upper_project {u v : Token n} {i : Fin d}
    (h : upperMove (tables Q) u i v) :
    project (leftToken ρ u) [i] ≤ leftToken ρ v := by
  cases u with
  | none => cases v <;> exact False.elim h
  | some u =>
      cases v with
      | none => exact False.elim h
      | some v =>
          obtain ⟨children, hc, hb⟩ := computed_upper_sound (constructor d) Q ρ hρ h
          simpa only [constructor, project_node, project_nil, hc] using project_mono hb [i]

theorem lower_project {u v : Token n} {i : Fin d}
    (h : lowerMove (tables Q) u i v) :
    rightToken ρ v ≤ project (rightToken ρ u) [i] := by
  cases u with
  | none => cases v <;> exact False.elim h
  | some u =>
      cases v with
      | none => exact False.elim h
      | some v =>
          obtain ⟨children, hc, hb⟩ := computed_lower_sound (constructor d) Q ρ hρ h
          simpa only [constructor, project_node, project_nil, hc] using project_mono hb [i]

theorem upper_not_top {u v : Token n} {i : Fin d}
    (h : upperMove (tables Q) u i v) : leftToken ρ u ≠ ⊤ := by
  cases u with
  | none => cases v <;> exact False.elim h
  | some u =>
      cases v with
      | none => exact False.elim h
      | some v =>
          obtain ⟨children, _, hb⟩ := computed_upper_sound (constructor d) Q ρ hρ h
          intro he
          change ρ u = ⊤ at he
          rw [he] at hb
          have hh := hb []
          exact (by decide : ¬ (2 : Label) ≤ 1) hh

theorem lower_not_bot {u v : Token n} {i : Fin d}
    (h : lowerMove (tables Q) u i v) : rightToken ρ u ≠ ⊥ := by
  cases u with
  | none => cases v <;> exact False.elim h
  | some u =>
      cases v with
      | none => exact False.elim h
      | some v =>
          obtain ⟨children, _, hb⟩ := computed_lower_sound (constructor d) Q ρ hρ h
          intro he
          change ρ u = ⊥ at he
          rw [he] at hb
          have hh := hb []
          exact (by decide : ¬ (1 : Label) ≤ 0) hh

theorem escape_order {u v : Token n} (h : escape (tables Q) u v) :
    leftToken ρ u ≤ rightToken ρ v := by
  rcases h with ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩ | ⟨x, y, rfl, rfl, hxy⟩
  · change ρ x ≤ _
    rw [computed_bot_sound (constructor d) Q ρ hρ hx]
    exact bot_le
  · change _ ≤ ρ y
    rw [computed_top_sound (constructor d) Q ρ hρ hy]
    exact le_top
  · exact computed_le_sound (constructor d) Q ρ hρ hxy

theorem pair_step_bounds {u v u' v' : Token n} {i : Fin d}
    (h : step (tables Q) (some (u,v)) i (some (u',v'))) :
    project (leftToken ρ u) [i] ≤ leftToken ρ u' ∧
    rightToken ρ v' ≤ project (rightToken ρ v) [i] := by
  rcases h with ⟨hu, rfl⟩ | ⟨rfl, hv⟩ | ⟨hu, hv⟩
  · exact ⟨upper_project Q ρ hρ hu, bot_le⟩
  · exact ⟨le_top, lower_project Q ρ hρ hv⟩
  · exact ⟨upper_project Q ρ hρ hu, lower_project Q ρ hρ hv⟩

theorem final_safe (side : Side) {q : State n} (h : final (tables Q) side q) :
    StateSafe ρ side q [] := by
  cases q with
  | none => trivial
  | some q =>
      rcases q with ⟨u,v⟩
      change Safe side (leftToken ρ u) (rightToken ρ v) []
      rcases h with he | hf
      · exact below_safe (escape_order Q ρ hρ he) side []
      · apply (safe_iff_project side _ _ []).mpr
        simp only [project_nil]
        cases side with
        | left =>
            obtain ⟨i,r,hr⟩ := hf
            exact fun ht => False.elim (upper_not_top Q ρ hρ hr ht)
        | right =>
            obtain ⟨i,r,hr⟩ := hf
            exact fun hb => False.elim (lower_not_bot Q ρ hρ hr hb)

theorem step_lift (side : Side) {q r : State n} {i : Fin d}
    (h : step (tables Q) q i r) (tail : List (Fin d))
    (ht : StateSafe ρ side r tail) : StateSafe ρ side q (i :: tail) := by
  cases q with
  | none => trivial
  | some q =>
      rcases q with ⟨u,v⟩
      cases r with
      | none => exact below_safe (escape_order Q ρ hρ h) side (i :: tail)
      | some r =>
          rcases r with ⟨u',v'⟩
          obtain ⟨hu,hv⟩ := pair_step_bounds Q ρ hρ h
          exact (safe_append side _ _ [i] tail).mpr (safe_mono side hu hv ht)

theorem run_lift (side : Side) {q r : State n} {path : List (Fin d)}
    (h : (rawNFA (tables Q) side).Runs q path r) (tail : List (Fin d))
    (ht : StateSafe ρ side r tail) : StateSafe ρ side q (path ++ tail) := by
  induction h with
  | nil q => exact ht
  | cons hs _ ih => exact step_lift Q ρ hρ side hs _ (ih ht)

omit hρ in
theorem run_all_end (side : Side) {q r : State n} {path : List (Fin d)}
    (h : (rawNFA (tables Q) side).Runs q path r) : q = none → r = none := by
  induction h with
  | nil q => exact id
  | @cons q s r i path hs _ ih =>
      intro he
      subst q
      apply ih
      cases s with
      | none => rfl
      | some s => exact False.elim hs

theorem pair_run_bounds (side : Side) {q r : State n} {path : List (Fin d)}
    (h : (rawNFA (tables Q) side).Runs q path r) :
    ∀ u v u' v', q = some (u,v) → r = some (u',v') →
      project (leftToken ρ u) path ≤ leftToken ρ u' ∧
      rightToken ρ v' ≤ project (rightToken ρ v) path := by
  induction h with
  | nil q =>
      rintro u v u' v' rfl he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      simp only [project_nil]
      exact ⟨le_rfl, le_rfl⟩
  | @cons q s r i path hs hrest ih =>
      rintro u v u' v' rfl rfl
      cases s with
      | none => exact False.elim (Option.noConfusion (run_all_end Q side hrest rfl))
      | some s =>
          rcases s with ⟨a,b⟩
          obtain ⟨ha,hb⟩ := pair_step_bounds Q ρ hρ hs
          obtain ⟨hu,hv⟩ := ih a b u' v' rfl rfl
          rw [project_cons (leftToken ρ u) i path, project_cons (rightToken ρ v) i path]
          exact ⟨(project_mono ha path).trans hu, hv.trans (project_mono hb path)⟩

theorem raw_accepts_safe (side : Side) (path : List (Fin d))
    (h : (rawNFA (tables Q) side).Accepts path) :
    Safe side (ρ Q.left) (ρ Q.right) path := by
  rcases h with ⟨q,r,hq,hr,hf⟩
  have he : q = some (some Q.left, some Q.right) := hq
  rw [he] at hr
  have hs := run_lift Q ρ hρ side hr [] (final_safe Q ρ hρ side hf)
  simpa only [List.append_nil, StateSafe, leftToken, rightToken] using hs

theorem pedge_safe (side : Side) {q r : State n} (root tail : List (Fin d)) (k : Nat)
    (hr : (rawNFA (tables Q) side).Runs q root r) (hp : pedge side r q)
    (ht : tail <+: Language.wordPower root k) : StateSafe ρ side q tail := by
  have hword := prefix_root_self root tail k ht
  cases q with
  | none => trivial
  | some q =>
      rcases q with ⟨u,v⟩
      cases r with
      | none => cases side <;> exact False.elim hp
      | some r =>
          rcases r with ⟨u',v'⟩
          have hb := pair_run_bounds Q ρ hρ side hr u v u' v' rfl rfl
          cases side with
          | left =>
              cases u <;> cases v <;> cases u' <;> simp only [pedge] at hp
              subst_vars
              exact periodic_left _ _ root tail hb.1 hword
          | right =>
              cases u <;> cases v <;> cases v' <;> simp only [pedge] at hp
              subst_vars
              exact periodic_right _ _ root tail hb.2 hword

end Valuation

theorem ordinary_sound (Q : Query n d) (side : Side) (path : List (Fin d))
    (h : (ForwardCapAutomaton.ordinary (automaton Q side)).Accepts path) :
    QuerySafe Q side path := by
  intro ρ hρ
  obtain ⟨r,hr,hf⟩ := (ForwardCapAutomaton.ordinary_accepts _ path).mp h
  apply raw_accepts_safe Q ρ hρ side path
  refine ⟨some (some Q.left, some Q.right), (stateEquiv n).symm r, rfl, ?_, hf⟩
  simpa only [automaton, compile, Equiv.symm_apply_apply] using decode_run (tables Q) side hr

theorem capped_sound (Q : Query n d) (side : Side) (path : List (Fin d))
    (h : ForwardCapAutomaton.Capped (automaton Q side) path) : QuerySafe Q side path := by
  intro ρ hρ
  obtain ⟨anchor,tail,q,r,root,k,rfl,ha,_hf,hr,hp,ht⟩ := h
  have hs := pedge_safe Q ρ hρ side root tail k (decode_run (tables Q) side hr) hp ht
  have hl := run_lift Q ρ hρ side (decode_run (tables Q) side ha) tail hs
  simpa only [automaton, compile, Equiv.symm_apply_apply, StateSafe, leftToken, rightToken,
    tables] using hl

/-- Every ordinary or P-edge accepted word has the ORIGINAL semantic safety. -/
theorem accepts_sound (Q : Query n d) (side : Side) (path : List (Fin d))
    (h : ForwardCapAutomaton.Accepts (automaton Q side) path) : QuerySafe Q side path := by
  rcases h with h | h
  · exact ordinary_sound Q side path h
  · exact capped_sound Q side path h

theorem universal_entails (Q : Query n d)
    (hl : ForwardCapAutomaton.Universal (automaton Q .left))
    (hr : ForwardCapAutomaton.Universal (automaton Q .right)) : Entails (constructor d) Q := by
  apply (entails_iff_both_safe Q).mpr
  exact ⟨fun path => accepts_sound Q .left path (hl path),
    fun path => accepts_sound Q .right path (hr path)⟩

/-- Positive answers of the actual constraint-derived Boolean are genuine
arbitrary-tree entailments. The negative direction is not claimed here. -/
theorem decideBothSides_sound (Q : Query n d) (h : decideBothSides Q = true) :
    Entails (constructor d) Q := by
  obtain ⟨hl,hr⟩ := (decideBothSides_correct Q).mp h
  exact universal_entails Q hl hr

theorem accepts_regular_sound (Q : Query n d) (s : Side) (w : List (Fin d))
    (h : ForwardCapAutomaton.Accepts (automaton Q s) w) : RegularQuerySafe Q s w :=
  fun ρ _ hρ => accepts_sound Q s w h ρ hρ

theorem decideBothSides_regular_sound (Q : Query n d) (h : decideBothSides Q = true) :
    RegularEntails Q := fun ρ _ hρ => decideBothSides_sound Q h ρ hρ

end NSSE.AbsorbingForwardSoundness
