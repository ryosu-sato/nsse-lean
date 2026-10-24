import NSSE.FiniteDFAConcat
import NSSE.CertificateSOA
import NSSE.FrozenCapRays

/-! # The original finite cap input constructs G, R, and the terminal decision

Only components with an empty root LANGUAGE are removed; roots accepting
epsilon survive. The constructed regular languages are proved to be the
original right-ideal complement and the exact prefix/split cover. The terminal
Boolean consequently describes uncovered words of the ORIGINAL expression.
-/

namespace NSSE.FiniteCapFrontEnd

open FiniteSOARankDecision FiniteDFAOperations FiniteDFAConcat

variable {α : Type}

structure Input (α : Type) where
  rows : List (Component α)
  routes : List (InputDFA α)

def Input.denote (E : Input α) : CapExpression α where
  caps := E.rows.map Component.denote
  routes := E.routes.map (fun A => A.automaton.language)

@[simp] theorem capCovered_denote (E : Input α) (xs : List α) :
    capCovered E.denote xs ↔ ∃ c ∈ E.rows, capComponentCovers c.denote xs := by
  simp [capCovered, Input.denote]

@[simp] theorem routeCovered_denote (E : Input α) (xs : List α) :
    routeCovered E.denote xs ↔
      ∃ A ∈ E.routes, Language.concat A.automaton.language Language.univ xs := by
  simp [routeCovered, Input.denote]

theorem right_nonempty_of_cover (c : CapComponent α) (xs : List α)
    (h : capComponentCovers c xs) : ∃ root, c.right root := by
  obtain ⟨_, _, _, _, _, root, _, _, hr, _⟩ := h
  exact ⟨root, hr⟩

def rightIdeal (A : InputDFA α) : InputDFA α := concat A (constant true)

@[simp] theorem rightIdeal_accepts (A : InputDFA α) (xs : List α) :
    (rightIdeal A).automaton.Accepts xs ↔
      Language.concat A.automaton.language Language.univ xs := by
  rw [rightIdeal, concat_accepts]
  simp [Language.concat, NSSE.DFA.language, Language.univ]

def G (E : Input α) : InputDFA α := complement (unions (E.routes.map rightIdeal))

theorem G_accepts (E : Input α) (xs : List α) :
    (G E).automaton.Accepts xs ↔ routeFree E.denote xs := by
  simp [G, routeFree, routeCovered_denote]

theorem G_prefixClosed (E : Input α) : NonliveBorderRank.PrefixClosed (G E).automaton := by
  intro x y hxy hy
  rw [G_accepts] at hy ⊢
  intro hx
  obtain ⟨tail, rfl⟩ := hxy
  obtain ⟨A, hA, pref, rest, he, ha, _⟩ := hx
  apply hy
  refine ⟨A, hA, pref, rest ++ tail, ?_, ha, trivial⟩
  rw [he, List.append_assoc]

theorem concat_prefix_iff_split (c : CapComponent α) (xs : List α) :
    Language.concat c.left (Language.prefixClosure c.right) xs ↔ SplitRoute c xs := by
  constructor
  · rintro ⟨pref, tail, rfl, ha, hb⟩
    exact ⟨pref.length, by simp, by simpa using ha, by simpa using hb⟩
  · rintro ⟨j, _, ha, hb⟩
    exact ⟨xs.take j, xs.drop j, (List.take_append_drop j xs).symm, ha, hb⟩

section FiniteAlphabet

variable [Fintype α] [DecidableEq α]

def prepared (E : Input α) : Input α :=
  { E with rows := E.rows.filter (fun c => nonempty c.right) }

theorem prepared_capCovered (E : Input α) (xs : List α) :
    capCovered (prepared E).denote xs ↔ capCovered E.denote xs := by
  rw [capCovered_denote, capCovered_denote]
  constructor
  · rintro ⟨c, hc, hcov⟩
    exact ⟨c, (List.mem_filter.mp hc).1, hcov⟩
  · rintro ⟨c, hc, hcov⟩
    refine ⟨c, List.mem_filter.mpr ⟨hc, ?_⟩, hcov⟩
    exact (nonempty_correct c.right).mpr (right_nonempty_of_cover c.denote xs hcov)

theorem prepared_covers (E : Input α) (xs : List α) :
    (prepared E).denote.Covers xs ↔ E.denote.Covers xs := by
  unfold CapExpression.Covers
  rw [prepared_capCovered]
  rfl

theorem prepared_uncovered (E : Input α) (xs : List α) :
    (prepared E).denote.Uncovered xs ↔ E.denote.Uncovered xs := not_congr (prepared_covers E xs)

theorem prepared_right_nonempty (E : Input α) :
    ∀ c ∈ (prepared E).denote.caps, ∃ root, c.right root := by
  intro c hc
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hc
  exact (nonempty_correct row.right).mp (List.mem_filter.mp hrow).2

theorem prepared_retains_epsilon (E : Input α) (c : Component α)
    (hc : c ∈ E.rows) (he : c.right.automaton.Accepts []) : c ∈ (prepared E).rows := by
  exact List.mem_filter.mpr ⟨hc, (nonempty_correct c.right).mpr ⟨[], he⟩⟩

def componentRegular (c : Component α) : InputDFA α :=
  union (prefixClosure c.left) (concat c.left (prefixClosure c.right))

theorem componentRegular_accepts (c : Component α) (xs : List α) :
    (componentRegular c).automaton.Accepts xs ↔ PrefixRoute c.denote xs ∨ SplitRoute c.denote xs := by
  rw [componentRegular, union_accepts, prefixClosure_accepts, concat_accepts]
  have he : (prefixClosure c.right).automaton.language = Language.prefixClosure c.denote.right := by
    funext w
    exact propext (prefixClosure_accepts c.right w)
  rw [he]
  exact or_congr Iff.rfl (concat_prefix_iff_split c.denote xs)

def R (E : Input α) : InputDFA α := unions ((prepared E).rows.map componentRegular)

theorem R_accepts (E : Input α) (xs : List α) :
    (R E).automaton.Accepts xs ↔ FrozenCapRays.regularCovered (prepared E).denote xs := by
  simp [R, FrozenCapRays.regularCovered, FrozenCapRays.RegularPart, Input.denote, componentRegular_accepts]

theorem R_le_capCovered (E : Input α) (xs : List α) (h : (R E).automaton.Accepts xs) :
    capCovered E.denote xs :=
  (prepared_capCovered E xs).mp (FrozenCapRays.regularCovered_le_capCovered
    (prepared E).denote (prepared_right_nonempty E) xs ((R_accepts E xs).mp h))

/-- The exact original-language bridge, with no input-side nonemptiness premise. -/
theorem uncovered_iff (E : Input α) (xs : List α) :
    E.denote.Uncovered xs ↔ (G E).automaton.Accepts xs ∧ ¬ (R E).automaton.Accepts xs ∧
      ¬ (toSOA (G E) (prepared E).rows).RootCov xs := by
  rw [← prepared_uncovered E xs,
    uncovered_iff_toSOA_avoider (prepared E).denote (prepared_right_nonempty E) xs,
    G_accepts, R_accepts]
  change ((routeFree E.denote xs ∧
    ∀ c ∈ (prepared E).denote.caps, ¬ PrefixRoute c xs ∧ ¬ SplitRoute c xs) ∧
    ¬ (toSOA (G E) (prepared E).rows).RootCov xs) ↔
    (routeFree E.denote xs ∧
      ¬ (∃ c ∈ (prepared E).denote.caps, PrefixRoute c xs ∨ SplitRoute c xs) ∧
      ¬ (toSOA (G E) (prepared E).rows).RootCov xs)
  simp only [not_exists, not_and, not_or]
  tauto

def terminalDecision (E : Input α) : Bool :=
  FiniteCapTerminal.decide (G E) (R E) (prepared E).rows

/-- The computed terminal branch decides ORIGINAL uncovered, nonlive words.
G, R, row preprocessing, and the rank promise are all constructed internally. -/
theorem terminalDecision_correct (E : Input α) (seed : α) :
    terminalDecision E = true ↔
      ∃ xs, E.denote.Uncovered xs ∧ ¬ NonliveBorderRank.Live (G E).automaton xs := by
  rw [terminalDecision, FiniteCapTerminal.decide_correct _ _ _ seed (G_prefixClosed E)]
  apply exists_congr
  intro xs
  rw [uncovered_iff]
  tauto

end FiniteAlphabet

end NSSE.FiniteCapFrontEnd
