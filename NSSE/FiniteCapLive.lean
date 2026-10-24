import NSSE.FiniteCapFrontEnd
import NSSE.FiniteBoundedPeriods
import NSSE.LiveShortRoot

/-! # Constructed live inclusion and the complete original cap Boolean

The bounded approximation is R plus the finite union of accepted proper-period
monitors after an anchor. Prefixes ending before the root ends are already in
R. This proves equality with the original anchored-ray approximation K, without
enumerating infinite rays or assuming a regular-language inclusion oracle.
-/

namespace NSSE.FiniteCapLive

open FiniteSOARankDecision FiniteDFAOperations FiniteDFAConcat FiniteCapFrontEnd
open FrozenCapRays LiveShortRoot

variable {α : Type}

/-- Exact finite-monitor description of the bounded anchored-ray cover. -/
theorem boundedCovered_iff (E : CapExpression α) (bound : Nat) (xs : List α) :
    BoundedCovered E bound xs ↔ regularCovered E xs ∨
      ∃ c ∈ E.caps, Language.concat c.left (BoundedPeriodLanguage c.right bound) xs := by
  constructor
  · rintro (hreg | ⟨c, hc, anchor, root, ha, hr, _, hb, hray⟩)
    · exact Or.inl hreg
    · by_cases hreg : regularCovered E xs
      · exact Or.inl hreg
      · have hout : ¬ RegularPart c xs := fun h => hreg ⟨c, hc, h⟩
        obtain ⟨hp, hend, hatake, hfactor⟩ := freeze_ray c xs anchor root hout ha hr hray
        obtain ⟨k, hx⟩ := hray
        have hd : xs.drop anchor.length <+: Language.wordPower root k := by
          simpa using hx.drop anchor.length
        obtain ⟨rest, hrest⟩ := hd
        have hshort : root.length < (xs.drop anchor.length).length := by
          simp only [List.length_drop]
          omega
        have hper := (Language.period_of_prefix_wordPower root (xs.drop anchor.length)
          rest k hp hshort hrest.symm).2
        refine Or.inr ⟨c, hc, xs.take anchor.length, xs.drop anchor.length,
          (List.take_append_drop anchor.length xs).symm, ?_, root.length, hp, hb, hper, ?_⟩
        · rwa [hatake]
        · change c.right (Word.factor xs anchor.length root.length)
          rwa [hfactor]
  · rintro (hreg | ⟨c, hc, anchor, tail, rfl, ha, p, hp, hb, hper, hr⟩)
    · exact Or.inl hreg
    · have hrootlen : (tail.take p).length = p := by
        simp [Nat.min_eq_left hper.1.le]
      obtain ⟨k, rest, hpow⟩ := Language.hasPeriod_prefix_wordPower tail p hp hper
      refine Or.inr ⟨c, hc, anchor, tail.take p, ha, hr, ?_, ?_, k, rest, ?_⟩
      · exact List.length_pos_iff.mp (by rwa [hrootlen])
      · rwa [hrootlen]
      · rw [hpow, List.append_assoc]

def rowIndex (E : Input α) (i : Fin E.denote.caps.length) : Fin E.rows.length :=
  ⟨i.val, by simpa [Input.denote] using i.isLt⟩

def rootPresentation (E : Input α) : RootPresentation E.denote where
  states i := (E.rows.get (rowIndex E i)).right.count
  dfa i := (E.rows.get (rowIndex E i)).right.automaton
  correct := by
    intro i xs
    simp [Input.denote, rowIndex, Component.denote, CapComponent.ofDFA,
      NSSE.DFA.language]

section FiniteAlphabet

variable [Fintype α] [DecidableEq α]

def periodicComponent (alphabet : Enumeration α) (c : Component α) (bound : Nat) : InputDFA α :=
  concat c.left (FiniteBoundedPeriods.bounded alphabet c.right bound)

omit [Fintype α] in
theorem periodicComponent_accepts (alphabet : Enumeration α) (c : Component α) (bound : Nat) (xs : List α) :
    (periodicComponent alphabet c bound).automaton.Accepts xs ↔
      Language.concat c.denote.left (BoundedPeriodLanguage c.denote.right bound) xs := by
  rw [periodicComponent, concat_accepts]
  have he : (FiniteBoundedPeriods.bounded alphabet c.right bound).automaton.language =
      BoundedPeriodLanguage c.denote.right bound := by
    funext w
    exact propext (FiniteBoundedPeriods.bounded_accepts alphabet c.right bound w)
  rw [he]
  rfl

def K (alphabet : Enumeration α) (E : Input α) (bound : Nat) : InputDFA α :=
  union (R E) (unions ((prepared E).rows.map (fun c => periodicComponent alphabet c bound)))

theorem K_accepts (alphabet : Enumeration α) (E : Input α) (bound : Nat) (xs : List α) :
    (K alphabet E bound).automaton.Accepts xs ↔ BoundedCovered (prepared E).denote bound xs := by
  rw [K, union_accepts, R_accepts, boundedCovered_iff]
  apply or_congr Iff.rfl
  simp [periodicComponent_accepts, Input.denote]

def L (E : Input α) : InputDFA α where
  count := (G E).count
  automaton := NonliveBorderRank.liveDFA (G E).automaton
  acceptDecision := inferInstance

theorem L_accepts (E : Input α) (xs : List α) :
    (L E).automaton.Accepts xs ↔ NonliveBorderRank.Live (G E).automaton xs :=
  NonliveBorderRank.liveDFA_accepts_iff (G E).automaton (G_prefixClosed E) xs

def bound (E : Input α) : Nat := (G E).count * rootBound (rootPresentation (prepared E))

def liveDecision (alphabet : Enumeration α) (E : Input α) : Bool := !(included (L E) (K alphabet E (bound E)))

theorem liveDecision_correct (alphabet : Enumeration α) (E : Input α) :
    liveDecision alphabet E = true ↔
      ∃ xs, E.denote.Uncovered xs ∧ NonliveBorderRank.Live (G E).automaton xs := by
  have hb : ∀ b : Bool, ((!b) = true ↔ ¬ b = true) := by decide
  have hi : included (L E) (K alphabet E (bound E)) = true ↔
      ∀ xs, NonliveBorderRank.Live (G E).automaton xs →
        BoundedCovered (prepared E).denote (bound E) xs := by
    rw [included_correct]
    simp only [L_accepts, K_accepts]
  have hl := live_counterexample_iff (G E).automaton (G_prefixClosed E)
    (prepared E).denote (rootPresentation (prepared E)) (prepared_right_nonempty E)
  simp only [Fintype.card_fin] at hl
  rw [liveDecision, hb, hi, bound, ← hl]
  apply exists_congr
  intro xs
  constructor
  · rintro ⟨hlive, hcap⟩
    have hg : (G E).automaton.Accepts xs := by
      obtain ⟨z, hxz, _, hz⟩ := hlive xs.length
      exact G_prefixClosed E hxz hz
    have hroute : routeFree E.denote xs := (G_accepts E xs).mp hg
    refine ⟨?_, hlive⟩
    rintro (hc | hr)
    · exact hcap ((prepared_capCovered E xs).mpr hc)
    · exact hroute hr
  · rintro ⟨huncovered, hlive⟩
    exact ⟨hlive, fun hc => huncovered (Or.inl ((prepared_capCovered E xs).mp hc))⟩

/-- The empty alphabet has just one word; no arbitrary seed is chosen. -/
def nilDecision (E : Input α) : Bool :=
  decide ((G E).automaton.Accepts []) && !(decide ((R E).automaton.Accepts []))

theorem nilDecision_correct (E : Input α) : nilDecision E = true ↔ E.denote.Uncovered [] := by
  have hn : ¬ (toSOA (G E) (prepared E).rows).RootCov [] := by
    rintro ⟨c, _, j, t, _, ht, _⟩
    exact Nat.not_lt_zero t ht
  rw [uncovered_iff]
  simp [nilDecision, hn]

def decideUncovered (alphabet : Enumeration α) (E : Input α) : Bool :=
  if alphabet.values.isEmpty then nilDecision E
  else liveDecision alphabet E || terminalDecision E

/-- Complete cap decision from finite transition tables and the actual alphabet
list. No SAB, supplied rank, language-inclusion or avoidance oracle occurs. -/
theorem decideUncovered_correct (alphabet : Enumeration α) (E : Input α) :
    decideUncovered alphabet E = true ↔ ∃ xs, E.denote.Uncovered xs := by
  cases he : alphabet.values with
  | nil =>
      have hword : ∀ xs : List α, xs = [] := by
        intro xs
        cases xs with
        | nil => rfl
        | cons x xs =>
            have hx := alphabet.complete x
            simp only [he, List.not_mem_nil] at hx
      simp only [decideUncovered, he, List.isEmpty_nil, ↓reduceIte, nilDecision_correct]
      constructor
      · intro h; exact ⟨[], h⟩
      · rintro ⟨xs, h⟩; rwa [hword xs] at h
  | cons seed rest =>
      simp only [decideUncovered, he, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        Bool.or_eq_true, liveDecision_correct, terminalDecision_correct E seed]
      classical
      constructor
      · rintro (⟨xs, h, _⟩ | ⟨xs, h, _⟩) <;> exact ⟨xs, h⟩
      · rintro ⟨xs, h⟩
        by_cases hl : NonliveBorderRank.Live (G E).automaton xs
        · exact Or.inl ⟨xs, h, hl⟩
        · exact Or.inr ⟨xs, h, hl⟩

theorem decideUncovered_false_iff (alphabet : Enumeration α) (E : Input α) :
    decideUncovered alphabet E = false ↔ E.denote.Universal := by
  have hb : ∀ b : Bool, (b = false ↔ ¬ b = true) := by decide
  rw [hb, decideUncovered_correct]
  classical
  simp [CapExpression.Uncovered, CapExpression.Universal]

def universalityDecision (alphabet : Enumeration α) (E : Input α) : Decidable E.denote.Universal :=
  decidable_of_iff (decideUncovered alphabet E = false) (decideUncovered_false_iff alphabet E)

end FiniteAlphabet

end NSSE.FiniteCapLive
