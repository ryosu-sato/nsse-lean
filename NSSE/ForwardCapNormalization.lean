import NSSE.ForwardCapAutomaton

/-! # Executable normalization of a forward cap automaton

The regular prefix core K and universal-continuation core U are computed,
not provided as semantic oracles. Anchor/root DFAs come from the ORIGINAL
ordinary paths. The resulting finite cap expression has exactly the literal
automaton language under gap universality and strict cap.
-/

namespace NSSE.ForwardCapNormalization

open FiniteSOARankDecision FiniteDFAOperations ForwardCapAutomaton

variable {α : Type}

def pathDFA (A : ForwardCapAutomaton.Input α) (q : Fin A.count)
    (F : Fin A.count → Prop) [DecidablePred F] : InputDFA α := determinize (pathNFA A q F)

theorem pathDFA_accepts (A : ForwardCapAutomaton.Input α) (q : Fin A.count)
    (F : Fin A.count → Prop) [DecidablePred F] (xs : List α) :
    (pathDFA A q F).automaton.Accepts xs ↔ ∃ r, (ordinary A).Runs q xs r ∧ F r := by
  rw [pathDFA, determinize_accepts, path_accepts]

def ordinaryDFA (A : ForwardCapAutomaton.Input α) : InputDFA α := pathDFA A A.start A.final

theorem ordinaryDFA_accepts (A : ForwardCapAutomaton.Input α) (xs : List α) :
    (ordinaryDFA A).automaton.Accepts xs ↔ (ordinary A).Accepts xs := by
  rw [ordinaryDFA, pathDFA, determinize_accepts]
  rfl

def anchorDFA (A : ForwardCapAutomaton.Input α) (q : Fin A.count) : InputDFA α :=
  pathDFA A A.start (fun r => r = q)

theorem anchorDFA_accepts (A : ForwardCapAutomaton.Input α) (q : Fin A.count) (xs : List α) :
    (anchorDFA A q).automaton.Accepts xs ↔ anchorLanguage A q xs := by
  simp only [anchorDFA, pathDFA_accepts, exists_eq_right, anchorLanguage]

def rootDFA (A : ForwardCapAutomaton.Input α) (q : Fin A.count) : InputDFA α :=
  pathDFA A q (fun r => A.pedge r q)

theorem rootDFA_accepts (A : ForwardCapAutomaton.Input α) (q : Fin A.count) (xs : List α) :
    (rootDFA A q).automaton.Accepts xs ↔ rootLanguage A q xs := by
  rw [rootDFA, pathDFA_accepts]
  rfl

def row (A : ForwardCapAutomaton.Input α) (q : Fin A.count) : Component α :=
  ⟨anchorDFA A q, rootDFA A q⟩

theorem row_denote (A : ForwardCapAutomaton.Input α) (q : Fin A.count) :
    (row A q).denote = component A q := by
  change CapComponent.mk _ _ = CapComponent.mk _ _
  congr 1
  · funext xs; exact propext (anchorDFA_accepts A q xs)
  · funext xs; exact propext (rootDFA_accepts A q xs)

def prefixCoreDFA (D : InputDFA α) : InputDFA α :=
  complement (FiniteCapFrontEnd.rightIdeal (complement D))

theorem prefixCoreDFA_accepts (D : InputDFA α) (xs : List α) :
    (prefixCoreDFA D).automaton.Accepts xs ↔ ∀ pref, pref <+: xs → D.automaton.Accepts pref := by
  rw [prefixCoreDFA, complement_accepts, FiniteCapFrontEnd.rightIdeal_accepts]
  classical
  constructor
  · intro hn pref hp
    by_contra hbad
    obtain ⟨tail, he⟩ := hp
    exact hn ⟨pref, tail, he.symm, (complement_accepts D pref).mpr hbad, trivial⟩
  · intro h
    rintro ⟨pref, tail, he, hn, _⟩
    exact (complement_accepts D pref).mp hn (h pref ⟨tail, he.symm⟩)

def epsilon : InputDFA α where
  count := 2
  automaton := { start := 0, step := fun _ _ => 1, accept := fun q => q = 0 }
  acceptDecision := fun _ => inferInstance

theorem epsilon_runFrom_one (xs : List α) :
    (epsilon (α := α)).automaton.runFrom (1 : Fin 2) xs = (1 : Fin 2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

theorem epsilon_accepts (xs : List α) : (epsilon (α := α)).automaton.Accepts xs ↔ xs = [] := by
  cases xs with
  | nil => simp [epsilon, NSSE.DFA.Accepts, NSSE.DFA.run]
  | cons x xs =>
      change ((epsilon (α := α)).automaton.runFrom (1 : Fin 2) xs = (0 : Fin 2)) ↔ x :: xs = []
      rw [epsilon_runFrom_one]
      simp

theorem cap_epsilon_iff (xs : List α) :
    Language.cap (epsilon (α := α)).automaton.language xs ↔ xs = [] := by
  simp only [Language.cap, NSSE.DFA.language, epsilon_accepts, exists_eq_left]
  simp [Language.wordPower]

section FiniteAlphabet

variable [Fintype α] [DecidableEq α]

def universalCoreDFA (D : InputDFA α) : InputDFA α where
  count := D.count
  automaton := { D.automaton with accept := fun q =>
    (complement D).automaton.executableProductive.productive q = false }
  acceptDecision := fun _ => inferInstance

theorem universalCoreDFA_accepts (D : InputDFA α) (xs : List α) :
    (universalCoreDFA D).automaton.Accepts xs ↔ ∀ tail, D.automaton.Accepts (xs ++ tail) := by
  change (complement D).automaton.executableProductive.productive (D.automaton.run xs) = false ↔ _
  have hb : ∀ b : Bool, (b = false ↔ ¬ b = true) := by decide
  rw [hb, (complement D).automaton.executableProductive.productive_iff]
  classical
  change (¬ ∃ tail, ¬ D.automaton.accept (D.automaton.runFrom (D.automaton.run xs) tail)) ↔ _
  simp only [not_exists, not_not, NSSE.DFA.Accepts, NSSE.DFA.run_append]

def coreRow (A : ForwardCapAutomaton.Input α) : Component α :=
  ⟨prefixCoreDFA (ordinaryDFA A), epsilon⟩

omit [Fintype α] [DecidableEq α] in
theorem coreRow_covers (A : ForwardCapAutomaton.Input α) (xs : List α) :
    capComponentCovers (coreRow A).denote xs ↔ PrefixCore A xs := by
  change (∃ tail, Language.concat (prefixCoreDFA (ordinaryDFA A)).automaton.language
    (Language.cap (epsilon (α := α)).automaton.language) (xs ++ tail)) ↔ _
  constructor
  · rintro ⟨tail, anchor, rest, he, ha, hr⟩ pref hp
    have hrest : rest = [] := (cap_epsilon_iff rest).mp hr
    subst rest
    have hxa : xs <+: anchor := ⟨tail, by simpa only [List.append_nil] using he⟩
    exact (ordinaryDFA_accepts A pref).mp
      ((prefixCoreDFA_accepts (ordinaryDFA A) anchor).mp ha pref (hp.trans hxa))
  · intro h
    refine ⟨[], xs, [], rfl, ?_, (cap_epsilon_iff []).mpr rfl⟩
    apply (prefixCoreDFA_accepts (ordinaryDFA A) xs).mpr
    intro pref hp
    exact (ordinaryDFA_accepts A pref).mpr (h pref hp)

theorem universalCore_rightIdeal (A : ForwardCapAutomaton.Input α) (xs : List α) :
    Language.concat (universalCoreDFA (ordinaryDFA A)).automaton.language Language.univ xs ↔
      UniversalCore A xs := by
  constructor
  · rintro ⟨pref, tail, rfl, h, _⟩ rest
    have hh := (universalCoreDFA_accepts (ordinaryDFA A) pref).mp h (tail ++ rest)
    exact (ordinaryDFA_accepts A _).mp (by simpa only [List.append_assoc] using hh)
  · intro h
    refine ⟨xs, [], by simp, ?_, trivial⟩
    apply (universalCoreDFA_accepts (ordinaryDFA A) xs).mpr
    intro tail
    exact (ordinaryDFA_accepts A _).mpr (h tail)

def normalize (A : ForwardCapAutomaton.Input α) : FiniteCapFrontEnd.Input α where
  rows := coreRow A :: ((List.finRange A.count).filter (fun q => decide (A.final q))).map (row A)
  routes := [universalCoreDFA (ordinaryDFA A)]

theorem normalize_shape (A : ForwardCapAutomaton.Input α) (xs : List α) :
    (normalize A).denote.Covers xs ↔
      (PrefixCore A xs ∨ ∃ q, A.final q ∧ capComponentCovers (component A q) xs) ∨ UniversalCore A xs := by
  simp only [CapExpression.Covers, FiniteCapFrontEnd.capCovered_denote,
    FiniteCapFrontEnd.routeCovered_denote, normalize, List.mem_cons, List.mem_map,
    List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq, exists_eq_left,
    List.mem_singleton, List.not_mem_nil, or_false, coreRow_covers, row_denote]
  constructor
  · rintro (⟨c, hc, hw⟩ | hu)
    · rcases hc with rfl | ⟨q, hq, rfl⟩
      · exact Or.inl (Or.inl ((coreRow_covers A xs).mp hw))
      · exact Or.inl (Or.inr ⟨q, hq, by rwa [row_denote] at hw⟩)
    · exact Or.inr ((universalCore_rightIdeal A xs).mp hu)
  · rintro ((hk | ⟨q, hq, hw⟩) | hu)
    · exact Or.inl ⟨coreRow A, Or.inl rfl, (coreRow_covers A xs).mpr hk⟩
    · exact Or.inl ⟨row A q, Or.inr ⟨q, hq, rfl⟩, by rwa [row_denote]⟩
    · exact Or.inr ((universalCore_rightIdeal A xs).mpr hu)

/-- Exact normalization of literal cap-automaton acceptance. Neither
completeness of the ordinary NFA nor shuffle is required. -/
theorem normalize_correct (A : ForwardCapAutomaton.Input α)
    (hgap : GapUniversal A) (hstrict : StrictCap A) (xs : List α) :
    (normalize A).denote.Covers xs ↔ Accepts A xs := by
  rw [normalize_shape]
  constructor
  · rintro ((hk | ⟨q, hq, hw⟩) | hu)
    · exact Or.inl ((ordinary_iff_cores A hgap xs).mpr (Or.inl hk))
    · exact prefix_component_accepts A hstrict q hq xs hw
    · exact Or.inl ((ordinary_iff_cores A hgap xs).mpr (Or.inr hu))
  · rintro (ho | hc)
    · rcases (ordinary_iff_cores A hgap xs).mp ho with hk | hu
      · exact Or.inl (Or.inl hk)
      · exact Or.inr hu
    · obtain ⟨q, hq, hw⟩ := (capped_iff A xs).mp hc
      exact Or.inl (Or.inr ⟨q, hq, [], by simpa only [List.append_nil] using hw⟩)

theorem normalize_universal (A : ForwardCapAutomaton.Input α)
    (hgap : GapUniversal A) (hstrict : StrictCap A) :
    (normalize A).denote.Universal ↔ Universal A :=
  forall_congr' (normalize_correct A hgap hstrict)

def decideUniversal (alphabet : Enumeration α) (A : ForwardCapAutomaton.Input α) : Bool :=
  !(FiniteCapLive.decideUncovered alphabet (normalize A))

theorem decideUniversal_correct (alphabet : Enumeration α) (A : ForwardCapAutomaton.Input α)
    (hgap : GapUniversal A) (hstrict : StrictCap A) :
    decideUniversal alphabet A = true ↔ Universal A := by
  have hb : ∀ b : Bool, ((!b) = true ↔ b = false) := by decide
  rw [decideUniversal, hb, FiniteCapLive.decideUncovered_false_iff,
    normalize_universal A hgap hstrict]

end FiniteAlphabet

end NSSE.ForwardCapNormalization
