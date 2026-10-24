import NSSE.FiniteCapSAB

/-! # Literal forward cap-automaton semantics and normalization lemmas

The final P-edge TARGET is material. Ordinary acceptance and the P-edge
contribution are defined before any conversion to cap expressions.
The only structural hypotheses used are gap universality and strict cap.
-/

namespace NSSE.ForwardCapAutomaton

open GuardedBlockRelation FiniteSOARankDecision

variable {α : Type}

structure Input (α : Type) where
  count : Nat
  start : Fin count
  step : Fin count → α → Fin count → Prop
  final : Fin count → Prop
  pedge : Fin count → Fin count → Prop
  stepDecision : ∀ q x r, Decidable (step q x r)
  finalDecision : DecidablePred final
  pedgeDecision : ∀ q r, Decidable (pedge q r)

instance (A : Input α) : DecidablePred A.final := A.finalDecision
instance (A : Input α) : ∀ q x r, Decidable (A.step q x r) := A.stepDecision
instance (A : Input α) : ∀ q r, Decidable (A.pedge q r) := A.pedgeDecision

def pathNFA (A : Input α) (q : Fin A.count) (F : Fin A.count → Prop) :
    NSSE.NFA α (Fin A.count) where
  start r := r = q
  step := A.step
  accept := F

def ordinary (A : Input α) : NSSE.NFA α (Fin A.count) := pathNFA A A.start A.final

instance pathStartDecision (A : Input α) (q : Fin A.count) (F : Fin A.count → Prop) :
    DecidablePred (pathNFA A q F).start := fun r => inferInstanceAs (Decidable (r = q))

instance pathAcceptDecision (A : Input α) (q : Fin A.count) (F : Fin A.count → Prop)
    [DecidablePred F] : DecidablePred (pathNFA A q F).accept := fun r => inferInstanceAs (Decidable (F r))

instance pathStepDecision (A : Input α) (q : Fin A.count) (F : Fin A.count → Prop) :
    ∀ r x s, Decidable ((pathNFA A q F).step r x s) := A.stepDecision

theorem path_runs (A : Input α) (s : Fin A.count) (F : Fin A.count → Prop)
    (q r : Fin A.count) (xs : List α) :
    (pathNFA A s F).Runs q xs r ↔ (ordinary A).Runs q xs r := by
  constructor <;> intro h <;> induction h with
  | nil q => exact .nil q
  | cons hs _ ih => exact .cons hs ih

theorem path_accepts (A : Input α) (q : Fin A.count) (F : Fin A.count → Prop)
    (xs : List α) : (pathNFA A q F).Accepts xs ↔
      ∃ r, (ordinary A).Runs q xs r ∧ F r := by
  constructor
  · rintro ⟨s, r, hs, hrun, hr⟩
    have he : s = q := hs
    subst s
    exact ⟨r, (path_runs A q F q r xs).mp hrun, hr⟩
  · rintro ⟨r, hrun, hr⟩
    exact ⟨q, r, rfl, (path_runs A q F q r xs).mpr hrun, hr⟩

theorem ordinary_accepts (A : Input α) (xs : List α) :
    (ordinary A).Accepts xs ↔ AcceptFrom (ordinary A) A.start xs :=
  path_accepts A A.start A.final xs

def GapUniversal (A : Input α) : Prop :=
  ∀ q x r, ¬ A.final q → A.step q x r → A.final r →
    ∀ xs, AcceptFrom (ordinary A) r xs

def StrictCap (A : Input α) : Prop :=
  ∀ q source target xs, xs ≠ [] → (ordinary A).Runs q xs source →
    A.pedge source target → A.final q

/-- Literal P-edge acceptance: the anchor lands at a FINAL target q, the
root path ends at a P-edge source, and the remaining input prefixes a power. -/
def Capped (A : Input α) (xs : List α) : Prop :=
  ∃ anchor tail q source root k,
    xs = anchor ++ tail ∧ (ordinary A).Runs A.start anchor q ∧ A.final q ∧
    (ordinary A).Runs q root source ∧ A.pedge source q ∧
    tail <+: Language.wordPower root k

def Accepts (A : Input α) (xs : List α) : Prop := (ordinary A).Accepts xs ∨ Capped A xs

def Universal (A : Input α) : Prop := ∀ xs, Accepts A xs

def anchorLanguage (A : Input α) (q : Fin A.count) : Language α :=
  fun xs => (ordinary A).Runs A.start xs q

def rootLanguage (A : Input α) (q : Fin A.count) : Language α :=
  fun xs => ∃ source, (ordinary A).Runs q xs source ∧ A.pedge source q

def component (A : Input α) (q : Fin A.count) : CapComponent α :=
  ⟨anchorLanguage A q, rootLanguage A q⟩

theorem capped_iff (A : Input α) (xs : List α) : Capped A xs ↔
    ∃ q, A.final q ∧ Language.concat (anchorLanguage A q) (Language.cap (rootLanguage A q)) xs := by
  constructor
  · rintro ⟨anchor, tail, q, source, root, k, he, ha, hq, hr, hp, rest, hpow⟩
    exact ⟨q, hq, anchor, tail, he, ha, root, k, rest, ⟨source, hr, hp⟩, hpow.symm⟩
  · rintro ⟨q, hq, anchor, tail, he, ha, root, k, rest, ⟨source, hr, hp⟩, hpow⟩
    exact ⟨anchor, tail, q, source, root, k, he, ha, hq, hr, hp, rest, hpow.symm⟩

def PrefixCore (A : Input α) (xs : List α) : Prop :=
  ∀ pref, pref <+: xs → (ordinary A).Accepts pref

def UniversalCore (A : Input α) (xs : List α) : Prop :=
  ∀ tail, (ordinary A).Accepts (xs ++ tail)

/-- From a nonfinal state an accepting run must cross a universal final
state. The proof preserves the actual initial segment of that run. -/
theorem accepting_run_universal (A : Input α) (hgap : GapUniversal A)
    {q r : Fin A.count} {xs : List α} (h : (ordinary A).Runs q xs r)
    (hn : ¬ A.final q) (hf : A.final r) :
    ∀ tail, AcceptFrom (ordinary A) q (xs ++ tail) := by
  induction h with
  | nil q => exact False.elim (hn hf)
  | @cons q s r x xs hs hr ih =>
      intro tail
      apply (acceptFrom_cons (ordinary A) q x (xs ++ tail)).mpr
      refine ⟨s, hs, ?_⟩
      by_cases hsf : A.final s
      · exact hgap q x s hn hs hsf (xs ++ tail)
      · exact ih hsf hf tail

theorem ordinary_iff_cores (A : Input α) (hgap : GapUniversal A) (xs : List α) :
    (ordinary A).Accepts xs ↔ PrefixCore A xs ∨ UniversalCore A xs := by
  classical
  constructor
  · intro hx
    by_cases hk : PrefixCore A xs
    · exact Or.inl hk
    · apply Or.inr
      obtain ⟨pref, hpref, hn⟩ : ∃ pref, pref <+: xs ∧ ¬ (ordinary A).Accepts pref := by
        simpa [PrefixCore] using hk
      obtain ⟨rest, rfl⟩ := hpref
      obtain ⟨r, hrun, hf⟩ := (ordinary_accepts A (pref ++ rest)).mp hx
      obtain ⟨q, hp, hr⟩ := (runs_append_iff (ordinary A) A.start r pref rest).mp hrun
      have hq : ¬ A.final q := fun h => hn ((ordinary_accepts A pref).mpr ⟨q, hp, h⟩)
      intro tail
      obtain ⟨s, hs, hsf⟩ := accepting_run_universal A hgap hr hq hf tail
      apply (ordinary_accepts A _).mpr
      exact ⟨s, by simpa only [List.append_assoc] using hp.append (ordinary A) hs, hsf⟩
  · rintro (hk | hu)
    · exact hk xs (List.prefix_refl xs)
    · simpa using hu []

/-- Every proper prefix of an accepted anchor is ordinarily accepted,
including when the accepted root itself is epsilon. -/
theorem proper_anchor_prefix (A : Input α) (hstrict : StrictCap A)
    (q : Fin A.count) (anchor pref : List α)
    (ha : anchorLanguage A q anchor) (hb : ∃ root, rootLanguage A q root)
    (hp : pref <+: anchor) (hne : pref ≠ anchor) : (ordinary A).Accepts pref := by
  obtain ⟨rest, he⟩ := hp
  obtain ⟨root, source, hr, hpe⟩ := hb
  have han : (ordinary A).Runs A.start (pref ++ rest) q := by rwa [he]
  obtain ⟨s, hs, hsq⟩ := (runs_append_iff (ordinary A) A.start q pref rest).mp han
  have hrest : rest ≠ [] := by
    intro hz
    apply hne
    simpa only [hz, List.append_nil] using he
  have hfinal : A.final s := hstrict s source q (rest ++ root)
    (fun hz => hrest (List.append_eq_nil_iff.mp hz).1) (hsq.append (ordinary A) hr) hpe
  exact (ordinary_accepts A pref).mpr ⟨s, hs, hfinal⟩

/-- Adding outer prefix closure to one cap term creates only words already
ordinarily accepted; the final-target hypothesis is retained explicitly. -/
theorem prefix_component_accepts (A : Input α) (hstrict : StrictCap A)
    (q : Fin A.count) (hq : A.final q) (xs : List α)
    (h : capComponentCovers (component A q) xs) : Accepts A xs := by
  obtain ⟨outer, anchor, tail, he, ha, root, k, rest, hr, hpow⟩ := h
  have hx : xs <+: anchor ++ Language.wordPower root k := by
    refine ⟨outer ++ rest, ?_⟩
    rw [hpow]
    simpa only [List.append_assoc] using congrArg (fun w => w ++ rest) he
  by_cases hshort : xs.length < anchor.length
  · apply Or.inl
    apply proper_anchor_prefix A hstrict q anchor xs ha ⟨root, hr⟩
    · exact (List.isPrefix_append_of_length hshort.le).mp hx
    · intro heq; subst xs; exact Nat.lt_irrefl _ hshort
  · have hale : anchor.length ≤ xs.length := by omega
    have hatake : xs.take anchor.length = anchor := by
      simpa using FrozenCapRays.take_eq_of_prefix hx hale
    have htail : xs.drop anchor.length <+: Language.wordPower root k := by
      simpa using hx.drop anchor.length
    apply Or.inr
    apply (capped_iff A xs).mpr
    refine ⟨q, hq, anchor, xs.drop anchor.length, ?_, ha, root, k, ?_, hr, ?_⟩
    · calc
        xs = xs.take anchor.length ++ xs.drop anchor.length := (List.take_append_drop anchor.length xs).symm
        _ = anchor ++ xs.drop anchor.length := by rw [hatake]
    · exact htail.choose
    · exact htail.choose_spec.symm

end NSSE.ForwardCapAutomaton
