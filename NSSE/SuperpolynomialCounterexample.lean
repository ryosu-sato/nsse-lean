import NSSE.Cap

/-!
# The modular counterexample family from Proposition 3.2

This module begins with the exact word-equation calculation that drives the
construction.  It is kept separate from the later automata-size estimates.
-/

namespace NSSE

inductive CounterexampleLetter where
  | marker
  | one
  | zero
  | hub
  | guard
  | stop
  deriving DecidableEq, Repr

namespace SuperpolynomialCounterexample

open CounterexampleLetter

def ones (n : Nat) : Word CounterexampleLetter :=
  List.replicate n one

theorem ones_add (a b : Nat) :
    ones (a + b) = ones a ++ ones b := by
  induction a with
  | zero => simp [ones]
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega]
      change one :: ones (a + b) =
        (one :: ones a) ++ ones b
      rw [ih]
      simp

theorem count_zero_ones (n : Nat) :
    (ones n).count zero = 0 := by
  induction n with
  | zero => simp [ones]
  | succ n ih =>
      unfold ones at ih ⊢
      rw [List.replicate_succ]
      simp [ih]

/-- A run of `one`s ending at the first `zero` has a unique length. -/
theorem ones_zero_prefix_injective
    (a b : Nat) (x y : Word CounterexampleLetter)
    (h : ones a ++ zero :: x = ones b ++ zero :: y) :
    a = b := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => rfl
      | succ b =>
          simp [ones, List.replicate_succ] at h
  | succ a ih =>
      cases b with
      | zero =>
          simp [ones, List.replicate_succ] at h
      | succ b =>
          simp [ones, List.replicate_succ] at h
          exact congrArg Nat.succ (ih b h)

def gap (s : Nat) : Word CounterexampleLetter :=
  ones s ++ [zero, hub]

def terminal : Word CounterexampleLetter :=
  [one, zero]

def counterexampleWord (n : Nat) : Word CounterexampleLetter :=
  [marker] ++ ones (n + 1) ++ [zero, hub] ++ terminal

def counterexampleStem (n : Nat) : Word CounterexampleLetter :=
  [marker] ++ ones (n + 1) ++ [zero, hub, one]

theorem counterexampleWord_length (n : Nat) :
    (counterexampleWord n).length = n + 6 := by
  simp [counterexampleWord, ones, terminal]

theorem counterexampleStem_length (n : Nat) :
    (counterexampleStem n).length = n + 5 := by
  simp [counterexampleStem, ones]

theorem counterexampleWord_eq_stem (n : Nat) :
    counterexampleWord n = counterexampleStem n ++ [zero] := by
  simp [counterexampleWord, counterexampleStem, terminal]

/-- The residual word equation `bc = cd` for the forced gap and suffix. -/
def GapEquation (s : Nat) : Prop :=
  ∃ d : Word CounterexampleLetter,
    gap s ++ terminal = terminal ++ d

/-- For `s = 1`, the residual equation has its evident solution. -/
theorem gapEquation_one : GapEquation 1 := by
  refine ⟨[hub, one, zero], ?_⟩
  simp [GapEquation, gap, terminal, ones]

/--
If the gap contains at least two initial `one`s, the equation is impossible:
its left side starts in `one,one`, whereas its right side starts in
`one,zero`.
-/
theorem not_gapEquation_of_two_le (s : Nat) (hs : 2 ≤ s) :
    ¬ GapEquation s := by
  rintro ⟨d, heq⟩
  have htake := congrArg (List.take 2) heq
  have hleft :
      (gap s ++ terminal).take 2 = [one, one] := by
    simp [gap, terminal, ones, List.take_append_eq_append_take,
      Nat.min_eq_left hs, Nat.sub_eq_zero_of_le hs]
  have hright :
      (terminal ++ d).take 2 = [one, zero] := by
    simp [terminal]
  rw [hleft, hright] at htake
  simp at htake

/-- The exact word-equation criterion used in Proposition 3.2. -/
theorem gapEquation_iff (s : Nat) (hs : 1 ≤ s) :
    GapEquation s ↔ s = 1 := by
  constructor
  · intro heq
    by_cases h : s = 1
    · exact h
    · exact False.elim
        (not_gapEquation_of_two_le s (by omega) heq)
  · intro h
    subst s
    exact gapEquation_one

/-!
The following predicate is the forced normal form of a product witness in
the component of modulus `p`.  The anchor has length `q`, the gap has
`s = n+1-q`, and the modular left language requires `p ∤ q`.
-/
def ModularWitness (p n : Nat) : Prop :=
  ∃ q s,
    1 ≤ q ∧
    ¬ p ∣ q ∧
    1 ≤ s ∧
    q + s = n + 1 ∧
    GapEquation s

def modularLeft (modulus : Nat) : Language CounterexampleLetter := fun w =>
  ∃ q,
    1 ≤ q ∧
    ¬ modulus ∣ q ∧
    w = [marker] ++ ones q

def modularRight : Language CounterexampleLetter := fun w =>
  ∃ s,
    1 ≤ s ∧
    w = gap s

def modularComponent (modulus : Nat) :
    CapComponent CounterexampleLetter where
  left := modularLeft modulus
  right := modularRight

def guardLeft : Language CounterexampleLetter := fun w =>
  ∃ a r,
    1 ≤ a ∧
    w = [marker] ++ ones a ++ [zero, hub] ++
      ones r ++ [guard]

def guardRight : Language CounterexampleLetter := fun w =>
  w = [stop]

def guardComponent : CapComponent CounterexampleLetter where
  left := guardLeft
  right := guardRight

theorem guardComponent_shuffle :
    ShuffleCondition guardComponent := by
  intro pi hleft hconcat
  rcases hleft with ⟨a, r, ha, hpi⟩
  rcases hconcat with ⟨x, y, hxy, hx, hy⟩
  have hstop : stop ∈ pi := by
    rw [hxy, hy]
    simp
  rw [hpi] at hstop
  simp [ones] at hstop

theorem counterexampleStem_guardLeft (n : Nat) :
    guardLeft (counterexampleStem n ++ [guard]) := by
  exact ⟨n + 1, 1, by omega, by
    simp [counterexampleStem, ones]⟩

/-- Every proper prefix of `W_n` lies in the prefix closure of the guard. -/
theorem properPrefix_guardPrefixRoute
    (n k : Nat) (hk : k < (counterexampleWord n).length) :
    PrefixRoute guardComponent ((counterexampleWord n).take k) := by
  have hkstem : k ≤ (counterexampleStem n).length := by
    have hwlen := counterexampleWord_length n
    rw [counterexampleStem_length]
    omega
  let target :=
    counterexampleStem n ++ [CounterexampleLetter.guard]
  have htakeWord :
      (counterexampleWord n).take k =
        (counterexampleStem n).take k := by
    rw [counterexampleWord_eq_stem]
    simp [List.take_append_eq_append_take,
      Nat.sub_eq_zero_of_le hkstem]
  have htakeTarget :
      target.take k = (counterexampleStem n).take k := by
    simp [target, List.take_append_eq_append_take,
      Nat.sub_eq_zero_of_le hkstem]
  refine ⟨target.drop k, ?_⟩
  have htarget :
      target.take k ++ target.drop k = target :=
    List.take_append_drop k target
  rw [htakeWord, ← htakeTarget, htarget]
  change guardLeft target
  simpa [target] using counterexampleStem_guardLeft n

theorem properPrefix_guardCovered
    (n k : Nat) (hk : k < (counterexampleWord n).length) :
    capComponentCovers guardComponent
      ((counterexampleWord n).take k) := by
  apply prefixRoute_capComponentCovers
  · exact ⟨[stop], rfl⟩
  · exact properPrefix_guardPrefixRoute n k hk

theorem guard_not_mem_counterexampleWord (n : Nat) :
    CounterexampleLetter.guard ∉ counterexampleWord n := by
  simp [counterexampleWord, terminal, ones]

theorem not_guardLeft_take
    (n j : Nat) :
    ¬ guardLeft ((counterexampleWord n).take j) := by
  rintro ⟨a, r, ha, heq⟩
  have hguardTake :
      CounterexampleLetter.guard ∈
        (counterexampleWord n).take j := by
    rw [heq]
    simp
  exact guard_not_mem_counterexampleWord n
    (List.mem_of_mem_take hguardTake)

theorem not_guard_prefixRoute (n : Nat) :
    ¬ PrefixRoute guardComponent (counterexampleWord n) := by
  rintro ⟨tail, a, r, ha, heq⟩
  have hcount := congrArg (List.count zero) heq
  simp [counterexampleWord, terminal, guardComponent, guardLeft,
    count_zero_ones] at hcount

theorem not_guard_splitRoute (n : Nat) :
    ¬ SplitRoute guardComponent (counterexampleWord n) := by
  rintro ⟨j, hj, hleft, -⟩
  exact not_guardLeft_take n j hleft

theorem not_guard_periodicWitness (n : Nat) :
    ¬ PeriodicWitness guardComponent (counterexampleWord n) := by
  rintro ⟨j, p, e, hp, he, hlen, hleft, -⟩
  exact not_guardLeft_take n j hleft

theorem not_guardComponent_covers (n : Nat) :
    ¬ capComponentCovers guardComponent (counterexampleWord n) := by
  have hrightNonempty : ∃ w, guardComponent.right w :=
    ⟨[stop], rfl⟩
  rw [capComponentCovers_iff_componentNormalForm
    guardComponent hrightNonempty]
  rintro (hprefix | hsplit | hperiodic)
  · exact not_guard_prefixRoute n hprefix
  · exact not_guard_splitRoute n hsplit
  · exact not_guard_periodicWitness n hperiodic

theorem counterexampleWord_take_anchor (n : Nat) :
    (counterexampleWord n).take (n + 1) =
      [marker] ++ ones n := by
  simp [counterexampleWord, ones, List.take_append_eq_append_take,
    show n + 1 - 1 = n by omega,
    show n - (n + 1) = 0 by omega]

theorem counterexampleWord_gap_factor (n : Nat) :
    Word.factor (counterexampleWord n) (n + 1) 3 =
      gap 1 := by
  simp [counterexampleWord, Word.factor, gap, terminal, ones,
    List.drop_append_eq_append_drop,
    show n + 1 - 1 = n by omega,
    show n - (n + 1) = 0 by omega,
    show n + 1 - n = 1 by omega,
    show n - (n + 2) = 0 by omega,
    show n + 2 - n = 2 by omega]

theorem counterexampleWord_witnessCopy (n : Nat) :
    Word.WitnessCopy (counterexampleWord n) (n + 1) 3 2 := by
  simp [Word.WitnessCopy, Word.factor, Word.suffix,
    counterexampleWord, terminal, ones,
    List.drop_append_eq_append_drop,
    show n + 1 - 1 = n by omega,
    show n - (n + 1) = 0 by omega,
    show n + 1 - n = 1 by omega]
  rw [show n - (n + 2) = 0 by omega,
    show n + 2 - n = 2 by omega]
  simp

/--
Every forced modular witness yields an actual periodic witness for the
corresponding cap component.
-/
theorem modularWitness_periodicWitness
    (modulus n : Nat) (hw : ModularWitness modulus n) :
    PeriodicWitness (modularComponent modulus)
      (counterexampleWord n) := by
  rcases hw with ⟨q, s, hq, hmod, hs, hsum, heq⟩
  have hsone : s = 1 := (gapEquation_iff s hs).1 heq
  have hqn : q = n := by omega
  subst s
  subst q
  refine ⟨n + 1, 3, 2, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · rw [counterexampleWord_length]
  · exact ⟨n, hq, hmod, counterexampleWord_take_anchor n⟩
  · exact ⟨1, by omega, counterexampleWord_gap_factor n⟩
  · exact counterexampleWord_witnessCopy n

theorem modularWitness_capCovered
    (modulus n : Nat) (hw : ModularWitness modulus n) :
    capComponentCovers (modularComponent modulus)
      (counterexampleWord n) :=
  periodicWitness_capComponentCovers _ _
    (modularWitness_periodicWitness modulus n hw)

/-- Every modular component satisfies shuffle vacuously. -/
theorem modularComponent_shuffle (modulus : Nat) :
    ShuffleCondition (modularComponent modulus) := by
  intro pi hleft hconcat
  rcases hleft with ⟨q, hq, hmodq, hpi⟩
  rcases hconcat with ⟨x, y, hxy, hx, hy⟩
  rcases hx with ⟨q', hq', hmodq', hx⟩
  rcases hy with ⟨s, hs, hy⟩
  have hzeroRight :
      zero ∈ ([marker] ++ ones q') ++ gap s := by
    simp [gap]
  have heq :
      [marker] ++ ones q =
        ([marker] ++ ones q') ++ gap s := by
    calc
      [marker] ++ ones q = pi := hpi.symm
      _ = x ++ y := hxy
      _ = ([marker] ++ ones q') ++ gap s := by rw [hx, hy]
  rw [← heq] at hzeroRight
  simp [ones] at hzeroRight

/--
Any semantic periodic witness on `W_n` has the forced modular normal form.
This is the parsing direction based on the unique `zero,hub` delimiter.
-/
theorem periodicWitness_modularWitness
    (modulus n : Nat)
    (hw : PeriodicWitness (modularComponent modulus)
      (counterexampleWord n)) :
    ModularWitness modulus n := by
  rcases hw with
    ⟨j, p, e, hp, he, hlen, hleft, hright, hcopy⟩
  rcases hleft with ⟨q, hq, hmod, hjword⟩
  rcases hright with ⟨s, hs, hfactor⟩
  have hjle : j ≤ (counterexampleWord n).length := by omega
  have hjlength : ((counterexampleWord n).take j).length = j := by
    simp [Nat.min_eq_left hjle]
  have hj : j = q + 1 := by
    have h := congrArg List.length hjword
    simpa [hjlength, ones] using h
  have hjp : j + p ≤ (counterexampleWord n).length := by omega
  have hfactorLength :
      (Word.factor (counterexampleWord n) j p).length = p := by
    rw [Word.factor_length]
    apply Nat.min_eq_left
    omega
  have hplen : p = s + 2 := by
    have h := congrArg List.length hfactor
    simpa [hfactorLength, gap, ones] using h
  have hprefix :
      (counterexampleWord n).take (j + p) =
        ([marker] ++ ones q) ++ gap s := by
    rw [← take_append_factor
      (w := counterexampleWord n) (j := j) (j' := j + p)
      (by omega)]
    rw [hjword, show j + p - j = p by omega, hfactor]
  have hdecomp :
      counterexampleWord n =
        (([marker] ++ ones q) ++ gap s) ++
          (counterexampleWord n).drop (j + p) := by
    calc
      counterexampleWord n =
          (counterexampleWord n).take (j + p) ++
            (counterexampleWord n).drop (j + p) :=
        (List.take_append_drop (j + p) _).symm
      _ = (([marker] ++ ones q) ++ gap s) ++
            (counterexampleWord n).drop (j + p) := by rw [hprefix]
  have hdelimiter :
      ones (n + 1) ++ zero :: (hub :: terminal) =
        ones (q + s) ++ zero ::
          (hub :: (counterexampleWord n).drop (j + p)) := by
    have h := hdecomp
    simp only [counterexampleWord, gap, List.append_assoc] at h
    have ht := (List.cons.inj h).2
    rw [← List.append_assoc (ones q) (ones s),
      ← ones_add] at ht
    simpa [counterexampleWord] using ht
  have hsum : q + s = n + 1 :=
    (ones_zero_prefix_injective
      (n + 1) (q + s) (hub :: terminal)
      (hub :: (counterexampleWord n).drop (j + p))
      hdelimiter).symm
  have heq : e = 2 := by
    rw [counterexampleWord_length, hj, hplen] at hlen
    omega
  subst e
  have hsmall :
      Word.factor (counterexampleWord n) j 2 =
        (Word.factor (counterexampleWord n) j p).take 2 := by
    simp [Word.factor, List.take_take,
      Nat.min_eq_left (by omega : 2 ≤ p)]
  have hsuffix :
      Word.suffix (counterexampleWord n) 2 = terminal := by
    rw [show counterexampleWord n =
      ([marker] ++ ones (n + 1) ++ [zero, hub]) ++ terminal by
        simp [counterexampleWord]]
    simp [Word.suffix, terminal, ones]
    rw [show n + 3 = (n + 1) + 2 by omega,
      List.drop_append_eq_append_drop]
    simp
    rw [show n - (n + 2) = 0 by omega,
      show n + 2 - n = 2 by omega]
    simp
  have htakeGap :
      (gap s).take 2 = terminal := by
    rw [← hfactor, ← hsmall, hcopy, hsuffix]
  have hsone : s = 1 := by
    by_cases h : s = 1
    · exact h
    · have hstwo : 2 ≤ s := by omega
      have : (gap s).take 2 = [one, one] := by
        simp [gap, ones, List.take_append_eq_append_take,
          Nat.min_eq_left hstwo, Nat.sub_eq_zero_of_le hstwo]
      rw [this] at htakeGap
      simp [terminal] at htakeGap
  exact ⟨q, s, hq, hmod, hs, hsum,
    (gapEquation_iff s hs).2 hsone⟩

theorem periodicWitness_iff_modularWitness
    (modulus n : Nat) :
    PeriodicWitness (modularComponent modulus)
        (counterexampleWord n) ↔
      ModularWitness modulus n := by
  exact ⟨periodicWitness_modularWitness modulus n,
    modularWitness_periodicWitness modulus n⟩

/-- The full distinguished word cannot use the left-prefix route. -/
theorem not_prefixRoute_counterexampleWord
    (modulus n : Nat) :
    ¬ PrefixRoute (modularComponent modulus)
      (counterexampleWord n) := by
  rintro ⟨tail, hleft⟩
  rcases hleft with ⟨q, hq, hmod, heq⟩
  have hzero :
      zero ∈ counterexampleWord n ++ tail := by
    simp [counterexampleWord]
  rw [heq] at hzero
  simp [ones] at hzero

/-- The full distinguished word cannot use a left/right split route. -/
theorem not_splitRoute_counterexampleWord
    (modulus n : Nat) :
    ¬ SplitRoute (modularComponent modulus)
      (counterexampleWord n) := by
  rintro ⟨j, hj, hleft, hright⟩
  rcases hleft with ⟨q, hq, hmod, htake⟩
  rcases hright with ⟨tail, s, hs, hdrop⟩
  have heq :
      counterexampleWord n ++ tail =
        ([marker] ++ ones q) ++ gap s := by
    calc
      counterexampleWord n ++ tail =
          ((counterexampleWord n).take j ++
            (counterexampleWord n).drop j) ++ tail := by
        rw [List.take_append_drop]
      _ = (counterexampleWord n).take j ++
            ((counterexampleWord n).drop j ++ tail) := by
        rw [List.append_assoc]
      _ = ([marker] ++ ones q) ++ gap s := by
        rw [htake, hdrop]
  have hcount := congrArg (List.count zero) heq
  simp [counterexampleWord, gap, terminal, count_zero_ones] at hcount

/--
The modular component covers the distinguished word exactly when its modulus
does not divide the index.
-/
theorem modularWitness_iff (p n : Nat) (hn : 1 ≤ n) :
    ModularWitness p n ↔ ¬ p ∣ n := by
  constructor
  · rintro ⟨q, s, hq, hpq, hs, hsum, heq⟩
    have hsone : s = 1 := (gapEquation_iff s hs).1 heq
    subst s
    have hqn : q = n := by omega
    simpa [hqn] using hpq
  · intro hpn
    exact ⟨n, 1, hn, hpn, by omega, by omega, gapEquation_one⟩

theorem periodicWitness_iff_not_dvd
    (modulus n : Nat) (hn : 1 ≤ n) :
    PeriodicWitness (modularComponent modulus)
        (counterexampleWord n) ↔
      ¬ modulus ∣ n := by
  rw [periodicWitness_iff_modularWitness,
    modularWitness_iff modulus n hn]

/--
Exact semantic coverage criterion for one modular cap component on `W_n`.
-/
theorem modularComponent_covers_iff
    (modulus n : Nat) (hn : 1 ≤ n) :
    capComponentCovers (modularComponent modulus)
        (counterexampleWord n) ↔
      ¬ modulus ∣ n := by
  have hrightNonempty :
      ∃ w, (modularComponent modulus).right w :=
    ⟨gap 1, 1, by omega, rfl⟩
  rw [capComponentCovers_iff_componentNormalForm
    (modularComponent modulus) hrightNonempty]
  unfold ComponentNormalForm
  constructor
  · intro h
    rcases h with hprefix | hsplit | hperiodic
    · exact False.elim
        (not_prefixRoute_counterexampleWord modulus n hprefix)
    · exact False.elim
        (not_splitRoute_counterexampleWord modulus n hsplit)
    · exact (periodicWitness_iff_not_dvd modulus n hn).1 hperiodic
  · intro h
    exact Or.inr (Or.inr
      ((periodicWitness_iff_not_dvd modulus n hn).2 h))

def modularExpression (moduli : List Nat) :
    CapExpression CounterexampleLetter where
  caps := moduli.map modularComponent
  routes := []

theorem modularExpression_restricted (moduli : List Nat) :
    (modularExpression moduli).IsRestricted := by
  intro c hc
  simp [modularExpression] at hc
  rcases hc with ⟨p, hp, rfl⟩
  exact modularComponent_shuffle p

theorem modularExpression_capCovered_iff
    (moduli : List Nat) (n : Nat) (hn : 1 ≤ n) :
    capCovered (modularExpression moduli)
        (counterexampleWord n) ↔
      ∃ p ∈ moduli, ¬ p ∣ n := by
  constructor
  · rintro ⟨c, hc, hcovers⟩
    simp [modularExpression] at hc
    rcases hc with ⟨p, hp, rfl⟩
    exact ⟨p, hp,
      (modularComponent_covers_iff p n hn).1 hcovers⟩
  · rintro ⟨p, hp, hpdvd⟩
    exact ⟨modularComponent p, by
      change modularComponent p ∈ moduli.map modularComponent
      exact List.mem_map_of_mem hp,
      (modularComponent_covers_iff p n hn).2 hpdvd⟩

theorem modularExpression_uncovered_iff
    (moduli : List Nat) (n : Nat) (hn : 1 ≤ n) :
    (modularExpression moduli).Uncovered
        (counterexampleWord n) ↔
      ∀ p ∈ moduli, p ∣ n := by
  classical
  unfold CapExpression.Uncovered CapExpression.Covers
  have hroute :
      ¬ routeCovered (modularExpression moduli)
        (counterexampleWord n) := by
    rintro ⟨R, hR, -⟩
    simp [modularExpression] at hR
  rw [or_iff_left hroute,
    modularExpression_capCovered_iff moduli n hn]
  constructor
  · intro h p hp
    by_cases hdiv : p ∣ n
    · exact hdiv
    · exact False.elim (h ⟨p, hp, hdiv⟩)
  · intro h hex
    rcases hex with ⟨p, hp, hnot⟩
    exact hnot (h p hp)

theorem modularExpression_first_uncovered
    (moduli : List Nat) (M : Nat)
    (hMpos : 0 < M)
    (hM : ∀ n, M ∣ n ↔ ∀ p ∈ moduli, p ∣ n) :
    (modularExpression moduli).Uncovered
        (counterexampleWord M) ∧
      ∀ n, 1 ≤ n → n < M →
        ¬ (modularExpression moduli).Uncovered
          (counterexampleWord n) := by
  constructor
  · exact (modularExpression_uncovered_iff
      moduli M hMpos).2 ((hM M).1 (Nat.dvd_refl M))
  · intro n hn hnM huncovered
    have hMdiv : M ∣ n := (hM n).2
      ((modularExpression_uncovered_iff moduli n hn).1 huncovered)
    have hMle : M ≤ n := Nat.le_of_dvd hn hMdiv
    omega

/-! ## Guarded full expression -/

def counterexampleFamily : Language CounterexampleLetter := fun w =>
  ∃ n, 1 ≤ n ∧ w = counterexampleWord n

def counterexampleG : Language CounterexampleLetter :=
  Language.prefixClosure counterexampleFamily

def outsideG : Language CounterexampleLetter := fun w =>
  ¬ counterexampleG w

def GShape (w : Word CounterexampleLetter) : Prop :=
  w = [] ∨
  w = [marker] ∨
  (∃ a, 1 ≤ a ∧ w = [marker] ++ ones a) ∨
  ∃ a, 2 ≤ a ∧
    (w = [marker] ++ ones a ++ [zero] ∨
     w = [marker] ++ ones a ++ [zero, hub] ∨
     w = [marker] ++ ones a ++ [zero, hub, one] ∨
     w = [marker] ++ ones a ++ [zero, hub, one, zero])

theorem take_counterexampleWord_shape
    (n k : Nat) (hn : 1 ≤ n)
    (hk : k ≤ (counterexampleWord n).length) :
    GShape ((counterexampleWord n).take k) := by
  rw [counterexampleWord_length] at hk
  by_cases hk0 : k = 0
  · subst k
    exact Or.inl (by simp)
  by_cases hk1 : k = 1
  · subst k
    exact Or.inr (Or.inl (by
      simp [counterexampleWord]))
  by_cases hkones : k ≤ n + 2
  · apply Or.inr (Or.inr (Or.inl ?_))
    refine ⟨k - 1, by omega, ?_⟩
    rw [show k = (k - 1) + 1 by omega]
    simp [counterexampleWord, ones,
      List.take_append_eq_append_take,
      show k - 1 ≤ n + 1 by omega,
      show k - 1 - (n + 1) = 0 by omega,
      show min (k - 1) (n + 1) = k - 1 by omega]
  · apply Or.inr (Or.inr (Or.inr ?_))
    refine ⟨n + 1, by omega, ?_⟩
    have hkCases :
        k = n + 3 ∨ k = n + 4 ∨
          k = n + 5 ∨ k = n + 6 := by omega
    rcases hkCases with rfl | rfl | rfl | rfl
    · exact Or.inl (by
        simp [counterexampleWord, terminal, ones,
          List.take_append_eq_append_take,
          show n + 2 - (n + 1) = 1 by omega,
          show min 2 1 = 1 by omega])
    · exact Or.inr (Or.inl (by
        simp [counterexampleWord, terminal, ones,
          List.take_append_eq_append_take,
          show n + 3 - (n + 1) = 2 by omega,
          show min 3 1 = 1 by omega]))
    · exact Or.inr (Or.inr (Or.inl (by
        simp [counterexampleWord, terminal, ones,
          List.take_append_eq_append_take,
          show n + 4 - (n + 1) = 3 by omega,
          show min 4 1 = 1 by omega])))
    · exact Or.inr (Or.inr (Or.inr (by
        simp [counterexampleWord, terminal, ones,
          List.take_append_eq_append_take,
          show n + 5 - (n + 1) = 4 by omega,
          show min 5 1 = 1 by omega])))

theorem gShape_mem_counterexampleG
    (w : Word CounterexampleLetter) (hw : GShape w) :
    counterexampleG w := by
  rcases hw with hnil | hmarker | hones | htail
  · subst w
    refine ⟨counterexampleWord 1, 1, by omega, ?_⟩
    simp
  · subst w
    refine ⟨(counterexampleWord 1).drop 1, 1, by omega, ?_⟩
    simp [counterexampleWord]
  · rcases hones with ⟨a, ha, rfl⟩
    by_cases ha1 : a = 1
    · subst a
      refine ⟨[one, zero, hub, one, zero], 1, by omega, ?_⟩
      simp [counterexampleWord, terminal, ones]
    · refine ⟨[zero, hub, one, zero], a - 1, by omega, ?_⟩
      simp [counterexampleWord, terminal, ones,
        show a - 1 + 1 = a by omega]
  · rcases htail with ⟨a, ha, hzero | hhub | hone | hfull⟩
    · subst w
      refine ⟨[hub, one, zero], a - 1, by omega, ?_⟩
      simp [counterexampleWord, terminal, ones,
        show a - 1 + 1 = a by omega]
    · subst w
      refine ⟨[one, zero], a - 1, by omega, ?_⟩
      simp [counterexampleWord, terminal, ones,
        show a - 1 + 1 = a by omega]
    · subst w
      refine ⟨[zero], a - 1, by omega, ?_⟩
      simp [counterexampleWord, terminal, ones,
        show a - 1 + 1 = a by omega]
    · subst w
      refine ⟨[], a - 1, by omega, ?_⟩
      simp [counterexampleWord, terminal, ones,
        show a - 1 + 1 = a by omega]

theorem counterexampleG_iff_gShape
    (w : Word CounterexampleLetter) :
    counterexampleG w ↔ GShape w := by
  constructor
  · rintro ⟨tail, n, hn, heq⟩
    have hwle : w.length ≤ (counterexampleWord n).length := by
      have hlen := congrArg List.length heq
      simp only [List.length_append] at hlen
      omega
    have htake :
        (counterexampleWord n).take w.length = w := by
      have ht := congrArg (List.take w.length) heq
      simpa using ht.symm
    rw [← htake]
    exact take_counterexampleWord_shape n w.length hn hwle
  · exact gShape_mem_counterexampleG w

def guardedExpression (moduli : List Nat) :
    CapExpression CounterexampleLetter where
  caps := guardComponent :: moduli.map modularComponent
  routes := [outsideG]

theorem guardedExpression_restricted (moduli : List Nat) :
    (guardedExpression moduli).IsRestricted := by
  intro c hc
  simp [guardedExpression] at hc
  rcases hc with rfl | ⟨p, hp, rfl⟩
  · exact guardComponent_shuffle
  · exact modularComponent_shuffle p

theorem outsideG_append
    (x tail : Word CounterexampleLetter) (hx : outsideG x) :
    outsideG (x ++ tail) := by
  intro h
  apply hx
  rcases h with ⟨outer, hfamily⟩
  exact ⟨tail ++ outer, by
    simpa [List.append_assoc] using hfamily⟩

theorem routeCovered_of_not_mem_G
    (moduli : List Nat) (w : Word CounterexampleLetter)
    (hw : ¬ counterexampleG w) :
    routeCovered (guardedExpression moduli) w := by
  exact ⟨outsideG, by simp [guardedExpression],
    w, [], by simp, hw, trivial⟩

theorem counterexampleWord_mem_G (n : Nat) (hn : 1 ≤ n) :
    counterexampleG (counterexampleWord n) :=
  ⟨[], n, hn, by simp⟩

theorem counterexampleWord_routeFree
    (moduli : List Nat) (n : Nat) (hn : 1 ≤ n) :
    routeFree (guardedExpression moduli)
      (counterexampleWord n) := by
  intro hroute
  rcases hroute with ⟨R, hR, x, y, hxy, hx, -⟩
  simp [guardedExpression] at hR
  subst R
  apply hx
  exact ⟨y, n, hn, hxy.symm⟩

theorem guardedExpression_capCovered_iff
    (moduli : List Nat) (n : Nat) (hn : 1 ≤ n) :
    capCovered (guardedExpression moduli)
        (counterexampleWord n) ↔
      ∃ p ∈ moduli, ¬ p ∣ n := by
  constructor
  · rintro ⟨c, hc, hcovers⟩
    simp [guardedExpression] at hc
    rcases hc with rfl | ⟨p, hp, rfl⟩
    · exact False.elim (not_guardComponent_covers n hcovers)
    · exact ⟨p, hp,
        (modularComponent_covers_iff p n hn).1 hcovers⟩
  · rintro ⟨p, hp, hnot⟩
    refine ⟨modularComponent p, ?_,
      (modularComponent_covers_iff p n hn).2 hnot⟩
    simp [guardedExpression]
    exact Or.inr ⟨p, hp, rfl⟩

theorem guardedExpression_uncovered_iff
    (moduli : List Nat) (n : Nat) (hn : 1 ≤ n) :
    (guardedExpression moduli).Uncovered
        (counterexampleWord n) ↔
      ∀ p ∈ moduli, p ∣ n := by
  classical
  unfold CapExpression.Uncovered CapExpression.Covers
  have hroute :=
    counterexampleWord_routeFree moduli n hn
  rw [or_iff_left hroute,
    guardedExpression_capCovered_iff moduli n hn]
  constructor
  · intro h p hp
    by_cases hdiv : p ∣ n
    · exact hdiv
    · exact False.elim (h ⟨p, hp, hdiv⟩)
  · intro h hex
    rcases hex with ⟨p, hp, hnot⟩
    exact hnot (h p hp)

theorem properPrefix_guardedCovered
    (moduli : List Nat) (n k : Nat)
    (hk : k < (counterexampleWord n).length) :
    (guardedExpression moduli).Covers
      ((counterexampleWord n).take k) := by
  apply Or.inl
  exact ⟨guardComponent, by simp [guardedExpression],
    properPrefix_guardCovered n k hk⟩

/--
Every word shorter than `W_M` is covered; hence `W_M` is a shortest
counterexample for the guarded expression.
-/
theorem guardedExpression_shortest_uncovered
    (moduli : List Nat) (M : Nat)
    (hMpos : 0 < M)
    (hM : ∀ n, M ∣ n ↔ ∀ p ∈ moduli, p ∣ n) :
    (guardedExpression moduli).Uncovered
        (counterexampleWord M) ∧
      ∀ w, w.length < (counterexampleWord M).length →
        (guardedExpression moduli).Covers w := by
  classical
  constructor
  · exact (guardedExpression_uncovered_iff
      moduli M hMpos).2 ((hM M).1 (Nat.dvd_refl M))
  · intro w hwlen
    by_cases hwG : counterexampleG w
    · rcases hwG with ⟨tail, n, hn, heq⟩
      by_cases htail : tail = []
      · subst tail
        simp only [List.append_nil] at heq
        subst w
        have hnM : n < M := by
          rw [counterexampleWord_length,
            counterexampleWord_length] at hwlen
          omega
        have hnotMdiv : ¬ M ∣ n := by
          intro hdiv
          exact (Nat.not_le_of_gt hnM) (Nat.le_of_dvd hn hdiv)
        have hnotAll : ¬ ∀ p ∈ moduli, p ∣ n := by
          intro hall
          exact hnotMdiv ((hM n).2 hall)
        have hcovered :
            ¬ (guardedExpression moduli).Uncovered
              (counterexampleWord n) := by
          intro hu
          exact hnotAll
            ((guardedExpression_uncovered_iff moduli n hn).1 hu)
        exact Classical.byContradiction fun hnot =>
          hcovered hnot
      · have hk :
            w.length < (counterexampleWord n).length := by
          have hlen := congrArg List.length heq
          simp only [List.length_append] at hlen
          have htailPos : 0 < tail.length :=
            List.length_pos_iff.2 htail
          omega
        have htake :
            (counterexampleWord n).take w.length = w := by
          have ht := congrArg (List.take w.length) heq
          simpa using ht.symm
        rw [← htake]
        exact properPrefix_guardedCovered moduli n w.length hk
    · exact Or.inr (routeCovered_of_not_mem_G moduli w hwG)

/-- A finite family misses `W_n` exactly when all its moduli divide `n`. -/
theorem noModularWitness_iff_all_dvd
    (moduli : List Nat) (n : Nat) (hn : 1 ≤ n) :
    (∀ p ∈ moduli, ¬ ModularWitness p n) ↔
      ∀ p ∈ moduli, p ∣ n := by
  constructor
  · intro h p hp
    by_cases hpdvd : p ∣ n
    · exact hpdvd
    · exact False.elim
        (h p hp ((modularWitness_iff p n hn).2 hpdvd))
  · intro h p hp hwitness
    exact (modularWitness_iff p n hn).1 hwitness (h p hp)

def IsCommonPeriod (moduli : List Nat) (M : Nat) : Prop :=
  0 < M ∧ ∀ n, M ∣ n ↔ ∀ p ∈ moduli, p ∣ n

theorem noModularWitness_iff_commonPeriod_dvd
    (moduli : List Nat) (M n : Nat)
    (hM : IsCommonPeriod moduli M) (hn : 1 ≤ n) :
    (∀ p ∈ moduli, ¬ ModularWitness p n) ↔
      M ∣ n := by
  rw [noModularWitness_iff_all_dvd moduli n hn, ← hM.2 n]

/--
Among positive indices, the first index missed by every modular component is
the least common multiple of the displayed moduli.
-/
theorem first_noModularWitness
    (moduli : List Nat) (M : Nat)
    (hM : IsCommonPeriod moduli M) :
    (∀ p ∈ moduli,
        ¬ ModularWitness p M) ∧
      ∀ n, 1 ≤ n → n < M →
        ∃ p ∈ moduli, ModularWitness p n := by
  classical
  constructor
  · exact (noModularWitness_iff_commonPeriod_dvd
      moduli M M hM hM.1).2 (Nat.dvd_refl _)
  · intro n hn hnM
    by_cases hall : ∀ p ∈ moduli, ¬ ModularWitness p n
    · have hMdiv :
          M ∣ n :=
        (noModularWitness_iff_commonPeriod_dvd
          moduli M n hM hn).1 hall
      have hMle : M ≤ n :=
        Nat.le_of_dvd hn hMdiv
      omega
    · apply Classical.byContradiction
      intro hnone
      apply hall
      intro p hp hwitness
      apply hnone
      exact ⟨p, hp, hwitness⟩

end SuperpolynomialCounterexample

end NSSE
