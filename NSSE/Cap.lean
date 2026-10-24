import NSSE.Insertion

/-!
# Restricted cap-set expression semantics

This module formalizes the language-theoretic front end of `proofs_en.md`:
the cap operator, restricted-cap expression coverage, universality, the route
reduction (Proposition 1.1), and the finite witness predicates used in Lemma
1.3 / Theorem 9.1.  Regularity is deliberately orthogonal: an automaton will
later supply a particular `Language α`.
-/

namespace NSSE

universe u

abbrev Language (α : Type u) := Word α → Prop

namespace Language

def univ : Language α := fun _ => True

def concat (L M : Language α) : Language α := fun w =>
  ∃ x y, w = x ++ y ∧ L x ∧ M y

def prefixClosure (L : Language α) : Language α := fun w =>
  ∃ tail, L (w ++ tail)

def wordPower (w : Word α) (k : Nat) : Word α :=
  (List.replicate k w).flatten

/-- `S° = {π | π ∈ pr(μ*) for some μ ∈ S}`. -/
def cap (S : Language α) : Language α := fun pi =>
  ∃ mu k tail, S mu ∧ wordPower mu k = pi ++ tail

theorem wordPower_succ (w : Word α) (k : Nat) :
    wordPower w (k + 1) = w ++ wordPower w k := by
  simp [wordPower, List.replicate_succ]

theorem wordPower_succ_right (w : Word α) (k : Nat) :
    wordPower w (k + 1) = wordPower w k ++ w := by
  have hrep :
      List.replicate (k + 1) w = List.replicate k w ++ [w] := by
    induction k with
    | zero => simp
    | succ k ih =>
        change w :: List.replicate (k + 1) w =
          w :: (List.replicate k w ++ [w])
        exact congrArg (List.cons w) ih
  simp [wordPower, hrep]

theorem hasPeriod_take
    (w : Word α) {p k : Nat}
    (hperiod : Word.HasPeriod w p)
    (hpk : p < k) (hkw : k ≤ w.length) :
    Word.HasPeriod (w.take k) p := by
  rcases hperiod with ⟨hpw, heq⟩
  have hsmall : k - p ≤ w.length - p := by omega
  have heq' := Word.factor_eq_of_factor_eq_of_le
    w 0 p (w.length - p) (k - p) hsmall heq
  have hlen : (w.take k).length = k := by simp [Nat.min_eq_left hkw]
  refine ⟨by omega, ?_⟩
  unfold Word.factor at heq' ⊢
  simp only [hlen]
  simpa [List.drop_take, List.take_take, Nat.min_eq_left hkw,
    Nat.min_eq_left (Nat.sub_le k p)] using heq'

/--
A finite word of positive proper period `p` is a prefix of a sufficiently
long finite power of its first `p` letters.

This is the repetition lemma needed for the reverse implication of the
period characterization in Lemma 1.2.
-/
theorem hasPeriod_prefix_wordPower
    (w : Word α) (p : Nat)
    (hp : 0 < p) (hperiod : Word.HasPeriod w p) :
    ∃ k tail,
      wordPower (w.take p) k = w ++ tail := by
  suffices ∀ n, ∀ v : Word α, v.length = n →
      Word.HasPeriod v p →
      ∃ k tail, wordPower (v.take p) k = v ++ tail by
    exact this w.length w rfl hperiod
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro w hn hperiod
      have hpw : p < w.length := hperiod.1
      have htake : w.take (w.length - p) = w.drop p := by
        have heq := hperiod.2
        unfold Word.factor at heq
        calc
          w.take (w.length - p) =
              (w.drop p).take (w.length - p) := heq
          _ = w.drop p := by
            apply List.take_of_length_le
            simp
      let r := w.drop p
      have hw : w = w.take p ++ r := by
        simp [r]
      by_cases hpr : p < r.length
      · have hrlen : r.length < w.length := by
          simp [r]
          omega
        have hrtake : r = w.take (w.length - p) := htake.symm
        have hpr' : p < w.length - p := by simpa [r] using hpr
        have hrperiod : Word.HasPeriod r p := by
          rw [hrtake]
          exact hasPeriod_take w hperiod hpr' (by omega)
        obtain ⟨k, tail, hk⟩ :=
          ih r.length (by rw [← hn]; exact hrlen) r rfl hrperiod
        have hbase : r.take p = w.take p := by
          rw [hrtake, List.take_take]
          simp [Nat.min_eq_left (Nat.le_of_lt hpr'),
            Nat.min_eq_left (Nat.le_of_lt hpw)]
        refine ⟨k + 1, tail, ?_⟩
        calc
          wordPower (w.take p) (k + 1) =
              w.take p ++ wordPower (w.take p) k := wordPower_succ _ _
          _ = r.take p ++ wordPower (r.take p) k := by rw [hbase]
          _ = r.take p ++ (r ++ tail) := by rw [hk]
          _ = w.take p ++ (r ++ tail) := by rw [hbase]
          _ = (w.take p ++ r) ++ tail := by simp [List.append_assoc]
          _ = w ++ tail := congrArg (fun x => x ++ tail) hw.symm
      · have hrle : r.length ≤ p := by omega
        have hrprefix : w.take p = r ++ (w.take p).drop r.length := by
          have hrlenEq : r.length = w.length - p := by simp [r]
          have hsuble : w.length - p ≤ p := by
            rw [← hrlenEq]
            exact hrle
          have hfirst : (w.take p).take r.length = r := by
            calc
              (w.take p).take r.length =
                  w.take (w.length - p) := by
                    rw [hrlenEq, List.take_take]
                    simp [Nat.min_eq_left hsuble]
              _ = r := by simpa [r] using htake
          calc
            w.take p =
                (w.take p).take r.length ++
                  (w.take p).drop r.length :=
                    (List.take_append_drop r.length (w.take p)).symm
            _ = r ++ (w.take p).drop r.length := by rw [hfirst]
        refine ⟨2, (w.take p).drop r.length, ?_⟩
        calc
          wordPower (w.take p) 2 =
              w.take p ++ w.take p := by simp [wordPower]
          _ = w.take p ++
              (r ++ (w.take p).drop r.length) :=
                congrArg (fun x => w.take p ++ x) hrprefix
          _ = (w.take p ++ r) ++
              (w.take p).drop r.length := by simp [List.append_assoc]
          _ = w ++ (w.take p).drop r.length :=
                congrArg (fun x => x ++ (w.take p).drop r.length) hw.symm

/-- The periodic branch of the reverse implication in Lemma 1.2. -/
theorem mem_cap_of_period
    (S : Language α) (sigma : Word α) (p : Nat)
    (hp : 0 < p) (hperiod : Word.HasPeriod sigma p)
    (hroot : S (sigma.take p)) :
    cap S sigma := by
  obtain ⟨k, tail, hpower⟩ :=
    hasPeriod_prefix_wordPower sigma p hp hperiod
  exact ⟨sigma.take p, k, tail, hroot, hpower⟩

theorem mem_prefixClosure_iff (L : Language α) (w : Word α) :
    prefixClosure L w ↔ ∃ tail, L (w ++ tail) := Iff.rfl

theorem prefixClosure_mono {L M : Language α}
    (h : ∀ w, L w → M w) :
    ∀ w, prefixClosure L w → prefixClosure M w := by
  rintro w ⟨tail, hw⟩
  exact ⟨tail, h _ hw⟩

theorem prefixClosure_idem (L : Language α) (w : Word α) :
    prefixClosure (prefixClosure L) w ↔ prefixClosure L w := by
  constructor
  · rintro ⟨x, y, h⟩
    refine ⟨x ++ y, ?_⟩
    simpa [List.append_assoc] using h
  · rintro ⟨x, h⟩
    exact ⟨x, [], by simpa using h⟩

theorem cap_prefix_closed (S : Language α) :
    ∀ {x y}, cap S (x ++ y) → cap S x := by
  rintro x y ⟨mu, k, tail, hmu, hpow⟩
  exact ⟨mu, k, y ++ tail, hmu, by simpa [List.append_assoc] using hpow⟩

theorem nil_mem_cap_of_nonempty (S : Language α)
    (hne : ∃ mu, S mu) : cap S [] := by
  rcases hne with ⟨mu, hmu⟩
  exact ⟨mu, 0, [], hmu, rfl⟩

/-- Every prefix of a word in `S` belongs to `S°` (the `k = 1` case). -/
theorem prefixClosure_le_cap (S : Language α) :
    ∀ w, prefixClosure S w → cap S w := by
  rintro w ⟨tail, hw⟩
  exact ⟨w ++ tail, 1, tail, hw, by simp [wordPower]⟩

/--
Lemma 1.2, reverse direction: either an ordinary `S`-prefix or an accepted
proper period root supplies membership in the cap language.
-/
theorem prefixOrPeriod_le_cap (S : Language α) (sigma : Word α) :
    (prefixClosure S sigma ∨
      ∃ p, 0 < p ∧ Word.HasPeriod sigma p ∧ S (sigma.take p)) →
    cap S sigma := by
  rintro (hprefix | ⟨p, hp, hperiod, hroot⟩)
  · exact prefixClosure_le_cap S sigma hprefix
  · exact mem_cap_of_period S sigma p hp hperiod hroot

/--
A prefix longer than one nonempty root block of a finite root power has
that root length as a proper period, and its first root block is the root.
-/
theorem period_of_prefix_wordPower
    (mu sigma tail : Word α) (k : Nat)
    (hmu : 0 < mu.length)
    (hshort : mu.length < sigma.length)
    (hpower : wordPower mu k = sigma ++ tail) :
    sigma.take mu.length = mu ∧ Word.HasPeriod sigma mu.length := by
  have hk : 0 < k := by
    by_cases hk0 : k = 0
    · subst k
      have hlen := congrArg List.length hpower
      simp [wordPower] at hlen
      omega
    · omega
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hmle : mu.length ≤ sigma.length := Nat.le_of_lt hshort
  have hroot : sigma.take mu.length = mu := by
    have ht := congrArg (List.take mu.length) hpower
    rw [List.take_append_of_le_length hmle] at ht
    simpa [wordPower_succ] using ht.symm
  let rest := sigma.drop mu.length
  have hrestPower :
      wordPower mu q = rest ++ tail := by
    have hd := congrArg (List.drop mu.length) hpower
    simpa [wordPower_succ, rest, List.drop_append_of_le_length hmle] using hd
  have hrestLen :
      rest.length ≤ (wordPower mu q).length := by
    have hlen := congrArg List.length hrestPower
    simp only [List.length_append] at hlen
    omega
  have hwholeTake :
      (wordPower mu (q + 1)).take sigma.length = sigma := by
    rw [hpower]
    simp
  have hrestTake :
      (wordPower mu q).take rest.length = rest := by
    rw [hrestPower]
    simp
  have hwholeRestTake :
      (wordPower mu (q + 1)).take rest.length = rest := by
    rw [wordPower_succ_right, List.take_append_of_le_length hrestLen]
    exact hrestTake
  have hrestle : rest.length ≤ sigma.length := by
    simp [rest]
  have hsigmaRestTake : sigma.take rest.length = rest := by
    calc
      sigma.take rest.length =
          ((wordPower mu (q + 1)).take sigma.length).take rest.length := by
            rw [hwholeTake]
      _ = (wordPower mu (q + 1)).take rest.length := by
            simp [List.take_take, Nat.min_eq_left hrestle]
      _ = rest := hwholeRestTake
  refine ⟨hroot, ?_⟩
  refine ⟨hshort, ?_⟩
  unfold Word.factor
  have hrestLength : rest.length = sigma.length - mu.length := by
    simp [rest]
  rw [hrestLength] at hsigmaRestTake
  have htakeDrop :
      (sigma.drop mu.length).take (sigma.length - mu.length) =
        sigma.drop mu.length := by
    apply List.take_of_length_le
    simp
  simpa [rest, htakeDrop] using hsigmaRestTake

/--
Lemma 1.2, forward direction for a nonempty capped word: a cap witness
either exposes an ordinary `S` prefix or a positive proper period whose
root prefix belongs to `S`.
-/
theorem cap_le_prefixOrPeriod
    (S : Language α) (sigma : Word α)
    (hsigma : sigma ≠ []) :
    cap S sigma →
      prefixClosure S sigma ∨
        ∃ p, 0 < p ∧ Word.HasPeriod sigma p ∧ S (sigma.take p) := by
  rintro ⟨mu, k, tail, hmuS, hpower⟩
  by_cases hlen : sigma.length ≤ mu.length
  · apply Or.inl
    have hk : 0 < k := by
      by_cases hk0 : k = 0
      · subst k
        have hempty : sigma ++ tail = [] := by
          simpa [wordPower] using hpower.symm
        exact False.elim (hsigma (List.append_eq_nil_iff.mp hempty).1)
      · omega
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    refine ⟨mu.drop sigma.length, ?_⟩
    have ht := congrArg (List.take sigma.length) hpower
    have hsigmaTake : (sigma ++ tail).take sigma.length = sigma := by simp
    have hmuTake : mu.take sigma.length = sigma := by
      rw [List.take_append_of_le_length (Nat.le_refl sigma.length)] at ht
      simpa [wordPower_succ, List.take_append_of_le_length hlen] using ht
    have hmudecomp :
        mu = sigma ++ mu.drop sigma.length := by
      calc
        mu = mu.take sigma.length ++ mu.drop sigma.length :=
          (List.take_append_drop sigma.length mu).symm
        _ = sigma ++ mu.drop sigma.length :=
          congrArg (fun x => x ++ mu.drop sigma.length) hmuTake
    rw [← hmudecomp]
    exact hmuS
  · have hmupos : 0 < mu.length := by
      by_cases hm : mu.length = 0
      · have hnil : mu = [] := List.length_eq_zero_iff.mp hm
        subst mu
        have hempty : sigma ++ tail = [] := by
          simpa [wordPower] using hpower.symm
        exact False.elim (hsigma (List.append_eq_nil_iff.mp hempty).1)
      · omega
    have hshort : mu.length < sigma.length := by omega
    obtain ⟨hroot, hperiod⟩ :=
      period_of_prefix_wordPower mu sigma tail k hmupos hshort hpower
    exact Or.inr ⟨mu.length, hmupos, hperiod, by simpa [hroot] using hmuS⟩

/--
Lemma 1.2 (period characterization), in the project definitions. For a
nonempty word, cap membership is equivalent to either ordinary prefix
membership or an accepted positive proper period root.

The paper additionally assumes `S` nonempty for its surrounding
preprocessing convention; the equivalence itself does not require it.
-/
theorem mem_cap_iff_prefixOrPeriod
    (S : Language α) (sigma : Word α)
    (hsigma : sigma ≠ []) :
    cap S sigma ↔
      prefixClosure S sigma ∨
        ∃ p, 0 < p ∧ Word.HasPeriod sigma p ∧ S (sigma.take p) := by
  exact ⟨cap_le_prefixOrPeriod S sigma hsigma,
    prefixOrPeriod_le_cap S sigma⟩

end Language

structure CapComponent (α : Type u) where
  left : Language α
  right : Language α

structure CapExpression (α : Type u) where
  caps : List (CapComponent α)
  routes : List (Language α)

/-- The Niehren--Priesnitz shuffle side condition for one cap component. -/
def ShuffleCondition (c : CapComponent α) : Prop :=
  ∀ pi, c.left pi → Language.concat c.left c.right pi →
    ∀ tail, c.left (pi ++ tail)

/--
The factor between two nested cut positions reconstructs the longer prefix.
-/
theorem take_append_factor {w : Word α} {j j' : Nat}
    (hjj' : j ≤ j') :
    w.take j ++ Word.factor w j (j' - j) = w.take j' := by
  rw [Word.factor, ← List.take_add, Nat.add_sub_of_le hjj']

/-- A cap expression is restricted when every cap component satisfies shuffle. -/
def CapExpression.IsRestricted (E : CapExpression α) : Prop :=
  ∀ c ∈ E.caps, ShuffleCondition c

def capComponentCovers (c : CapComponent α) : Language α :=
  Language.prefixClosure (Language.concat c.left (Language.cap c.right))

def capCovered (E : CapExpression α) (w : Word α) : Prop :=
  ∃ c ∈ E.caps, capComponentCovers c w

def routeCovered (E : CapExpression α) (w : Word α) : Prop :=
  ∃ R ∈ E.routes, Language.concat R Language.univ w

def CapExpression.Covers (E : CapExpression α) (w : Word α) : Prop :=
  capCovered E w ∨ routeCovered E w

def CapExpression.Universal (E : CapExpression α) : Prop :=
  ∀ w, E.Covers w

def CapExpression.Uncovered (E : CapExpression α) (w : Word α) : Prop :=
  ¬ E.Covers w

def routeFree (E : CapExpression α) (w : Word α) : Prop :=
  ¬ routeCovered E w

/-- Proposition 1.1, without the separate regularity/effectivity claim. -/
theorem universal_iff_routeFree_capCovered (E : CapExpression α) :
    E.Universal ↔ ∀ w, routeFree E w → capCovered E w := by
  constructor
  · intro h w hfree
    rcases h w with hcap | hroute
    · exact hcap
    · exact False.elim (hfree hroute)
  · intro h w
    by_cases hroute : routeCovered E w
    · exact Or.inr hroute
    · exact Or.inl (h w hroute)

theorem not_universal_iff_exists_uncovered (E : CapExpression α) :
    ¬ E.Universal ↔ ∃ w, E.Uncovered w := by
  classical
  simp [CapExpression.Universal, CapExpression.Uncovered]

/-- A route language followed by `A*` covers exactly words with a marked prefix. -/
theorem concat_univ_iff_markedPrefix (R : Language α) (w : Word α) :
    Language.concat R Language.univ w ↔
      ∃ j, j ≤ w.length ∧ R (w.take j) := by
  constructor
  · rintro ⟨x, y, rfl, hx, -⟩
    exact ⟨x.length, by simp, by simpa using hx⟩
  · rintro ⟨j, hj, hprefix⟩
    exact ⟨w.take j, w.drop j, (List.take_append_drop j w).symm,
      hprefix, trivial⟩

theorem routeCovered_iff_markedPrefix (E : CapExpression α) (w : Word α) :
    routeCovered E w ↔
      ∃ R ∈ E.routes, ∃ j, j ≤ w.length ∧ R (w.take j) := by
  constructor
  · rintro ⟨R, hR, hw⟩
    exact ⟨R, hR, (concat_univ_iff_markedPrefix R w).1 hw⟩
  · rintro ⟨R, hR, hw⟩
    exact ⟨R, hR, (concat_univ_iff_markedPrefix R w).2 hw⟩

/-- A universally accepting route makes the whole expression universal. -/
theorem routeOnly_universal (R : Language α) (hall : ∀ w, R w) :
    (CapExpression.mk [] [R]).Universal := by
  intro w
  apply Or.inr
  refine ⟨R, by simp, [], w, by simp, hall [], trivial⟩

/--
A single cap component is universal when its left language accepts the empty
word and its right language accepts every word. This is a direct semantic
sanity check that uses the cap branch rather than the route branch.
-/
theorem capComponent_universal_of_nil_left_right_univ
    (c : CapComponent α) (hleft : c.left [])
    (hright : ∀ w, c.right w) :
    ∀ w, capComponentCovers c w := by
  intro w
  refine ⟨[], [], w, by simp, hleft, ?_⟩
  apply Language.prefixClosure_le_cap c.right w
  exact ⟨[], by simpa using hright w⟩

theorem singleCap_universal_of_nil_left_right_univ
    (c : CapComponent α) (hleft : c.left [])
    (hright : ∀ w, c.right w) :
    (CapExpression.mk [c] []).Universal := by
  intro w
  apply Or.inl
  exact ⟨c, by simp,
    capComponent_universal_of_nil_left_right_univ c hleft hright w⟩

/-! ## Certificate normal-form predicates -/

def PrefixRoute (c : CapComponent α) (w : Word α) : Prop :=
  Language.prefixClosure c.left w

/--
Lemma 5.1 (shuffle non-rechaining): once a later left prefix can be obtained
by a left/right split at an earlier cut, shuffle promotes that later prefix
to the whole word. Thus no further cap rechaining is needed.
-/
theorem shuffle_non_rechaining
    (c : CapComponent α) (w : Word α) {j j' : Nat}
    (hshuffle : ShuffleCondition c)
    (hjj' : j ≤ j')
    (hleft : c.left (w.take j))
    (hleft' : c.left (w.take j'))
    (hright : c.right (Word.factor w j (j' - j))) :
    c.left w ∧ PrefixRoute c w := by
  have hconcat : Language.concat c.left c.right (w.take j') := by
    exact ⟨w.take j, Word.factor w j (j' - j),
      (take_append_factor hjj').symm, hleft, hright⟩
  have hwhole : c.left w := by
    have htail := hshuffle (w.take j') hleft' hconcat (w.drop j')
    simpa using htail
  exact ⟨hwhole, [], by simpa using hwhole⟩

def SplitRoute (c : CapComponent α) (w : Word α) : Prop :=
  ∃ j, j ≤ w.length ∧ c.left (w.take j) ∧
    Language.prefixClosure c.right (w.drop j)

theorem prefixRoute_capComponentCovers
    (c : CapComponent α) (w : Word α)
    (hright : ∃ mu, c.right mu) (hroute : PrefixRoute c w) :
    capComponentCovers c w := by
  rcases hroute with ⟨tail, hleft⟩
  refine ⟨tail, w ++ tail, [], by simp, hleft, ?_⟩
  exact Language.nil_mem_cap_of_nonempty c.right hright

theorem splitRoute_capComponentCovers
    (c : CapComponent α) (w : Word α)
    (hroute : SplitRoute c w) :
  capComponentCovers c w := by
  rcases hroute with ⟨j, hj, hleft, hright⟩
  refine ⟨[], ?_⟩
  refine ⟨w.take j, w.drop j, ?_, hleft, ?_⟩
  · simp
  · exact Language.prefixClosure_le_cap c.right _ hright

def PeriodicWitness (c : CapComponent α) (w : Word α) : Prop :=
  ∃ j p e,
    0 < p ∧ 0 < e ∧ j + p + e = w.length ∧
    c.left (w.take j) ∧ c.right (Word.factor w j p) ∧
    Word.WitnessCopy w j p e

def MarkedOccurrence (c : CapComponent α) (w : Word α) : Prop :=
  ∃ j t,
    j < t ∧ t < w.length ∧
    c.left (w.take j) ∧ c.right (Word.factor w j (t - j)) ∧
    OccursSuffixAt w j t

/--
Prefix-context transport of one marked occurrence.  The copied suffix
and right factor transport literally; only acceptance of the enlarged
left prefix is an explicit control obligation.
-/
theorem markedOccurrence_prefix_shift
    (c : CapComponent α) (pre w : Word α)
    (h : MarkedOccurrence c w)
    (hleft :
      ∀ j t, j < t → t < w.length →
        c.left (w.take j) → c.left (pre ++ w.take j)) :
    MarkedOccurrence c (pre ++ w) := by
  obtain ⟨j, t, hjt, ht, hjleft, hjright, hoccurs⟩ := h
  refine ⟨pre.length + j, pre.length + t, by omega, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append]
    omega
  · simpa [List.take_append, Nat.add_sub_cancel_left] using
      hleft j t hjt ht hjleft
  · have hdiff :
        (pre.length + t) - (pre.length + j) = t - j := by omega
    rw [hdiff, Word.factor_prefix_shift]
    exact hjright
  · exact occursSuffixAt_prefix_shift pre w j t hoccurs

/--
Transport of a marked occurrence across an insertion before its source
cut.  Literal factor/copy data shift automatically; acceptance of the
new enlarged left prefix is the only explicit control premise.
-/
theorem markedOccurrence_insertAt_before
    (c : CapComponent α) (w payload : Word α)
    (slot j t : Nat)
    (hslot : slot ≤ j) (hjt : j < t) (ht : t < w.length)
    (hleft :
      c.left ((Word.insertAt w payload slot).take
        (j + payload.length)))
    (hright : c.right (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t) :
    MarkedOccurrence c (Word.insertAt w payload slot) := by
  have hslotlen : slot ≤ w.length := by omega
  refine ⟨j + payload.length, t + payload.length,
    by omega, ?_, hleft, ?_, ?_⟩
  · rw [Word.insertAt_length w payload hslotlen]
    omega
  · have hdiff :
        (t + payload.length) - (j + payload.length) =
          t - j := by omega
    rw [hdiff,
      Word.factor_insertAt_before w payload slot j (t - j)
        hslot (by omega)]
    exact hright
  · exact Word.occursSuffixAt_insertAt_before
      w payload slot j t hslot hjt ht hoccurs

def ComponentNormalForm (c : CapComponent α) (w : Word α) : Prop :=
  PrefixRoute c w ∨ SplitRoute c w ∨ PeriodicWitness c w

/-- The periodic-witness branch of Lemma 1.3 is semantically covered. -/
theorem periodicWitness_capComponentCovers
    (c : CapComponent α) (w : Word α)
    (hwitness : PeriodicWitness c w) :
    capComponentCovers c w := by
  rcases hwitness with
    ⟨j, p, e, hp, he, hlen, hleft, hright, hcopy⟩
  have hperiod : Word.AnchoredPeriod w j p :=
    (Word.witnessCopy_iff_anchoredPeriod w j p e hlen he).1 hcopy
  have hcap : Language.cap c.right (w.drop j) := by
    apply Language.mem_cap_of_period c.right (w.drop j) p hp hperiod
    simpa [Word.factor] using hright
  refine ⟨[], w.take j, w.drop j, by simp, hleft, hcap⟩

/--
Lemma 1.3, componentwise form. Under the nonempty-right-language
preprocessing convention, semantic cap coverage is exactly the three
certificate normal forms.
-/
theorem capComponentCovers_iff_componentNormalForm
    (c : CapComponent α)
    (hrightNonempty : ∃ mu, c.right mu)
    (w : Word α) :
    capComponentCovers c w ↔ ComponentNormalForm c w := by
  constructor
  · rintro ⟨outerTail, x, y, hxy, hx, hycap⟩
    by_cases hwx : w.length ≤ x.length
    · apply Or.inl
      have htake := congrArg (List.take w.length) hxy
      have hxprefix : x.take w.length = w := by
        simpa [List.take_append_of_le_length hwx] using htake.symm
      refine ⟨x.drop w.length, ?_⟩
      have hxdecomp : x = w ++ x.drop w.length := by
        calc
          x = x.take w.length ++ x.drop w.length :=
            (List.take_append_drop w.length x).symm
          _ = w ++ x.drop w.length := by rw [hxprefix]
      rw [← hxdecomp]
      exact hx
    · have hxw : x.length ≤ w.length := by omega
      have htake := congrArg (List.take x.length) hxy
      have hwprefix : w.take x.length = x := by
        simpa [List.take_append_of_le_length hxw] using htake
      have hdrop := congrArg (List.drop x.length) hxy
      have hydecomp : y = w.drop x.length ++ outerTail := by
        simpa [List.drop_append_of_le_length hxw] using hdrop.symm
      have hsuffixCap : Language.cap c.right (w.drop x.length) := by
        apply Language.cap_prefix_closed c.right
        rw [← hydecomp]
        exact hycap
      by_cases hsuffix : w.drop x.length = []
      · apply Or.inr
        apply Or.inl
        refine ⟨x.length, hxw, ?_, ?_⟩
        · simpa [hwprefix] using hx
        · obtain ⟨mu, hmu⟩ := hrightNonempty
          refine ⟨mu, ?_⟩
          simpa [hsuffix] using hmu
      · rcases (Language.mem_cap_iff_prefixOrPeriod
            c.right (w.drop x.length) hsuffix).1 hsuffixCap with
          hsuffixPrefix | ⟨p, hp, hperiod, hroot⟩
        · apply Or.inr
          apply Or.inl
          exact ⟨x.length, hxw, by simpa [hwprefix] using hx,
            hsuffixPrefix⟩
        · apply Or.inr
          apply Or.inr
          let e := (w.drop x.length).length - p
          have hpSuffix : p < (w.drop x.length).length := hperiod.1
          have he : 0 < e := by
            dsimp [e]
            omega
          have hlen : x.length + p + e = w.length := by
            dsimp [e]
            have hsuffixLen :
                (w.drop x.length).length = w.length - x.length := by simp
            omega
          refine ⟨x.length, p, e, hp, he, hlen,
            by simpa [hwprefix] using hx, ?_, ?_⟩
          · simpa [Word.factor] using hroot
          · apply (Word.witnessCopy_iff_anchoredPeriod
              w x.length p e hlen he).2
            exact hperiod
  · rintro (hprefix | hsplit | hperiodic)
    · exact prefixRoute_capComponentCovers c w hrightNonempty hprefix
    · exact splitRoute_capComponentCovers c w hsplit
    · exact periodicWitness_capComponentCovers c w hperiodic

def CertificateUncovered (E : CapExpression α) (w : Word α) : Prop :=
  routeFree E w ∧ ∀ c ∈ E.caps, ¬ ComponentNormalForm c w

/--
The purely logical part of Theorem 9.1. Once Lemma 1.3 supplies the
componentwise equivalence, uncovered words are exactly the certificate-free,
route-free words.
-/
theorem uncovered_iff_certificateUncovered
    (E : CapExpression α)
    (hnf : ∀ c ∈ E.caps, ∀ w, capComponentCovers c w ↔ ComponentNormalForm c w)
    (w : Word α) :
    E.Uncovered w ↔ CertificateUncovered E w := by
  unfold CapExpression.Uncovered CapExpression.Covers CertificateUncovered
  constructor
  · intro h
    have hcap : ¬ capCovered E w := fun hc => h (Or.inl hc)
    have hroute : routeFree E w := fun hr => h (Or.inr hr)
    refine ⟨hroute, ?_⟩
    intro c hc hnormal
    exact hcap ⟨c, hc, (hnf c hc w).2 hnormal⟩
  · rintro ⟨hroute, hnormal⟩ (hcap | hr)
    · rcases hcap with ⟨c, hc, hcovered⟩
      exact hnormal c hc ((hnf c hc w).1 hcovered)
    · exact hroute hr

/--
Theorem 9.1 after empty-right components have been removed. Lemma 1.3 now
supplies the component normal-form equivalence internally, so no external
normal-form hypothesis remains.
-/
theorem uncovered_iff_certificateUncovered_of_nonempty_right
    (E : CapExpression α)
    (hright : ∀ c ∈ E.caps, ∃ mu, c.right mu)
    (w : Word α) :
    E.Uncovered w ↔ CertificateUncovered E w := by
  apply uncovered_iff_certificateUncovered E
  intro c hc v
  exact capComponentCovers_iff_componentNormalForm
    c (hright c hc) v

theorem witnessCopy_iff_occursSuffixAt
    (w : Word α) (j p e : Nat)
    (hp : 0 < p) (he : 0 < e) (hlen : j + p + e = w.length) :
    Word.WitnessCopy w j p e ↔ OccursSuffixAt w j (j + p) := by
  have hjt : j < j + p := by omega
  have ht : j + p < w.length := by omega
  rw [Word.witnessCopy_iff_anchoredPeriod w j p e hlen he]
  rw [occursSuffixAt_iff_anchoredPeriod w j (j + p) hjt ht]
  have hsub : j + p - j = p := by omega
  rw [hsub]

theorem periodicWitness_iff_markedOccurrence
    (c : CapComponent α) (w : Word α) :
    PeriodicWitness c w ↔ MarkedOccurrence c w := by
  constructor
  · rintro ⟨j, p, e, hp, he, hlen, hleft, hright, hcopy⟩
    refine ⟨j, j + p, by omega, by omega, hleft, ?_, ?_⟩
    · simpa [Nat.add_sub_cancel_left] using hright
    · exact (witnessCopy_iff_occursSuffixAt w j p e hp he hlen).1 hcopy
  · rintro ⟨j, t, hjt, ht, hleft, hright, hocc⟩
    let p := t - j
    let e := w.length - t
    have hp : 0 < p := by dsimp [p]; omega
    have he : 0 < e := by dsimp [e]; omega
    have hlen : j + p + e = w.length := by dsimp [p, e]; omega
    refine ⟨j, p, e, hp, he, hlen, hleft, ?_, ?_⟩
    · simpa [p] using hright
    · apply (witnessCopy_iff_occursSuffixAt w j p e hp he hlen).2
      have hjp : j + p = t := by dsimp [p]; omega
      rw [hjp]
      exact hocc

end NSSE
