import NSSE.NonliveBorderRank
import NSSE.FrozenCapRays
import NSSE.PeriodSpectrum
import Mathlib.Algebra.Ring.Periodic

/-!
# Same-anchor short-root replacement on the live part

Choose one bounded-cycle lasso, then one frozen cap ray covering all its
prefixes. No assertion that the entire live graph is forced is needed.
-/

namespace NSSE.LiveShortRoot

open NonliveBorderRank FrozenCapRays

universe u v
variable {α : Type u} {Q : Type v}

/-- The pigeonhole lasso can retain its explicit cycle-length bound. -/
theorem bounded_lasso [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (w : List α) (hw : Live A w) :
    ∃ pre a : List α, w <+: pre ∧ a ≠ [] ∧ a.length ≤ Fintype.card Q ∧
      A.runFrom (A.run pre) a = A.run pre ∧ A.Accepts (pre ++ a) := by
  obtain ⟨tail, hlen, hacc⟩ := (live_iff_extension_length A hpc w).mp hw
  let z := w ++ tail
  let f : Fin (Fintype.card Q + 1) → Q := fun i => A.run (z.take (w.length + i.val))
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have grow : ∀ i j : Fin (Fintype.card Q + 1), i.val < j.val → f i = f j →
      ∃ pre a : List α, w <+: pre ∧ a ≠ [] ∧ a.length ≤ Fintype.card Q ∧
        A.runFrom (A.run pre) a = A.run pre ∧ A.Accepts (pre ++ a) := by
    intro i j hij hstates
    let lo := w.length + i.val
    let hi := w.length + j.val
    let a := (z.drop lo).take (hi - lo)
    have hhi : hi ≤ z.length := by simp only [z, hi, List.length_append, hlen]; omega
    have hlohi : lo < hi := by dsimp [lo, hi]; omega
    have ha : a.length = j.val - i.val := by
      simp only [a, List.length_take, List.length_drop]
      rw [Nat.min_eq_left (by omega)]
      dsimp [hi, lo]
      omega
    have hsplit : z.take lo ++ a = z.take hi := (take_cut_split z hlohi.le).symm
    refine ⟨z.take lo, a, ?_, ?_, ?_, ?_, ?_⟩
    · exact List.prefix_take_iff.mpr ⟨List.prefix_append w tail, by dsimp [lo]; omega⟩
    · apply List.length_pos_iff.mp
      rw [ha]
      omega
    · rw [ha]
      omega
    · rw [← A.run_append, hsplit]
      exact hstates.symm
    · rw [hsplit]
      exact hpc (List.take_prefix hi z) hacc
  have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hneval with hij | hji
  · exact grow i j hij heq
  · exact grow j i hji heq.symm

theorem power_prefix {a : List α} {m n : Nat} (hmn : m ≤ n) :
    Word.power a m <+: Word.power a n := by
  exact ⟨Word.power a (n - m), by rw [← Word.power_add, Nat.add_sub_of_le hmn]⟩

/-- A finite family covering every stage of a nested sequence contains one
member covering ALL stages. This is finite pigeonhole, not infinite compactness. -/
theorem finite_nested_cover {I : Type*} [Fintype I] (P : I → Nat → Prop)
    (hmono : ∀ i m n, m ≤ n → P i n → P i m) (hcover : ∀ n, ∃ i, P i n) :
    ∃ i, ∀ n, P i n := by
  classical
  by_contra h
  push_neg at h
  choose bad hbad using h
  obtain ⟨i, hi⟩ := hcover (Finset.univ.sup bad)
  exact hbad i (hmono i _ _ (Finset.le_sup (Finset.mem_univ i)) hi)

/-- Under live coverage, one original frozen anchor/root covers every stage
of the selected accepting lasso, not a different root at each length. -/
theorem fixed_ray_of_lasso (A : DFA α Q) (E : CapExpression α)
    (hcover : ∀ z, Live A z → capCovered E z)
    (w pre a : List α) (hout : ¬ regularCovered E w)
    (hwpre : w <+: pre) (ha : a ≠ [])
    (hloop : A.runFrom (A.run pre) a = A.run pre) (hacc : A.Accepts (pre ++ a)) :
    ∃ i : Index w, Enabled E w i ∧
      ∀ n, Ray (anchorAt w i) (rootAt w i) (pre ++ Word.power a n) := by
  have hpre : A.Accepts pre := by simpa only [DFA.Accepts, A.run_append, hloop] using hacc
  have hlive : ∀ n, Live A (pre ++ Word.power a n) := by
    intro n
    apply live_of_lasso A
    refine ⟨pre ++ Word.power a n, a, ⟨[], by simp⟩, ha, ?_, ?_⟩
    · rw [A.run_append, runFrom_power_loop A _ a hloop]
      exact hloop
    · change A.accept (A.run ((pre ++ Word.power a n) ++ a))
      rw [A.run_append, A.run_append, runFrom_power_loop A _ a hloop, hloop]
      exact hpre
  have heach : ∀ n, ∃ i : Index w, Enabled E w i ∧
      Ray (anchorAt w i) (rootAt w i) (pre ++ Word.power a n) := by
    intro n
    exact (covered_extension_iff E w _ hout
      (hwpre.trans (List.prefix_append pre _))).mp (hcover _ (hlive n))
  obtain ⟨i, hi⟩ := finite_nested_cover
    (fun i n => Enabled E w i ∧ Ray (anchorAt w i) (rootAt w i) (pre ++ Word.power a n))
    (by
      intro i m n hmn hn
      exact ⟨hn.1, ray_prefix ((List.prefix_append_right_inj pre).mpr (power_prefix hmn)) hn.2⟩)
    heach
  exact ⟨i, (hi 0).1, fun n => (hi n).2⟩

/-- A positive accepted power has a positive accepted exponent no larger
than the number of DFA states, including when the initial state is final. -/
theorem short_positive_power [Fintype Q] (B : DFA α Q) (a : List α)
    (hex : ∃ n, 0 < n ∧ B.Accepts (Word.power a n)) :
    ∃ n, 0 < n ∧ n ≤ Fintype.card Q ∧ B.Accepts (Word.power a n) := by
  classical
  let k := Nat.find hex
  have hk : 0 < k ∧ B.Accepts (Word.power a k) := Nat.find_spec hex
  have hinj : Function.Injective (fun i : Fin k => B.run (Word.power a (i.val + 1))) := by
    intro i j heq
    have cannot : ∀ i j : Fin k, i.val < j.val →
        B.run (Word.power a (i.val + 1)) = B.run (Word.power a (j.val + 1)) → False := by
      intro i j hij hstate
      let rest := k - (j.val + 1)
      have hkform : j.val + 1 + rest = k := by dsimp [rest]; omega
      have hshort : i.val + 1 + rest < k := by omega
      have hrun : B.run (Word.power a (i.val + 1 + rest)) = B.run (Word.power a k) := by
        rw [Word.power_add, B.run_append, hstate, ← B.run_append, ← Word.power_add, hkform]
      have haccept : B.Accepts (Word.power a (i.val + 1 + rest)) := by
        change B.accept (B.run _)
        rw [hrun]
        exact hk.2
      exact Nat.find_min hex hshort ⟨by omega, haccept⟩
    by_contra hne
    have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hneval with hij | hji
    · exact cannot i j hij heq
    · exact cannot j i hji heq.symm
  refine ⟨k, hk.1, ?_, hk.2⟩
  simpa using Fintype.card_le_of_injective _ hinj

/-- Optional lookup avoids assuming that the alphabet is inhabited. -/
def letter (r : List α) (i : Nat) : Option α := r[i % r.length]?

theorem letter_period (r : List α) : Function.Periodic (letter r) r.length := by
  intro i
  simp [letter]

theorem power_lookup (r : List α) (n i : Nat) (hi : i < (Word.power r n).length) :
    (Word.power r n)[i]? = letter r i := by
  induction n generalizing i with
  | zero => simp at hi
  | succ n ih =>
      rw [Word.power_succ]
      by_cases hir : i < r.length
      · rw [List.getElem?_append_left hir]
        simp [letter, Nat.mod_eq_of_lt hir]
      · have hle : r.length ≤ i := by omega
        rw [List.getElem?_append_right hle]
        have ht : i - r.length < (Word.power r n).length := by
          simp only [Word.power_succ, List.length_append] at hi
          omega
        rw [ih _ ht]
        unfold letter
        have heq : i = (i - r.length) + r.length := by omega
        conv_rhs => rw [heq, Nat.add_mod_right]

theorem prefix_lookup {x y : List α} (hxy : x <+: y) (i : Nat) (hi : i < x.length) :
    x[i]? = y[i]? := by
  obtain ⟨tail, rfl⟩ := hxy
  exact (List.getElem?_append_left hi).symm

theorem ray_lookup {anchor root x : List α} (hx : Ray anchor root x)
    (i : Nat) (hi : anchor.length + i < x.length) :
    x[anchor.length + i]? = letter root i := by
  obtain ⟨k, hk⟩ := hx
  rw [language_wordPower_eq_word_power] at hk
  have hlen := hk.length_le
  rw [prefix_lookup hk _ hi, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact power_lookup root k i (by simp only [List.length_append] at hlen; omega)

/-- Equality of arbitrarily long finite prefixes identifies the periodic
tails, with the original anchor offset recorded explicitly. -/
theorem lasso_letter_eq (anchor root pre a : List α) (ha : a ≠ [])
    (hle : anchor.length ≤ pre.length)
    (hall : ∀ n, Ray anchor root (pre ++ Word.power a n)) (i : Nat) :
    letter root (pre.length - anchor.length + i) = letter a i := by
  have hap : 0 < a.length := List.length_pos_iff.mpr ha
  have hi : i < (Word.power a (i + 1)).length := by
    rw [Word.power_length]
    have := Nat.le_mul_of_pos_right (i + 1) hap
    omega
  have hr := ray_lookup (hall (i + 1)) (pre.length - anchor.length + i)
    (by simp only [List.length_append]; omega)
  have hoff : anchor.length + (pre.length - anchor.length + i) = pre.length + i := by omega
  rw [hoff, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hr
  exact hr.symm.trans (power_lookup a (i + 1) i hi)

theorem period_of_eventual {β : Type*} (f : Nat → β) {p d cutoff : Nat}
    (hp : 0 < p) (hperiod : Function.Periodic f p)
    (htail : ∀ i, cutoff ≤ i → f (i + d) = f i) : Function.Periodic f d := by
  intro i
  have hshift : cutoff ≤ i + (cutoff + 1) * p := by
    have := Nat.le_mul_of_pos_right (cutoff + 1) hp
    omega
  have h := htail (i + (cutoff + 1) * p) hshift
  rw [show i + (cutoff + 1) * p + d = (i + d) + (cutoff + 1) * p by omega] at h
  have h₁ : f ((i + d) + (cutoff + 1) * p) = f (i + d) := by
    simpa using hperiod.nat_mul (cutoff + 1) (i + d)
  have h₂ : f (i + (cutoff + 1) * p) = f i := by
    simpa using hperiod.nat_mul (cutoff + 1) i
  exact h₁.symm.trans (h.trans h₂)

theorem root_period_of_lasso (anchor root pre a : List α)
    (hr : root ≠ []) (ha : a ≠ []) (hle : anchor.length ≤ pre.length)
    (hall : ∀ n, Ray anchor root (pre ++ Word.power a n)) :
    Function.Periodic (letter root) a.length := by
  apply period_of_eventual (letter root) (List.length_pos_iff.mpr hr) (letter_period root)
    (cutoff := pre.length - anchor.length)
  intro i hi
  have h₁ := lasso_letter_eq anchor root pre a ha hle hall (i - (pre.length - anchor.length))
  have h₂ := lasso_letter_eq anchor root pre a ha hle hall
    (i - (pre.length - anchor.length) + a.length)
  have heq : pre.length - anchor.length + (i - (pre.length - anchor.length)) = i := by omega
  rw [← Nat.add_assoc, heq, letter_period a] at h₂
  rw [heq] at h₁
  exact h₂.trans h₁.symm

theorem power_hasPeriod (r : List α) (n d : Nat)
    (hperiod : Function.Periodic (letter r) d) (hd : d < (Word.power r n).length) :
    Word.HasPeriod (Word.power r n) d := by
  refine ⟨hd, ?_⟩
  unfold Word.factor
  simp only [List.drop_zero]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < (Word.power r n).length - d
  · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi, List.getElem?_drop]
    rw [power_lookup r n i (by omega), power_lookup r n (d + i) (by omega)]
    simpa only [Nat.add_comm] using (hperiod i).symm
  · simp only [List.getElem?_take, if_neg hi]

/-- A pure periodic ray with another positive period has a same-alignment
root no longer than that period. The proof uses finite word commutation. -/
theorem short_root_of_period (r : List α) (hr : r ≠ []) (d : Nat) (hd : 0 < d)
    (hperiod : Function.Periodic (letter r) d) :
    ∃ v m, v ≠ [] ∧ 0 < m ∧ v.length ≤ d ∧ r = Word.power v m := by
  by_cases hrd : r.length ≤ d
  · exact ⟨r, 1, hr, by omega, hrd, by simp⟩
  have hpos : 0 < r.length := List.length_pos_iff.mpr hr
  have hdr : d < r.length := by omega
  let z := Word.power r 2
  have hz : z.length = 2 * r.length := Word.power_length r 2
  have hp : Word.HasPeriod z r.length :=
    power_hasPeriod r 2 r.length (letter_period r) (by rw [Word.power_length]; omega)
  have hq : Word.HasPeriod z d := power_hasPeriod r 2 d hperiod (by rw [Word.power_length]; omega)
  have hcomm := Word.periodRoots_commute z r.length d hp hq (by omega)
  have htake : z.take r.length = r := by simp [z, Word.power_succ]
  have hsmall : z.take d = r.take d := by
    simp only [z, Word.power_succ]
    exact List.take_append_of_le_length hdr.le
  rw [htake, hsmall] at hcomm
  obtain ⟨v, m, n, hrpow, hdpow⟩ := (Word.commute_iff_common_power r (r.take d)).mp hcomm
  have hv : v ≠ [] := by intro hnil; exact hr (by simpa [hnil] using hrpow)
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm
    exact hr (by simpa [hm] using hrpow)
  have hlength := congrArg List.length hdpow
  simp only [List.length_take, Nat.min_eq_left hdr.le, Word.power_length] at hlength
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    rw [hn, Nat.zero_mul] at hlength
    omega
  refine ⟨v, m, hv, hm, ?_, hrpow⟩
  rw [hlength]
  exact Nat.le_mul_of_pos_left v.length hn

/-- Positive powers define exactly the same anchored ray. -/
theorem ray_power_iff (anchor v : List α) (q : Nat) (hq : 0 < q) (w : List α) :
    Ray anchor (Word.power v q) w ↔ Ray anchor v w := by
  unfold Ray
  simp only [language_wordPower_eq_word_power, Word.power_power]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨q * n, hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, hn.trans ((List.prefix_append_right_inj anchor).mpr (power_prefix ?_))⟩
    exact Nat.le_mul_of_pos_left n hq

/-- The original accepted root is replaced at the SAME anchor by a shorter
accepted root defining exactly the SAME ray on all finite words. -/
theorem same_anchor_short_root [Fintype Q] (B : DFA α Q)
    (anchor root pre a : List α) (hr : root ≠ []) (ha : a ≠ [])
    (hle : anchor.length ≤ pre.length)
    (hall : ∀ n, Ray anchor root (pre ++ Word.power a n)) (haccept : B.Accepts root) :
    ∃ root' : List α, root' ≠ [] ∧ root'.length ≤ a.length * Fintype.card Q ∧
      B.Accepts root' ∧ ∀ w, Ray anchor root w ↔ Ray anchor root' w := by
  obtain ⟨v, m, hv, hm, hvlen, hrpow⟩ := short_root_of_period root hr a.length
    (List.length_pos_iff.mpr ha) (root_period_of_lasso anchor root pre a hr ha hle hall)
  obtain ⟨q, hq, hqb, hqacc⟩ := short_positive_power B v ⟨m, hm, by rwa [← hrpow]⟩
  refine ⟨Word.power v q, ?_, ?_, hqacc, ?_⟩
  · apply List.length_pos_iff.mp
    rw [Word.power_length]
    exact Nat.mul_pos hq (List.length_pos_iff.mpr hv)
  · rw [Word.power_length, Nat.mul_comm q v.length]
    exact Nat.mul_le_mul hvlen hqb
  · intro w
    rw [hrpow, ray_power_iff anchor v m hm, ray_power_iff anchor v q hq]

/-- Concrete finite automata for the original root languages, indexed by
the original finite component list. No language-decision oracle is supplied. -/
structure RootPresentation (E : CapExpression α) where
  states : Fin E.caps.length → Nat
  dfa : (i : Fin E.caps.length) → DFA α (Fin (states i))
  correct : ∀ i w, (E.caps.get i).right w ↔ (dfa i).Accepts w

def rootBound {E : CapExpression α} (F : RootPresentation E) : Nat := Finset.univ.sup F.states

theorem states_le_rootBound {E : CapExpression α} (F : RootPresentation E) (i : Fin E.caps.length) :
    F.states i ≤ rootBound F := Finset.le_sup (Finset.mem_univ i)

/-- The paper's regular bounded-root approximation, stated first at the
literal original-cap semantics. -/
def BoundedCovered (E : CapExpression α) (bound : Nat) (w : List α) : Prop :=
  regularCovered E w ∨ ∃ c ∈ E.caps, ∃ anchor root : List α,
    c.left anchor ∧ c.right root ∧ root ≠ [] ∧ root.length ≤ bound ∧ Ray anchor root w

theorem boundedCovered_le_capCovered (E : CapExpression α)
    (hne : ∀ c ∈ E.caps, ∃ root, c.right root) (bound : Nat) (w : List α)
    (hw : BoundedCovered E bound w) : capCovered E w := by
  rcases hw with hreg | ⟨c, hc, anchor, root, hleft, hright, _, _, hray⟩
  · exact regularCovered_le_capCovered E hne w hreg
  · exact ⟨c, hc, (capComponentCovers_iff_ray c w).mpr ⟨anchor, root, hleft, hright, hray⟩⟩

/-- The full live short-root implication, with an explicit computable
bound from the candidate DFA and the supplied root DFAs. -/
theorem live_bounded_covered [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (E : CapExpression α) (F : RootPresentation E)
    (hcover : ∀ z, Live A z → capCovered E z) (w : List α) (hw : Live A w) :
    BoundedCovered E (Fintype.card Q * rootBound F) w := by
  classical
  by_cases hreg : regularCovered E w
  · exact Or.inl hreg
  obtain ⟨pre, a, hwpre, ha, habound, hloop, hacc⟩ := bounded_lasso A hpc w hw
  obtain ⟨i, hi, hall⟩ := fixed_ray_of_lasso A E hcover w pre a hreg hwpre ha hloop hacc
  obtain ⟨c, hc, hleft, hright⟩ := hi.2.2.1
  obtain ⟨ci, rfl⟩ := List.mem_iff_get.mp hc
  have hroot : rootAt w i ≠ [] := enabled_root_ne_nil E w i hi
  have hanchor : (anchorAt w i).length ≤ pre.length := by
    simp only [anchorAt, List.length_take]
    exact (Nat.min_le_right _ _).trans hwpre.length_le
  obtain ⟨root', hr', hbound, haccept, hray⟩ := same_anchor_short_root (F.dfa ci)
    (anchorAt w i) (rootAt w i) pre a hroot ha hanchor hall ((F.correct ci _).mp hright)
  refine Or.inr ⟨E.caps.get ci, List.get_mem _ _, anchorAt w i, root', hleft,
    (F.correct ci _).mpr haccept, hr', ?_, (hray w).mp hi.2.2.2⟩
  simp only [Fintype.card_fin] at hbound
  exact hbound.trans (Nat.mul_le_mul habound (states_le_rootBound F ci))

/-- Exact live inclusion criterion. Nonempty root-language preprocessing
is used only for R ⊆ P, not for the forward short-root construction. -/
theorem live_covered_iff_bounded [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (E : CapExpression α) (F : RootPresentation E)
    (hne : ∀ c ∈ E.caps, ∃ root, c.right root) :
    (∀ w, Live A w → capCovered E w) ↔
      ∀ w, Live A w → BoundedCovered E (Fintype.card Q * rootBound F) w := by
  constructor
  · intro h w hw
    exact live_bounded_covered A hpc E F h w hw
  · intro h w hw
    exact boundedCovered_le_capCovered E hne _ w (h w hw)

/-- Failure of bounded inclusion certifies existence of a genuine live
avoider. It does NOT assert that a word outside the bounded approximation
is itself uncovered by all longer original roots. -/
theorem live_counterexample_iff [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (E : CapExpression α) (F : RootPresentation E)
    (hne : ∀ c ∈ E.caps, ∃ root, c.right root) :
    (∃ w, Live A w ∧ ¬ capCovered E w) ↔
      ¬ ∀ w, Live A w → BoundedCovered E (Fintype.card Q * rootBound F) w := by
  classical
  rw [← live_covered_iff_bounded A hpc E F hne]
  simp only [not_forall, _root_.not_imp, exists_prop]

end NSSE.LiveShortRoot
