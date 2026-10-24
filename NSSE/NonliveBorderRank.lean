import NSSE.Automata
import NSSE.Commutation
import NSSE.TerminalBorderRank
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn

/-!
# DFA nonlive words have bounded suffix-border rank

The rank is the exact cardinal rank from `TerminalBorderRank`. A live word
has accepted extensions of arbitrarily large length. This module derives
the rank promise from finite accepting control, not from a supplied bound.
-/

namespace NSSE.NonliveBorderRank

universe u v
variable {α : Type u} {Q : Type v}

open TerminalBorderRank

def PrefixClosed (A : DFA α Q) : Prop :=
  ∀ ⦃x y : List α⦄, x <+: y → A.Accepts y → A.Accepts x

/-- Accepted extensions of arbitrarily large length. -/
def Live (A : DFA α Q) (w : List α) : Prop :=
  ∀ n : Nat, ∃ z : List α, w <+: z ∧ n ≤ z.length ∧ A.Accepts z

theorem prefix_power_append {a b : List α} (h : b <+: a ++ b) (n : Nat) :
    b <+: Word.power a n ++ b := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hlift := (List.prefix_append_right_inj a).mpr ih
      simpa only [Word.power_succ, List.append_assoc] using h.trans hlift

theorem prefix_power {a b : List α} (h : b <+: a ++ b) (n : Nat)
    (hlen : b.length ≤ n * a.length) : b <+: Word.power a n := by
  apply (List.isPrefix_append_of_length (by simpa [Word.power_length] using hlen)).mp
  exact prefix_power_append h n

theorem runFrom_power_loop (A : DFA α Q) (q : Q) (a : List α)
    (hloop : A.runFrom q a = q) (n : Nat) : A.runFrom q (Word.power a n) = q := by
  induction n with
  | zero => simp
  | succ n ih => simp [Word.power_succ, A.runFrom_append, hloop, ih]

/-- A repeated control state at nested-border cuts makes the WHOLE word live. -/
theorem live_of_nested_loop (A : DFA α Q) (pre a b : List α)
    (ha : a ≠ []) (hprefix : b <+: a ++ b)
    (hloop : A.runFrom (A.run pre) a = A.run pre) (hacc : A.Accepts pre) :
    Live A (pre ++ a ++ b) := by
  have hapos : 0 < a.length := List.length_pos_iff.mpr ha
  intro n
  let k := n + b.length
  have hk : k ≤ k * a.length := Nat.le_mul_of_pos_right k hapos
  have hbp : b <+: Word.power a k := prefix_power hprefix k (by dsimp [k] at hk ⊢; omega)
  refine ⟨pre ++ Word.power a (k + 1), ?_, ?_, ?_⟩
  · have hleft := (List.prefix_append_right_inj (pre ++ a)).mpr hbp
    simpa only [Word.power_succ, List.append_assoc] using hleft
  · simp only [List.length_append, Word.power_length]
    have hk' : k + 1 ≤ (k + 1) * a.length := Nat.le_mul_of_pos_right (k + 1) hapos
    dsimp [k] at *
    omega
  · change A.accept (A.run (pre ++ Word.power a (k + 1)))
    rw [A.run_append, runFrom_power_loop A (A.run pre) a hloop]
    exact hacc

theorem take_cut_split (w : List α) {i j : Nat} (hij : i ≤ j) :
    w.take j = w.take i ++ (w.drop i).take (j - i) := by
  have h := List.take_append_drop i (w.take j)
  simpa [List.take_take, Nat.min_eq_left hij, List.drop_take] using h.symm

/-- Nested suffix cuts at the same DFA state force liveness of the whole word. -/
theorem live_of_equal_nested_cuts (A : DFA α Q) (hpc : PrefixClosed A)
    (w : List α) (hw : A.Accepts w) (i j : Nat) (hij : i < j) (hj : j ≤ w.length)
    (heq : A.run (w.take i) = A.run (w.take j))
    (hnested : w.drop j <+: w.drop i) : Live A w := by
  let pre := w.take i
  let a := (w.drop i).take (j - i)
  let b := w.drop j
  have hdrop : w.drop i = a ++ b := by
    have h := List.take_append_drop (j - i) (w.drop i)
    have hoff : i + (j - i) = j := by omega
    simpa only [a, b, List.drop_drop, hoff] using h.symm
  have hword : pre ++ a ++ b = w := by
    rw [List.append_assoc, ← hdrop]
    exact List.take_append_drop i w
  have ha : a ≠ [] := by
    have hlen : a.length = j - i := by
      simp [a, Nat.min_eq_left (show j - i ≤ w.length - i by omega)]
    exact List.length_pos_iff.mp (by omega)
  have hpre : A.Accepts pre := hpc (List.take_prefix i w) hw
  have hloop : A.runFrom (A.run pre) a = A.run pre := by
    rw [← A.run_append]
    exact (congrArg A.run (take_cut_split w hij.le).symm).trans heq.symm
  have hnest : b <+: a ++ b := by simpa only [b, ← hdrop] using hnested
  have hlive := live_of_nested_loop A pre a b ha hnest hloop hpre
  rwa [hword] at hlive

theorem live_mono (A : DFA α Q) {w z : List α} (hwz : w <+: z) (hz : Live A z) :
    Live A w := by
  intro n
  obtain ⟨v, hzv, hlen, hv⟩ := hz n
  exact ⟨v, hwz.trans hzv, hlen, hv⟩

/-- A finite accepting loop certificate ahead of the given word. -/
def HasLasso (A : DFA α Q) (w : List α) : Prop :=
  ∃ pre a : List α, w <+: pre ∧ a ≠ [] ∧
    A.runFrom (A.run pre) a = A.run pre ∧ A.Accepts (pre ++ a)

theorem live_of_lasso (A : DFA α Q) {w : List α} (h : HasLasso A w) : Live A w := by
  obtain ⟨pre, a, hwpre, ha, hloop, hacc⟩ := h
  have hpre : A.Accepts pre := by
    simpa only [DFA.Accepts, A.run_append, hloop] using hacc
  have hp : ([] : List α) <+: a ++ [] := List.nil_prefix
  have hlive := live_of_nested_loop A pre a [] ha hp hloop hpre
  apply live_mono A (hwpre.trans (List.prefix_append pre a))
  simpa only [List.append_nil] using hlive

theorem lasso_of_equal_cuts (A : DFA α Q) (hpc : PrefixClosed A)
    (v w : List α) (hv : A.Accepts v) (i j : Nat) (hij : i < j) (hj : j ≤ v.length)
    (hwpre : w <+: v.take i) (heq : A.run (v.take i) = A.run (v.take j)) :
    HasLasso A w := by
  let a := (v.drop i).take (j - i)
  have hsplit : v.take i ++ a = v.take j := (take_cut_split v hij.le).symm
  have ha : a ≠ [] := by
    have hlen : a.length = j - i := by
      simp [a, Nat.min_eq_left (show j - i ≤ v.length - i by omega)]
    exact List.length_pos_iff.mp (by omega)
  refine ⟨v.take i, a, hwpre, ha, ?_, ?_⟩
  · rw [← A.run_append, hsplit]
    exact heq.symm
  · rw [hsplit]
    exact hpc (List.take_prefix j v) hv

/-- A long enough accepted extension supplies a genuine reachable accepting loop. -/
theorem lasso_of_long_extension [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (w tail : List α) (hlen : Fintype.card Q ≤ tail.length)
    (hacc : A.Accepts (w ++ tail)) : HasLasso A w := by
  let f : Fin (Fintype.card Q + 1) → Q :=
    fun i => A.run ((w ++ tail).take (w.length + i.val))
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have grow : ∀ (i j : Fin (Fintype.card Q + 1)), i.val < j.val → f i = f j →
      HasLasso A w := by
    intro i j hij hstates
    have hi := i.isLt
    have hj := j.isLt
    apply lasso_of_equal_cuts A hpc (w ++ tail) w hacc
      (w.length + i.val) (w.length + j.val) (by omega) _ _ hstates
    · simp only [List.length_append]
      omega
    · apply List.prefix_take_iff.mpr
      exact ⟨List.prefix_append w tail, by omega⟩
  have hneval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hneval with hij | hji
  · exact grow i j hij heq
  · exact grow j i hji heq.symm

/-- For prefix-closed finite-state languages, one fixed extension length suffices. -/
theorem live_iff_extension_length [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (w : List α) : Live A w ↔
      ∃ tail : List α, tail.length = Fintype.card Q ∧ A.Accepts (w ++ tail) := by
  constructor
  · intro hlive
    obtain ⟨z, ⟨tail, rfl⟩, hlen, hacc⟩ := hlive (w.length + Fintype.card Q)
    have htail : Fintype.card Q ≤ tail.length := by
      simp only [List.length_append] at hlen
      omega
    refine ⟨tail.take (Fintype.card Q), by simp [Nat.min_eq_left htail], ?_⟩
    exact hpc ((List.prefix_append_right_inj w).mpr (List.take_prefix _ tail)) hacc
  · rintro ⟨tail, hlen, hacc⟩
    exact live_of_lasso A (lasso_of_long_extension A hpc w tail hlen.ge hacc)

theorem live_iff_lasso [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (w : List α) : Live A w ↔ HasLasso A w := by
  constructor
  · intro hlive
    obtain ⟨tail, hlen, hacc⟩ := (live_iff_extension_length A hpc w).mp hlive
    exact lasso_of_long_extension A hpc w tail hlen.ge hacc
  · exact live_of_lasso A

/-- The loop certificate describes compatible, arbitrarily long accepted
prefixes of one periodic continuation, not unrelated finite branches. -/
theorem lasso_power_prefixes (A : DFA α Q) (hpc : PrefixClosed A)
    {w : List α} (h : HasLasso A w) :
    ∃ pre a : List α, w <+: pre ∧ a ≠ [] ∧
      ∀ n : Nat, ∀ z : List α, z <+: pre ++ Word.power a n → A.Accepts z := by
  obtain ⟨pre, a, hwpre, ha, hloop, hacc⟩ := h
  have hpre : A.Accepts pre := by
    simpa only [DFA.Accepts, A.run_append, hloop] using hacc
  refine ⟨pre, a, hwpre, ha, ?_⟩
  intro n z hz
  apply hpc hz
  change A.accept (A.run (pre ++ Word.power a n))
  rw [A.run_append, runFrom_power_loop A (A.run pre) a hloop]
  exact hpre

theorem live_iff_extension_function [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (w : List α) : Live A w ↔
      ∃ f : Fin (Fintype.card Q) → α, A.Accepts (w ++ List.ofFn f) := by
  rw [live_iff_extension_length A hpc w]
  constructor
  · rintro ⟨tail, hlen, hacc⟩
    have hex : ∃ f : Fin tail.length → α, List.ofFn f = tail :=
      ⟨tail.get, List.ofFn_get tail⟩
    rw [hlen] at hex
    obtain ⟨f, hf⟩ := hex
    exact ⟨f, by simpa only [hf] using hacc⟩
  · rintro ⟨f, hf⟩
    exact ⟨List.ofFn f, List.length_ofFn, hf⟩

/-- The ordinary DFA for the live language: only its accepting set changes. -/
def liveDFA [Fintype Q] (A : DFA α Q) : DFA α Q where
  start := A.start
  step := A.step
  accept := fun q => ∃ f : Fin (Fintype.card Q) → α,
    A.accept (A.runFrom q (List.ofFn f))

theorem liveDFA_accepts_iff [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (w : List α) : (liveDFA A).Accepts w ↔ Live A w := by
  rw [live_iff_extension_function A hpc w]
  change (∃ f : Fin (Fintype.card Q) → α, A.accept (A.runFrom (A.run w) (List.ofFn f))) ↔ _
  simp only [DFA.Accepts, A.run_append]

instance liveDFA_decidableAccept [Fintype α] [DecidableEq α] [Fintype Q]
    (A : DFA α Q) [DecidablePred A.accept] : DecidablePred (liveDFA A).accept :=
  fun q => inferInstanceAs (Decidable (∃ f : Fin (Fintype.card Q) → α,
    A.accept (A.runFrom q (List.ofFn f))))

def liveTest [Fintype α] [DecidableEq α] [Fintype Q] (A : DFA α Q)
    [DecidablePred A.accept] (w : List α) : Bool :=
  decide ((liveDFA A).accept ((liveDFA A).run w))

theorem liveTest_correct [Fintype α] [DecidableEq α] [Fintype Q] (A : DFA α Q)
    [DecidablePred A.accept] (hpc : PrefixClosed A) (w : List α) :
    liveTest A w = true ↔ Live A w := by
  simp only [liveTest, decide_eq_true_eq]
  exact liveDFA_accepts_iff A hpc w

theorem liveDFA_prefixClosed [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A) :
    PrefixClosed (liveDFA A) := by
  intro w z hwz hz
  exact (liveDFA_accepts_iff A hpc w).mpr
    (live_mono A hwz ((liveDFA_accepts_iff A hpc z).mp hz))

/-- The regular nonlive candidate, before subtracting any other regular routes. -/
def nonliveDFA [Fintype Q] (A : DFA α Q) : DFA α Q where
  start := A.start
  step := A.step
  accept := fun q => A.accept q ∧ ¬ (liveDFA A).accept q

theorem nonliveDFA_accepts_iff [Fintype Q] (A : DFA α Q) (hpc : PrefixClosed A)
    (w : List α) : (nonliveDFA A).Accepts w ↔ A.Accepts w ∧ ¬ Live A w := by
  change (A.Accepts w ∧ ¬ (liveDFA A).Accepts w) ↔ _
  rw [liveDFA_accepts_iff A hpc w]

instance nonliveDFA_decidableAccept [Fintype α] [DecidableEq α] [Fintype Q]
    (A : DFA α Q) [DecidablePred A.accept] : DecidablePred (nonliveDFA A).accept :=
  fun q => inferInstanceAs (Decidable (A.accept q ∧ ¬ (liveDFA A).accept q))

variable [DecidableEq α]

/-- All border lengths, including the full word and the empty border. -/
def allBorderLengths (w : List α) : Finset Nat :=
  insert 0 (insert w.length (properBorderLengths w))

theorem mem_allBorderLengths {w : List α} {b : Nat} :
    b ∈ allBorderLengths w ↔ b ≤ w.length ∧ Word.BorderCopy w b := by
  constructor
  · intro hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · simp [Word.BorderCopy, Word.«prefix», Word.suffix]
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · simp [Word.BorderCopy, Word.«prefix», Word.suffix]
      · obtain ⟨_, hlt, hcopy⟩ := mem_properBorderLengths.mp hb
        exact ⟨hlt.le, hcopy⟩
  · rintro ⟨hle, hcopy⟩
    by_cases hzero : b = 0
    · simp [allBorderLengths, hzero]
    by_cases hfull : b = w.length
    · simp [allBorderLengths, hfull]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact mem_properBorderLengths.mpr ⟨by omega, by omega, hcopy⟩

theorem allBorderLengths_card (w : List α) (hw : w ≠ []) :
    (allBorderLengths w).card = borderCount w + 2 := by
  have hlen : w.length ∉ properBorderLengths w := by
    intro h
    have := (mem_properBorderLengths.mp h).2.1
    omega
  have hzero : 0 ∉ insert w.length (properBorderLengths w) := by
    intro h
    rcases Finset.mem_insert.mp h with heq | h
    · have := List.length_pos_iff.mpr hw
      omega
    · have := (mem_properBorderLengths.mp h).1
      omega
  rw [allBorderLengths, Finset.card_insert_of_not_mem hzero,
    Finset.card_insert_of_not_mem hlen]
  rfl

theorem drop_at_border {z w : List α} (hz : z <:+ w) {b : Nat}
    (hb : b ∈ allBorderLengths z) : w.drop (w.length - b) = z.take b := by
  obtain ⟨hble, hcopy⟩ := mem_allBorderLengths.mp hb
  have hzw := hz.length_le
  have hzeq := List.suffix_iff_eq_drop.mp hz
  change z.take b = z.drop (z.length - b) at hcopy
  calc
    w.drop (w.length - b) = (w.drop (w.length - z.length)).drop (z.length - b) := by
      rw [List.drop_drop]
      congr 1
      omega
    _ = z.drop (z.length - b) := by rw [← hzeq]
    _ = z.take b := hcopy.symm

theorem border_states_ne (A : DFA α Q) (hpc : PrefixClosed A)
    {w z : List α} (hw : A.Accepts w) (hnonlive : ¬ Live A w) (hz : z <:+ w)
    {small large : Nat} (hs : small ∈ allBorderLengths z)
    (hl : large ∈ allBorderLengths z) (hsl : small < large) :
    A.run (w.take (w.length - small)) ≠ A.run (w.take (w.length - large)) := by
  intro heq
  have hslen := (mem_allBorderLengths.mp hs).1
  have hllen := (mem_allBorderLengths.mp hl).1
  have hzw := hz.length_le
  apply hnonlive
  apply live_of_equal_nested_cuts A hpc w hw (w.length - large) (w.length - small)
    (by omega) (by omega) heq.symm
  rw [drop_at_border hz hs, drop_at_border hz hl]
  exact List.take_prefix_take_left hsl.le

/-- Each nonempty suffix contributes its proper borders and two endpoints
as DISTINCT accepting DFA states. -/
theorem borderCount_add_two_le_states (A : DFA α Q) (hpc : PrefixClosed A)
    (states : Finset Q) (hstates : ∀ x, A.Accepts x → A.run x ∈ states)
    {w z : List α} (hw : A.Accepts w) (hnonlive : ¬ Live A w)
    (hz : z <:+ w) (hzpos : z ≠ []) : borderCount z + 2 ≤ states.card := by
  let f := fun b => A.run (w.take (w.length - b))
  have hf : ∀ b ∈ allBorderLengths z, f b ∈ states := by
    intro b _
    exact hstates _ (hpc (List.take_prefix (w.length - b) w) hw)
  have hinj : Set.InjOn f (allBorderLengths z) := by
    intro i hi j hj heq
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim (border_states_ne A hpc hw hnonlive hz hi hj hij heq)
    · exact hij
    · exact False.elim (border_states_ne A hpc hw hnonlive hz hj hi hij heq.symm)
  have hcard := Finset.card_le_card_of_injOn f hf hinj
  rwa [allBorderLengths_card z hzpos] at hcard

/-- The nonlive rank bound is derived from accepting control, with no
short-word or rank-bound premise. Empty suffixes are handled separately. -/
theorem nonlive_rank_le_states_sub_two (A : DFA α Q) (hpc : PrefixClosed A)
    (states : Finset Q) (hstates : ∀ x, A.Accepts x → A.run x ∈ states)
    {w : List α} (hw : A.Accepts w) (hnonlive : ¬ Live A w) :
    suffixBorderRank w ≤ states.card - 2 := by
  apply Finset.sup_le
  intro j _
  by_cases hz : w.drop j = []
  · simp [hz]
  · have hbound := borderCount_add_two_le_states A hpc states hstates hw hnonlive
      (List.drop_suffix j w) hz
    omega

/-- A concrete, input-only envelope; unreachable accepting states are harmless. -/
def acceptingStates [Fintype Q] (A : DFA α Q) [DecidablePred A.accept] : Finset Q :=
  Finset.univ.filter A.accept

theorem nonlive_rank_le_accepting_states [Fintype Q] (A : DFA α Q)
    [DecidablePred A.accept] (hpc : PrefixClosed A) {w : List α}
    (hw : A.Accepts w) (hnonlive : ¬ Live A w) :
    suffixBorderRank w ≤ (acceptingStates A).card - 2 := by
  apply nonlive_rank_le_states_sub_two A hpc (acceptingStates A) _ hw hnonlive
  intro x hx
  simpa [acceptingStates, DFA.Accepts] using hx

/-- The constructed regular candidate automatically satisfies the rank promise.
On a finite alphabet its accepting predicate is computable; the rank theorem
itself also holds over infinite alphabets with decidable equality. -/
theorem nonliveDFA_rank_bound [Fintype Q] (A : DFA α Q)
    [DecidablePred A.accept] (hpc : PrefixClosed A) (w : List α)
    (hw : (nonliveDFA A).Accepts w) :
    suffixBorderRank w ≤ (acceptingStates A).card - 2 := by
  obtain ⟨hacc, hnonlive⟩ := (nonliveDFA_accepts_iff A hpc w).mp hw
  exact nonlive_rank_le_accepting_states A hpc hacc hnonlive

theorem rank_bound_of_liveTest_false [Fintype α] [Fintype Q] (A : DFA α Q)
    [DecidablePred A.accept] (hpc : PrefixClosed A) (w : List α)
    (hw : A.Accepts w) (hfalse : liveTest A w = false) :
    suffixBorderRank w ≤ (acceptingStates A).card - 2 := by
  apply nonlive_rank_le_accepting_states A hpc hw
  intro hlive
  have htrue := (liveTest_correct A hpc w).mpr hlive
  rw [hfalse] at htrue
  contradiction

end NSSE.NonliveBorderRank
