import NSSE.P0ProperMachine
import Mathlib.Data.List.OfFn

/-! The proper predicate on actual finite literal words. It is defined
without padding symbols or an inhabited alphabet, so epsilon over the
empty alphabet is included. Exact agreement with the stream formulation
is proved, rather than assuming a finite-word recognition interface. -/
namespace NSSE.P0ProperWords
open P0ProperMachine
variable {Q A H : Type*}

def state (M : Machine Q A H) (w : List A) (k : Nat) : Q :=
  (w.take k).foldl M.step M.initial

def Spells (z : Nat → A) (w : List A) : Prop :=
  ∀ k, k < w.length → w[k]? = some (z k)

def WordMatch (w : List A) (a b l : Nat) : Prop :=
  ∀ k, k < l → w[a+k]? = w[b+k]?

def GoodWord (M : Machine Q A H) (w : List A) : Prop :=
  (∀ k, k ≤ w.length → M.valid (state M w k)) ∧
  ∀ a, a ≤ w.length → ∀ b, b ≤ w.length → ∀ l, l ≤ w.length →
    a+l ≤ w.length → b+l ≤ w.length → M.birth (state M w a) (state M w b) →
    WordMatch w a b l → M.head (state M w (a+l)) = M.head (state M w (b+l))

theorem state_eq_run (M : Machine Q A H) (w : List A) (z : Nat → A)
    (hz : Spells z w) (k : Nat) (hk : k ≤ w.length) : state M w k = run M z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkl : k < w.length := by omega
    have hletter : w[k] = z k := by
      simpa only [List.getElem?_eq_getElem hkl,Option.some.injEq] using hz k hkl
    simp only [state,List.take_succ_eq_append_getElem hkl,List.foldl_append,
      List.foldl_cons,List.foldl_nil]
    rw [show (w.take k).foldl M.step M.initial = run M z k from ih (by omega),hletter,run_succ]

theorem match_iff (w : List A) (z : Nat → A) (hz : Spells z w) (a b l : Nat)
    (ha : a+l ≤ w.length) (hb : b+l ≤ w.length) : WordMatch w a b l ↔ Match z a b l := by
  constructor
  · intro hm k hk
    have he := hm k hk
    rw [hz (a+k) (by omega),hz (b+k) (by omega)] at he
    exact Option.some.inj he
  · intro hm k hk
    rw [hz (a+k) (by omega),hz (b+k) (by omega),hm k hk]

theorem goodWord_iff_stream (M : Machine Q A H) (w : List A) (z : Nat → A)
    (hz : Spells z w) : GoodWord M w ↔ GoodUpTo M z w.length := by
  constructor
  · rintro ⟨hv,hr⟩
    constructor
    · intro k hk
      rw [← state_eq_run M w z hz k hk]
      exact hv k hk
    · intro a ha b hb l hl hal hbl hborn hm
      have hborn' : M.birth (state M w a) (state M w b) := by
        rwa [state_eq_run M w z hz a ha,state_eq_run M w z hz b hb]
      have he := hr a ha b hb l hl hal hbl hborn' ((match_iff w z hz a b l hal hbl).mpr hm)
      rwa [state_eq_run M w z hz (a+l) hal,state_eq_run M w z hz (b+l) hbl] at he
  · rintro ⟨hv,hr⟩
    constructor
    · intro k hk
      rw [state_eq_run M w z hz k hk]
      exact hv k hk
    · intro a ha b hb l hl hal hbl hborn hm
      have hborn' : M.birth (run M z a) (run M z b) := by
        rwa [← state_eq_run M w z hz a ha,← state_eq_run M w z hz b hb]
      rw [state_eq_run M w z hz (a+l) hal,state_eq_run M w z hz (b+l) hbl]
      exact hr a ha b hb l hl hal hbl hborn' ((match_iff w z hz a b l hal hbl).mp hm)

def prefixWord (z : Nat → A) (n : Nat) : List A := List.ofFn (fun k : Fin n => z k.val)

@[simp] theorem prefix_length (z : Nat → A) (n : Nat) : (prefixWord z n).length = n := by
  simp [prefixWord]

theorem spells_prefix (z : Nat → A) (n : Nat) : Spells z (prefixWord z n) := by
  intro k hk
  have hkn : k < n := by simpa using hk
  simp [prefixWord,hkn]

theorem goodWord_prefix (M : Machine Q A H) (z : Nat → A) (n : Nat) :
    GoodWord M (prefixWord z n) ↔ GoodUpTo M z n := by
  simpa using goodWord_iff_stream M (prefixWord z n) z (spells_prefix z n)

def goodWordDecision [DecidableEq A] [DecidableEq H] (M : Machine Q A H)
    (validDecision : DecidablePred M.valid) (birthDecision : DecidableRel M.birth)
    (w : List A) : Decidable (GoodWord M w) := by
  letI := validDecision
  letI := birthDecision
  unfold GoodWord WordMatch
  refine @instDecidableAnd _ _ ?_ ?_
  · infer_instance
  · refine @Nat.decidableBallLE w.length _ ?_
    intro a _
    refine @Nat.decidableBallLE w.length _ ?_
    intro b _
    refine @Nat.decidableBallLE w.length _ ?_
    intro l _
    infer_instance

def inspectWord [DecidableEq A] [DecidableEq H] (M : Machine Q A H)
    (validDecision : DecidablePred M.valid) (birthDecision : DecidableRel M.birth)
    (w : List A) : Bool := @decide (GoodWord M w) (goodWordDecision M validDecision birthDecision w)

theorem inspectWord_correct [DecidableEq A] [DecidableEq H] (M : Machine Q A H)
    (validDecision : DecidablePred M.valid) (birthDecision : DecidableRel M.birth) (w : List A) :
    inspectWord M validDecision birthDecision w = true ↔ GoodWord M w := by
  unfold inspectWord
  simp only [decide_eq_true_eq]

end NSSE.P0ProperWords
