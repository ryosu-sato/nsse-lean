import NSSE.P0FiniteOrbit
import Mathlib.Data.List.GetD

/-! Proper deterministic controls with literal-factor ray comparisons.
The state can include a rejecting sink, the actual token annotation and
a finite head selector. Births use their semantic X/Y order; no ordering
restriction is placed on their physical origins. This is the proper-word
layer only, not an original-input compilation theorem.
-/
namespace NSSE.P0ProperMachine

structure Machine (Q A H : Type*) where
  initial : Q
  step : Q → A → Q
  valid : Q → Prop
  head : Q → H
  birth : Q → Q → Prop

variable {Q A H : Type*}

def run (M : Machine Q A H) (z : Nat → A) : Nat → Q
  | 0 => M.initial
  | k+1 => M.step (run M z k) (z k)

@[simp] theorem run_zero (M : Machine Q A H) (z : Nat → A) : run M z 0 = M.initial := rfl
@[simp] theorem run_succ (M : Machine Q A H) (z : Nat → A) (k : Nat) :
    run M z (k+1) = M.step (run M z k) (z k) := rfl

def Match (z : Nat → A) (a b l : Nat) : Prop :=
  ∀ k, k < l → z (a+k) = z (b+k)

theorem match_mono (z : Nat → A) (a b l k : Nat) (hkl : k ≤ l)
    (hm : Match z a b l) : Match z a b k := fun t ht => hm t (by omega)

theorem match_symm (z : Nat → A) (a b l : Nat) (hm : Match z a b l) :
    Match z b a l := fun k hk => (hm k hk).symm

theorem run_equal (M : Machine Q A H) (z : Nat → A) (a b l : Nat)
    (hs : run M z a = run M z b) (hm : Match z a b l) :
    run M z (a+l) = run M z (b+l) := by
  induction l with
  | zero => simpa using hs
  | succ l ih =>
    rw [Nat.add_succ,Nat.add_succ,run_succ,run_succ,
      ih (match_mono z a b (l+1) l (by omega) hm),hm l (by omega)]

theorem run_congr (M : Machine Q A H) (z z' : Nat → A) (l : Nat)
    (hz : ∀ k, k < l → z k = z' k) : run M z l = run M z' l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [run_succ,run_succ,ih (fun k hk => hz k (by omega)),hz l (by omega)]

def GoodUpTo (M : Machine Q A H) (z : Nat → A) (n : Nat) : Prop :=
  (∀ k, k ≤ n → M.valid (run M z k)) ∧
  ∀ a, a ≤ n → ∀ b, b ≤ n → ∀ l, l ≤ n →
    a+l ≤ n → b+l ≤ n → M.birth (run M z a) (run M z b) →
    Match z a b l → M.head (run M z (a+l)) = M.head (run M z (b+l))

def Good (M : Machine Q A H) (z : Nat → A) : Prop := ∀ n, GoodUpTo M z n

theorem goodUpTo_mono (M : Machine Q A H) (z : Nat → A) (m n : Nat)
    (hmn : m ≤ n) (hg : GoodUpTo M z n) : GoodUpTo M z m := by
  constructor
  · exact fun k hk => hg.1 k (by omega)
  · intro a ha b hb l hl hal hbl hborn hm
    exact hg.2 a (by omega) b (by omega) l (by omega) (by omega) (by omega) hborn hm

theorem good_iff (M : Machine Q A H) (z : Nat → A) :
    Good M z ↔ (∀ k, M.valid (run M z k)) ∧
      ∀ a b l, M.birth (run M z a) (run M z b) → Match z a b l →
        M.head (run M z (a+l)) = M.head (run M z (b+l)) := by
  constructor
  · intro hg
    refine ⟨fun k => (hg k).1 k (by omega),?_⟩
    intro a b l hb hm
    exact (hg (a+b+l)).2 a (by omega) b (by omega) l (by omega)
      (by omega) (by omega) hb hm
  · rintro ⟨hv,hr⟩ n
    exact ⟨fun k _ => hv k,fun a _ b _ l _ _ _ hb hm => hr a b l hb hm⟩

/-- Erasing equal-state births changes no proper goodness verdict. -/
def eraseEqual (M : Machine Q A H) : Machine Q A H :=
  { M with birth := fun q t => M.birth q t ∧ q ≠ t }

@[simp] theorem run_eraseEqual (M : Machine Q A H) (z : Nat → A) (n : Nat) :
    run (eraseEqual M) z n = run M z n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [run_succ,eraseEqual] using congrArg (fun q => M.step q (z n)) ih

theorem goodUpTo_eraseEqual (M : Machine Q A H) (z : Nat → A) (n : Nat) :
    GoodUpTo (eraseEqual M) z n ↔ GoodUpTo M z n := by
  simp only [GoodUpTo]
  simp only [run_eraseEqual]
  simp only [eraseEqual]
  constructor
  · rintro ⟨hv,hr⟩
    refine ⟨hv,?_⟩
    intro a ha b hb l hl hal hbl hborn hm
    by_cases hs : run M z a = run M z b
    · exact congrArg M.head (run_equal M z a b l hs hm)
    · exact hr a ha b hb l hl hal hbl ⟨hborn,hs⟩ hm
  · rintro ⟨hv,hr⟩
    exact ⟨hv,fun a ha b hb l hl hal hbl hborn hm => hr a ha b hb l hl hal hbl hborn.1 hm⟩

theorem good_eraseEqual (M : Machine Q A H) (z : Nat → A) :
    Good (eraseEqual M) z ↔ Good M z := by
  simp only [Good,goodUpTo_eraseEqual]

end NSSE.P0ProperMachine
