import NSSE.Cap

/-!
# Deterministic finite-automaton interface

The cap semantics is phrased for arbitrary languages. This module supplies
the concrete deterministic automata used by restricted cap expressions.
Finiteness can be imposed separately as `[Fintype Q]`; elementary run lemmas
do not need enumeration.
-/

namespace NSSE

universe u v

structure DFA (α : Type u) (Q : Type v) where
  start : Q
  step : Q → α → Q
  accept : Q → Prop

structure NFA (α : Type u) (Q : Type v) where
  start : Q → Prop
  step : Q → α → Q → Prop
  accept : Q → Prop

namespace DFA

def runFrom (A : DFA α Q) (q : Q) (w : Word α) : Q :=
  w.foldl A.step q

def run (A : DFA α Q) (w : Word α) : Q :=
  A.runFrom A.start w

def Accepts (A : DFA α Q) (w : Word α) : Prop :=
  A.accept (A.run w)

def language (A : DFA α Q) : Language α := A.Accepts

@[simp] theorem runFrom_nil (A : DFA α Q) (q : Q) :
    A.runFrom q [] = q := rfl

@[simp] theorem runFrom_cons (A : DFA α Q) (q : Q) (a : α) (w : Word α) :
    A.runFrom q (a :: w) = A.runFrom (A.step q a) w := by
  rfl

theorem runFrom_append (A : DFA α Q) (q : Q) (x y : Word α) :
    A.runFrom q (x ++ y) = A.runFrom (A.runFrom q x) y := by
  induction x generalizing q with
  | nil => rfl
  | cons a x ih => simpa using ih (A.step q a)

theorem run_append (A : DFA α Q) (x y : Word α) :
    A.run (x ++ y) = A.runFrom (A.run x) y := by
  exact A.runFrom_append A.start x y

theorem accepts_append_iff (A : DFA α Q) (x y : Word α) :
    A.Accepts (x ++ y) ↔ A.accept (A.runFrom (A.run x) y) := by
  rw [Accepts, run_append]

theorem accepts_prefix_of_loop
    (A : DFA α Q) (loop w : Word α)
    (hloop : A.run loop = A.start)
    (hw : A.Accepts w) :
    A.Accepts (loop ++ w) := by
  unfold Accepts at hw ⊢
  rw [run_append, hloop]
  exact hw

theorem run_take_insertAt_before
    (A : DFA α Q) (w payload : Word α) (slot cut : Nat)
    (hslot : slot ≤ cut) (hcut : cut ≤ w.length)
    (hloop :
      A.runFrom (A.run (w.take slot)) payload =
        A.run (w.take slot)) :
    A.run ((Word.insertAt w payload slot).take
        (cut + payload.length)) =
      A.run (w.take cut) := by
  rw [Word.take_insertAt_before w payload slot cut hslot hcut]
  unfold Word.insertAt
  have htake :
      (w.take cut).take slot = w.take slot := by
    simp [List.take_take, Nat.min_eq_left hslot]
  rw [run_append, run_append, htake, hloop]
  have hdecomp :
      w.take cut =
        w.take slot ++ (w.take cut).drop slot := by
    calc
      w.take cut =
          (w.take cut).take slot ++ (w.take cut).drop slot :=
        (List.take_append_drop slot (w.take cut)).symm
      _ = w.take slot ++ (w.take cut).drop slot := by rw [htake]
  rw [hdecomp, run_append]
  simp [List.drop_append, List.length_take,
    Nat.min_eq_left (Nat.le_trans hslot hcut)]

theorem accepts_take_insertAt_before_of_loop
    (A : DFA α Q) (w payload : Word α) (slot cut : Nat)
    (hslot : slot ≤ cut) (hcut : cut ≤ w.length)
    (hloop :
      A.runFrom (A.run (w.take slot)) payload =
        A.run (w.take slot))
    (haccept : A.Accepts (w.take cut)) :
    A.Accepts ((Word.insertAt w payload slot).take
      (cut + payload.length)) := by
  unfold Accepts at haccept ⊢
  rw [A.run_take_insertAt_before w payload slot cut
    hslot hcut hloop]
  exact haccept

theorem run_insertAt_of_loop
    (A : DFA α Q) (w payload : Word α) (slot : Nat)
    (hloop :
      A.runFrom (A.run (w.take slot)) payload =
        A.run (w.take slot)) :
    A.run (Word.insertAt w payload slot) = A.run w := by
  unfold Word.insertAt
  rw [run_append, run_append, hloop]
  calc
    A.runFrom (A.run (w.take slot)) (w.drop slot) =
        A.run (w.take slot ++ w.drop slot) :=
      (A.run_append (w.take slot) (w.drop slot)).symm
    _ = A.run w :=
      congrArg A.run (List.take_append_drop slot w)

theorem accepts_insertAt_of_loop
    (A : DFA α Q) (w payload : Word α) (slot : Nat)
    (hloop :
      A.runFrom (A.run (w.take slot)) payload =
        A.run (w.take slot))
    (haccept : A.Accepts w) :
    A.Accepts (Word.insertAt w payload slot) := by
  unfold Accepts at haccept ⊢
  rw [A.run_insertAt_of_loop w payload slot hloop]
  exact haccept

end DFA

/-! ## Single-row SOA period signatures -/

/-- A period is good for a pair of DFAs when its root prefix is accepted by
`B` and the complementary suffix is accepted by `C`. -/
def GoodPeriod (B : DFA α Q₁) (C : DFA α Q₂) (w : Word α) (p : Nat) : Prop :=
  Word.HasPeriod w p ∧
    B.Accepts (w.take p) ∧ C.Accepts (w.drop p)

/-- The word has no good period for the row `(B,C)`. -/
def AvoidsGoodPeriods (B : DFA α Q₁) (C : DFA α Q₂) (w : Word α) : Prop :=
  ∀ p, ¬ GoodPeriod B C w p

/-- Every period of `small` has a period of `large` with the same two DFA
states relevant to the good-period test.  The periods themselves and their
locations need not agree.  This is the exact semantic conclusion targeted by
the experimental `FS-Sig` lemma in `notes_chatgpt_v67.md`. -/
def PeriodSignatureCovered
    (B : DFA α Q₁) (C : DFA α Q₂) (small large : Word α) : Prop :=
  ∀ p, Word.HasPeriod small p →
    ∃ q, Word.HasPeriod large q ∧
      B.run (small.take p) = B.run (large.take q) ∧
      C.run (small.drop p) = C.run (large.drop q)

/-- Signature coverage is sufficient for downward transfer of avoidance.
This proves the logical last step of `FS-Sig`; constructing the coverage from
fold-set equality remains the open combinatorial problem. -/
theorem avoidsGoodPeriods_of_signatureCovered
    (B : DFA α Q₁) (C : DFA α Q₂) (small large : Word α)
    (hcover : PeriodSignatureCovered B C small large)
    (havoid : AvoidsGoodPeriods B C large) :
    AvoidsGoodPeriods B C small := by
  intro p hp
  rcases hp with ⟨hperiod, hB, hC⟩
  rcases hcover p hperiod with ⟨q, hq, hrunB, hrunC⟩
  apply havoid q
  refine ⟨hq, ?_, ?_⟩
  · unfold DFA.Accepts at hB ⊢
    rwa [← hrunB]
  · unfold DFA.Accepts at hC ⊢
    rwa [← hrunC]

namespace NFA

inductive Runs (A : NFA α Q) : Q → Word α → Q → Prop
  | nil (q : Q) : Runs A q [] q
  | cons {q r s : Q} {a : α} {w : Word α} :
      A.step q a r → Runs A r w s → Runs A q (a :: w) s

def Accepts (A : NFA α Q) (w : Word α) : Prop :=
  ∃ q₀ q₁, A.start q₀ ∧ A.Runs q₀ w q₁ ∧ A.accept q₁

def language (A : NFA α Q) : Language α := A.Accepts

theorem Runs.append (A : NFA α Q)
    {q r s : Q} {x y : Word α}
    (hx : A.Runs q x r) (hy : A.Runs r y s) :
    A.Runs q (x ++ y) s := by
  induction hx with
  | nil => exact hy
  | cons hstep hrun ih =>
      exact Runs.cons hstep (ih hy)

end NFA

/-- Convert a pair of automata directly into a cap component. -/
def CapComponent.ofDFA
    (left : DFA α Q₁) (right : DFA α Q₂) : CapComponent α where
  left := left.language
  right := right.language

theorem markedOccurrence_prefix_shift_of_left_loop
    (left : DFA α Q₁) (right : DFA α Q₂)
    (loop w : Word α)
    (hloop : left.run loop = left.start)
    (hmarked : MarkedOccurrence (CapComponent.ofDFA left right) w) :
    MarkedOccurrence (CapComponent.ofDFA left right) (loop ++ w) := by
  apply markedOccurrence_prefix_shift
    (CapComponent.ofDFA left right) loop w hmarked
  intro j t hjt ht hleft
  exact left.accepts_prefix_of_loop loop (w.take j) hloop hleft

theorem markedOccurrence_insertAt_before_of_left_loop
    (left : DFA α Q₁) (right : DFA α Q₂)
    (w payload : Word α) (slot j t : Nat)
    (hslot : slot ≤ j) (hjt : j < t) (ht : t < w.length)
    (hleft : left.Accepts (w.take j))
    (hright : right.Accepts (Word.factor w j (t - j)))
    (hoccurs : OccursSuffixAt w j t)
    (hloop :
      left.runFrom (left.run (w.take slot)) payload =
        left.run (w.take slot)) :
    MarkedOccurrence (CapComponent.ofDFA left right)
      (Word.insertAt w payload slot) := by
  apply markedOccurrence_insertAt_before
    (CapComponent.ofDFA left right) w payload slot j t
    hslot hjt ht
  · exact left.accepts_take_insertAt_before_of_loop
      w payload slot j hslot (by omega) hloop hleft
  · exact hright
  · exact hoccurs

def CapComponent.ofNFA
    (left : NFA α Q₁) (right : NFA α Q₂) : CapComponent α where
  left := left.language
  right := right.language

def DFA.acceptAll (α : Type u) : DFA α Unit where
  start := ()
  step := fun _ _ => ()
  accept := fun _ => True

@[simp] theorem DFA.acceptAll_accepts (w : Word α) :
    (DFA.acceptAll α).Accepts w := by
  trivial

end NSSE
