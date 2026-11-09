import NSSE.P0ProperWords
import Mathlib.Data.Fintype.Prod

/-! Synchronized pairs read the same literal word. Safety includes both
initial and final endpoints and does not depend on the birth predicate. -/
namespace NSSE.P0SafePairs
open P0ProperMachine
variable {Q A H : Type*}

def ValidPair (M : Machine Q A H) (p : Q × Q) : Prop :=
  M.valid p.1 ∧ M.valid p.2 ∧ M.head p.1 = M.head p.2

def move (M : Machine Q A H) (a : A) (p : Q × Q) : Q × Q :=
  (M.step p.1 a, M.step p.2 a)

def finish (M : Machine Q A H) (w : List A) (p : Q × Q) : Q × Q :=
  w.foldl (fun p a => move M a p) p

def Safe (M : Machine Q A H) : List A → Q × Q → Prop
  | [], p => ValidPair M p
  | a :: w, p => ValidPair M p ∧ Safe M w (move M a p)

@[simp] theorem finish_nil (M : Machine Q A H) (p : Q × Q) : finish M [] p = p := rfl

@[simp] theorem finish_cons (M : Machine Q A H) (a : A) (w : List A) (p : Q × Q) :
    finish M (a :: w) p = finish M w (move M a p) := rfl

theorem finish_append (M : Machine Q A H) (u v : List A) (p : Q × Q) :
    finish M (u ++ v) p = finish M v (finish M u p) := List.foldl_append

theorem safe_start (M : Machine Q A H) (w : List A) (p : Q × Q)
    (hs : Safe M w p) : ValidPair M p := by
  cases w with
  | nil => exact hs
  | cons a w => exact hs.1

theorem safe_finish (M : Machine Q A H) (w : List A) (p : Q × Q)
    (hs : Safe M w p) : ValidPair M (finish M w p) := by
  induction w generalizing p with
  | nil => exact hs
  | cons a w ih => exact ih _ hs.2

theorem safe_append (M : Machine Q A H) (u v : List A) (p : Q × Q) :
    Safe M (u ++ v) p ↔ Safe M u p ∧ Safe M v (finish M u p) := by
  induction u generalizing p with
  | nil =>
    change Safe M v p ↔ ValidPair M p ∧ Safe M v p
    exact ⟨fun h => ⟨safe_start M v p h,h⟩,fun h => h.2⟩
  | cons a u ih =>
    change (ValidPair M p ∧ Safe M (u ++ v) (move M a p)) ↔
      (ValidPair M p ∧ Safe M u (move M a p)) ∧ Safe M v (finish M u (move M a p))
    rw [ih]
    exact and_assoc.symm

theorem safe_take (M : Machine Q A H) (w : List A) (p : Q × Q)
    (hs : Safe M w p) (k : Nat) : Safe M (w.take k) p := by
  have h := (safe_append M (w.take k) (w.drop k) p).mp
    (by simpa only [List.take_append_drop] using hs)
  exact h.1

theorem safe_at (M : Machine Q A H) (w : List A) (p : Q × Q)
    (hs : Safe M w p) (k : Nat) : ValidPair M (finish M (w.take k) p) :=
  safe_finish M _ p (safe_take M w p hs k)

theorem safe_iff (M : Machine Q A H) (w : List A) (p : Q × Q) :
    Safe M w p ↔ ∀ k, k ≤ w.length → ValidPair M (finish M (w.take k) p) := by
  constructor
  · intro hs k _
    exact safe_at M w p hs k
  · intro h
    induction w generalizing p with
    | nil => exact h 0 (by simp)
    | cons a w ih =>
      refine ⟨h 0 (by simp),ih _ ?_⟩
      intro k hk
      simpa only [List.take_succ_cons,finish_cons] using h (k+1) (by simp; omega)

theorem finish_fst (M : Machine Q A H) (w : List A) (p : Q × Q) :
    (finish M w p).1 = w.foldl M.step p.1 := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih => exact ih _

theorem finish_snd (M : Machine Q A H) (w : List A) (p : Q × Q) :
    (finish M w p).2 = w.foldl M.step p.2 := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih => exact ih _

theorem diagonal_safe (M : Machine Q A H) (w : List A) (q : Q)
    (hv : ∀ k, k ≤ w.length → M.valid ((w.take k).foldl M.step q)) :
    Safe M w (q,q) := by
  apply (safe_iff M w (q,q)).mpr
  intro k hk
  simp only [ValidPair,finish_fst,finish_snd]
  exact ⟨hv k hk,hv k hk,True.intro⟩

instance validPairDecision [DecidableEq H] (M : Machine Q A H)
    [DecidablePred M.valid] : DecidablePred (ValidPair M) := fun _ => by
  unfold ValidPair
  infer_instance

instance safeDecision [DecidableEq H] (M : Machine Q A H)
    [DecidablePred M.valid] (w : List A) : DecidablePred (Safe M w) := by
  induction w with
  | nil => exact validPairDecision M
  | cons a w ih =>
    intro p
    change Decidable (ValidPair M p ∧ Safe M w (move M a p))
    letI := ih
    infer_instance

end NSSE.P0SafePairs
