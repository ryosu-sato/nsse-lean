import NSSE.Insertion

/-!
# Finite insertion-event streams

This module formalizes the combinatorial first-mismatch skeleton used when
pulling a selected witness back through deletions.
-/

namespace NSSE

universe u

structure InsertionEvent (α : Type u) where
  slot : Nat
  payload : Word α
deriving DecidableEq

namespace InsertionEvent

def apply (e : InsertionEvent α) (w : Word α) : Word α :=
  Word.insertAt w e.payload e.slot

def applyStream (events : List (InsertionEvent α)) (w : Word α) : Word α :=
  events.foldl (fun current e => e.apply current) w

theorem applyStream_congr
    {events₁ events₂ : List (InsertionEvent α)}
    (h : events₁ = events₂) (w : Word α) :
    applyStream events₁ w = applyStream events₂ w := by
  rw [h]

end InsertionEvent

/--
Exact forms of the first divergence of two finite streams.  The common
prefix is retained explicitly; no events on different variants are
silently merged.
-/
inductive StreamDivergence {γ : Type u} : List γ → List γ → Prop
  | leftEnded (pre : List γ) (y : γ) (ys : List γ) :
      StreamDivergence pre (pre ++ y :: ys)
  | rightEnded (pre : List γ) (x : γ) (xs : List γ) :
      StreamDivergence (pre ++ x :: xs) pre
  | mismatch (pre : List γ) (x y : γ) (xs ys : List γ)
      (hne : x ≠ y) :
      StreamDivergence (pre ++ x :: xs) (pre ++ y :: ys)

namespace StreamDivergence

theorem ne {xs ys : List γ} (h : StreamDivergence xs ys) : xs ≠ ys := by
  intro heq
  cases h with
  | leftEnded pre y tail =>
      have hlen := congrArg List.length heq
      simp at hlen
  | rightEnded pre x tail =>
      have hlen := congrArg List.length heq
      simp at hlen
  | mismatch pre x y xt yt hxy =>
      have hcancel : x :: xt = y :: yt := by
        apply List.append_cancel_left (as := pre)
        simpa [List.append_assoc] using heq
      exact hxy (List.cons.inj hcancel).1

end StreamDivergence

/-- Two finite streams are equal or have a unique-form first divergence. -/
theorem eq_or_streamDivergence [DecidableEq γ] (xs ys : List γ) :
    xs = ys ∨ StreamDivergence xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact Or.inl rfl
      | cons y yt =>
          exact Or.inr (StreamDivergence.leftEnded [] y yt)
  | cons x xt ih =>
      cases ys with
      | nil =>
          exact Or.inr (StreamDivergence.rightEnded [] x xt)
      | cons y yt =>
          by_cases hxy : x = y
          · subst y
            rcases ih yt with htail | hdiv
            · exact Or.inl (congrArg (List.cons x) htail)
            · right
              cases hdiv with
              | leftEnded pre z zs =>
                  simpa [List.cons_append] using
                    (StreamDivergence.leftEnded (x :: xt) z zs)
              | rightEnded pre z zs =>
                  simpa [List.cons_append] using
                    (StreamDivergence.rightEnded (x :: yt) z zs)
              | mismatch pre a b as bs hab =>
                  simpa [List.cons_append] using
                    (StreamDivergence.mismatch
                      (x :: pre) a b as bs hab)
          · exact Or.inr
              (StreamDivergence.mismatch [] x y xt yt hxy)

theorem streamDivergence_iff_ne [DecidableEq γ] (xs ys : List γ) :
    StreamDivergence xs ys ↔ xs ≠ ys := by
  constructor
  · exact StreamDivergence.ne
  · intro hne
    rcases eq_or_streamDivergence xs ys with heq | hdiv
    · exact False.elim (hne heq)
    · exact hdiv

end NSSE
