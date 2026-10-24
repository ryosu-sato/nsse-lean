import NSSE.SymbolicProjection
import NSSE.SymbolicControl

/-!
# Symbolic inverse images under tape/coordinate selection

After epsilon elimination, erased input columns are genuine identity steps.
This implements unused tapes, including their longer tails, without changing
the old selected-word run or rebinding its parameters.
-/

namespace NSSE.SymbolicPreimage

open FirstOrder FirstOrder.Language SymbolicAutomata SymbolicProjection

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w}

section Runs

variable {α β Q : Type*}

def preimageNFA (A : NSSE.NFA β Q) (f : α → Option β) : NSSE.NFA α Q where
  start := A.start
  accept := A.accept
  step q a r := match f a with
    | none => q = r
    | some b => A.step q b r

theorem preimage_run_iff (A : NSSE.NFA β Q) (f : α → Option β)
    (q r : Q) (w : List α) :
    (preimageNFA A f).Runs q w r ↔ A.Runs q (w.filterMap f) r := by
  induction w generalizing q with
  | nil =>
      constructor <;> intro h <;> cases h <;> exact .nil _
  | cons a w ih =>
      cases hf : f a with
      | none =>
          simp only [List.filterMap_cons, hf]
          constructor
          · intro h
            cases h with
            | @cons _ t _ _ _ hstep hrest =>
                have hqt : q = t := by simpa only [preimageNFA, hf] using hstep
                subst t
                exact (ih q).mp hrest
          · intro h
            exact .cons (by simp [preimageNFA, hf]) ((ih q).mpr h)
      | some b =>
          simp only [List.filterMap_cons, hf]
          constructor
          · intro h
            cases h with
            | cons hstep hrest =>
                exact .cons (by simpa only [preimageNFA, hf] using hstep) ((ih _).mp hrest)
          · intro h
            cases h with
            | cons hstep hrest =>
                exact .cons (by simpa only [preimageNFA, hf] using hstep) ((ih _).mpr hrest)

theorem preimage_accepts (A : NSSE.NFA β Q) (f : α → Option β) (w : List α) :
    (preimageNFA A f).Accepts w ↔ A.Accepts (w.filterMap f) := by
  constructor
  · rintro ⟨q, r, hq, hrun, hr⟩
    exact ⟨q, r, hq, (preimage_run_iff A f q r w).mp hrun, hr⟩
  · rintro ⟨q, r, hq, hrun, hr⟩
    exact ⟨q, r, hq, (preimage_run_iff A f q r w).mpr hrun, hr⟩

end Runs

variable {n m m' : Nat} {arity : Fin m → Nat} {arity' : Fin m' → Nat}

def compile (plan : Plan arity arity') (A : Automaton L P n m' arity') :
    Automaton L P n m arity where
  initial := A.epsilonFree.initial
  final := A.epsilonFree.final
  silent _ _ := ⊥
  step s q r := match plan s with
    | .erase => SymbolicControl.flag (decide (q = r))
    | .keep t pick => (A.epsilonFree.step t q r).relabel (Sum.map id pick)

theorem compile_dataInterpret (plan : Plan arity arity') (A : Automaton L P n m' arity')
    {D : Type*} [L.Structure D] (p : P → D) :
    (compile plan A).dataInterpret p =
      preimageNFA (A.epsilonFree.dataInterpret p) (mapColumn plan) := by
  unfold Automaton.dataInterpret compile preimageNFA
  congr 1
  funext q c r
  rcases c with ⟨s, xs⟩
  apply propext
  cases hp : plan s with
  | erase => simp [hp, mapColumn, Action.map]
  | keep t pick =>
      simp only [hp, mapColumn, Action.map, Formula.realize_relabel]
      have hv : Sum.elim p xs ∘ Sum.map id pick = Sum.elim p (xs ∘ pick) := by
        funext x
        cases x <;> rfl
      rw [hv]

/-- Exact inverse image of the original epsilon language on all raw columns. -/
theorem compile_correct (plan : Plan arity arity') (A : Automaton L P n m' arity')
    {D : Type*} [L.Structure D] (p : P → D) (w : List (Column D arity)) :
    (compile plan A).Accepts p w ↔ A.Accepts p (w.filterMap (mapColumn plan)) := by
  rw [(compile plan A).accepts_iff_data_of_noSilent p (by intro q r; simp [compile]) w,
    compile_dataInterpret, preimage_accepts, A.epsilonFree_correct p _]

end NSSE.SymbolicPreimage
