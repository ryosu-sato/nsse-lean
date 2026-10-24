import NSSE.GuardedRowFiring

/-! # Capture-free parameter maps preserve literal Row runs and firings -/

namespace NSSE.RowParameterTransport

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedRowFiring

universe u v w w'
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {P' : Type w'} {n : Nat}

def mapRow (f : P → P') (R : Row L P n) : Row L P' n where
  initial q := (R.initial q).relabel f
  final q := (R.final q).relabel f
  data q r := (R.data q r).relabel (Sum.map f id)
  left q r := (R.left q r).relabel f
  right q r := (R.right q r).relabel f
  guard := R.guard.relabel (Sum.map f id)

theorem valuation_comp {D X : Type*} (f : P → P') (p : P' → D) (xs : X → D) :
    Sum.elim p xs ∘ Sum.map f id = Sum.elim (p ∘ f) xs := by
  funext x
  cases x <;> rfl

theorem dataNFA_map (f : P → P') (R : Row L P n) {D : Type*}
    [L.Structure D] (p : P' → D) :
    (mapRow f R).dataNFA p = R.dataNFA (p ∘ f) := by
  unfold Row.dataNFA mapRow
  congr 1
  · funext q
    exact propext Formula.realize_relabel
  · funext q x r
    apply propext
    rw [Formula.realize_relabel, valuation_comp]
  · funext q
    exact propext Formula.realize_relabel

theorem markedNFA_map (f : P → P') (R : Row L P n) {D : Type*}
    [L.Structure D] (p : P' → D) :
    (mapRow f R).markedNFA p = R.markedNFA (p ∘ f) := by
  unfold Row.markedNFA Row.dataNFA mapRow
  congr 1
  · funext q
    exact propext Formula.realize_relabel
  · funext q x r
    cases x with
    | inl x =>
        apply propext
        dsimp only
        rw [Formula.realize_relabel, valuation_comp]
    | inr b => cases b <;> exact propext Formula.realize_relabel
  · funext q
    exact propext Formula.realize_relabel

theorem firesAt_map (f : P → P') (R : Row L P n) {D : Type*}
    [L.Structure D] (p : P' → D) (seed : D) (body : List D) (j t : Nat) :
    FiresAt (mapRow f R) p seed body j t ↔ FiresAt R (p ∘ f) seed body j t := by
  unfold FiresAt
  rw [markedNFA_map]
  simp only [mapRow, Formula.realize_relabel, valuation_comp]

theorem fires_map (f : P → P') (R : Row L P n) {D : Type*}
    [L.Structure D] (p : P' → D) (seed : D) (body : List D) :
    Fires (mapRow f R) p seed body ↔ Fires R (p ∘ f) seed body := by
  simp only [Fires, firesAt_map]

end NSSE.RowParameterTransport
