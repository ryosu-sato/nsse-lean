import NSSE.GuardedRowFiring

/-! # Syntactic language maps preserve actual Row paths and firing semantics -/

namespace NSSE.RowLanguageTransport

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedRowFiring

universe u v u' v' w
variable {L : FirstOrder.Language.{u, v}} {L' : FirstOrder.Language.{u', v'}}
variable {P : Type w} {n : Nat}

def mapRow (f : L →ᴸ L') (R : Row L P n) : Row L' P n where
  initial q := f.onFormula (R.initial q)
  final q := f.onFormula (R.final q)
  data q r := f.onFormula (R.data q r)
  left q r := f.onFormula (R.left q r)
  right q r := f.onFormula (R.right q r)
  guard := f.onFormula R.guard

theorem dataNFA_map (f : L →ᴸ L') (R : Row L P n) {D : Type*}
    [L.Structure D] [L'.Structure D] [f.IsExpansionOn D] (p : P → D) :
    (mapRow f R).dataNFA p = R.dataNFA p := by
  unfold Row.dataNFA mapRow
  congr 1
  · funext q
    exact propext (f.realize_onFormula _)
  · funext q x r
    exact propext (f.realize_onFormula _)
  · funext q
    exact propext (f.realize_onFormula _)

theorem markedNFA_map (f : L →ᴸ L') (R : Row L P n) {D : Type*}
    [L.Structure D] [L'.Structure D] [f.IsExpansionOn D] (p : P → D) :
    (mapRow f R).markedNFA p = R.markedNFA p := by
  unfold Row.markedNFA Row.dataNFA mapRow
  congr 1
  · funext q
    exact propext (f.realize_onFormula _)
  · funext q x r
    cases x with
    | inl x => exact propext (f.realize_onFormula _)
    | inr b => cases b <;> exact propext (f.realize_onFormula _)
  · funext q
    exact propext (f.realize_onFormula _)

theorem firesAt_map (f : L →ᴸ L') (R : Row L P n) {D : Type*}
    [L.Structure D] [L'.Structure D] [f.IsExpansionOn D] (p : P → D)
    (seed : D) (body : List D) (j t : Nat) :
    FiresAt (mapRow f R) p seed body j t ↔ FiresAt R p seed body j t := by
  unfold FiresAt
  rw [markedNFA_map]
  simp only [mapRow, LHom.realize_onFormula]

theorem fires_map (f : L →ᴸ L') (R : Row L P n) {D : Type*}
    [L.Structure D] [L'.Structure D] [f.IsExpansionOn D] (p : P → D)
    (seed : D) (body : List D) :
    Fires (mapRow f R) p seed body ↔ Fires R p seed body := by
  simp only [Fires, firesAt_map]

end NSSE.RowLanguageTransport
