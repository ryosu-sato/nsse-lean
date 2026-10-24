import NSSE.LinearFamilyWordDecomposition
import Mathlib.Data.Nat.ModEq

/-!
# Concrete semantics of relative letter tables

Once an affine origin is known to precede the position, fixed relative
lookup is ordinary subtraction and periodic relative lookup is the
remainder of that subtraction modulo the word length.
-/

namespace NSSE

theorem fixedRelativeLetterAt_iff_local
    (word : Word α)
    (position origin : NatLinearExpr arity)
    (letter : α)
    (valuation : Fin arity → Nat)
    (horigin :
      origin.Eval valuation ≤ position.Eval valuation) :
    FixedRelativeLetterAt word position origin letter valuation ↔
      position.Eval valuation - origin.Eval valuation <
          word.length ∧
        word[position.Eval valuation -
          origin.Eval valuation]? = some letter := by
  constructor
  · rintro ⟨offset, hoffset, hletter, hposition⟩
    have hoffsetEq :
        position.Eval valuation - origin.Eval valuation =
          offset := by omega
    simpa [hoffsetEq] using And.intro hoffset hletter
  · rintro ⟨hoffset, hletter⟩
    refine ⟨position.Eval valuation -
        origin.Eval valuation, hoffset, hletter, ?_⟩
    exact (Nat.add_sub_of_le horigin).symm

theorem periodicRelativeLetterAt_iff_local
    (word : Word α)
    (hword : word ≠ [])
    (position origin : NatLinearExpr arity)
    (letter : α)
    (valuation : Fin arity → Nat)
    (horigin :
      origin.Eval valuation ≤ position.Eval valuation) :
    PeriodicRelativeLetterAt word position origin letter valuation ↔
      word[(position.Eval valuation -
        origin.Eval valuation) % word.length]? =
          some letter := by
  have hlength : 0 < word.length :=
    List.length_pos_iff.mpr hword
  let localOffset :=
    position.Eval valuation - origin.Eval valuation
  have hposition :
      origin.Eval valuation + localOffset =
        position.Eval valuation :=
    Nat.add_sub_of_le horigin
  constructor
  · rintro ⟨residue, hresidue, hletter, hmod⟩
    have haddMod :
        origin.Eval valuation + localOffset ≡
          origin.Eval valuation + residue
            [MOD word.length] := by
      change
        (origin.Eval valuation + localOffset) % word.length =
          (origin.Eval valuation + residue) % word.length
      rwa [hposition]
    have hlocalMod :
        localOffset ≡ residue [MOD word.length] :=
      Nat.ModEq.add_left_cancel'
        (origin.Eval valuation) haddMod
    have hlocalResidue :
        localOffset % word.length = residue := by
      change localOffset % word.length =
        residue % word.length at hlocalMod
      rwa [Nat.mod_eq_of_lt hresidue] at hlocalMod
    simpa [localOffset, hlocalResidue] using hletter
  · intro hletter
    let residue := localOffset % word.length
    have hresidue : residue < word.length :=
      Nat.mod_lt _ hlength
    refine ⟨residue, hresidue, ?_, ?_⟩
    · simpa [localOffset, residue] using hletter
    · have hlocalMod :
          localOffset ≡ residue [MOD word.length] := by
        change localOffset % word.length =
          residue % word.length
        simp [residue, Nat.mod_eq_of_lt hresidue]
      have haddMod :=
        hlocalMod.add_left (origin.Eval valuation)
      change
        position.Eval valuation % word.length =
          (origin.Eval valuation + residue) %
            word.length
      rw [← hposition]
      exact haddMod

end NSSE
