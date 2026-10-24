import NSSE.Insertion
import NSSE.Commutation

/-!
# Guarded insertion-square holonomy

Exact free-word conclusion of the nonflat square branch.
-/

namespace NSSE

universe u

namespace Word

/--
If a nonempty payload can be inserted on either side of `T` with the same
result, the payload and `T` are powers of one primitive root; conversely
such powers give equal insertion results.
-/
theorem insertion_holonomy_iff_common_primitive
    (A T B X : Word α) (hX : X ≠ []) :
    insertAt (A ++ T ++ B) X A.length =
        insertAt (A ++ T ++ B) X (A.length + T.length) ↔
      ∃ root : Word α, ∃ m n,
        root.IsPrimitive ∧ 0 < m ∧
        X = power root m ∧ T = power root n := by
  rw [insertAt_two_slots_equal_iff_commute]
  exact commute_iff_common_primitive_power X T hX

end Word

end NSSE
