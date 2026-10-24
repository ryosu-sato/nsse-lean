import NSSE.ConcreteSOA
import Lean.Elab.Tactic.Omega

/-!
# Concrete covered deletion squares

The v395 common-bottom square for two disjoint nonempty factors.  All
four edges are actual contiguous `DeletesTo` steps, and shortest-avoider
minimality covers the three proper vertices.
-/

namespace NSSE

universe u

namespace SOAInstance

structure CoveredDeletionSquare
    (I : SOAInstance α) (top sideH sideK bottom : Word α) : Prop where
  sideH_from_top : I.DeletesTo sideH top
  sideK_from_top : I.DeletesTo sideK top
  bottom_from_sideH : I.DeletesTo bottom sideH
  bottom_from_sideK : I.DeletesTo bottom sideK
  sideH_covered : I.RootCov sideH
  sideK_covered : I.RootCov sideK
  bottom_covered : I.RootCov bottom

theorem CoveredDeletionSquare.bottom_marked_witness
    {I : SOAInstance α} {top sideH sideK bottom : Word α}
    (square : I.CoveredDeletionSquare top sideH sideK bottom) :
    ∃ row ∈ I.rows, ∃ j t,
      j < t ∧ t < bottom.length ∧
      row.left (bottom.take j) ∧
      row.right (Word.factor bottom j (t - j)) ∧
      OccursSuffixAt bottom j t := by
  obtain ⟨row, hrow, hcovers⟩ := square.bottom_covered
  rw [rowCovers_iff_cuts] at hcovers
  obtain ⟨j, t, hjt, ht, hleft, hright, hoccurs⟩ := hcovers
  exact ⟨row, hrow, j, t, hjt, ht, hleft, hright, hoccurs⟩

/--
Deleting `H` and `K` from `A H T K B` in either order gives the same
bottom `A T B`, with all proper vertices covered.
-/
theorem covered_disjoint_deletion_square
    (I : SOAInstance α)
    (A H T K B : Word α)
    (hH : H ≠ []) (hK : K ≠ [])
    (hminimal :
      I.LengthMinimalAvoider (A ++ H ++ T ++ K ++ B))
    (hsideH : I.candidate (A ++ T ++ K ++ B))
    (hsideK : I.candidate (A ++ H ++ T ++ B))
    (hbottom : I.candidate (A ++ T ++ B)) :
    I.CoveredDeletionSquare
      (A ++ H ++ T ++ K ++ B)
      (A ++ T ++ K ++ B)
      (A ++ H ++ T ++ B)
      (A ++ T ++ B) := by
  have hHpos : 0 < H.length := List.length_pos_iff.mpr hH
  have hKpos : 0 < K.length := List.length_pos_iff.mpr hK
  have hsideHDelete :
      I.DeletesTo (A ++ T ++ K ++ B)
        (A ++ H ++ T ++ K ++ B) := by
    simpa [List.append_assoc] using
      I.deletesTo_append A H (T ++ K ++ B) hH
        (by simpa [List.append_assoc] using hsideH)
  have hsideKDelete :
      I.DeletesTo (A ++ H ++ T ++ B)
        (A ++ H ++ T ++ K ++ B) := by
    simpa [List.append_assoc] using
      I.deletesTo_append (A ++ H ++ T) K B hK
        (by simpa [List.append_assoc] using hsideK)
  have hbottomFromH :
      I.DeletesTo (A ++ T ++ B) (A ++ T ++ K ++ B) := by
    simpa [List.append_assoc] using
      I.deletesTo_append (A ++ T) K B hK
        (by simpa [List.append_assoc] using hbottom)
  have hbottomFromK :
      I.DeletesTo (A ++ T ++ B) (A ++ H ++ T ++ B) := by
    simpa [List.append_assoc] using
      I.deletesTo_append A H (T ++ B) hH
        (by simpa [List.append_assoc] using hbottom)
  have hsideHShort :
      (A ++ T ++ K ++ B).length <
        (A ++ H ++ T ++ K ++ B).length := by
    simp only [List.length_append]
    omega
  have hsideKShort :
      (A ++ H ++ T ++ B).length <
        (A ++ H ++ T ++ K ++ B).length := by
    simp only [List.length_append]
    omega
  have hbottomShort :
      (A ++ T ++ B).length <
        (A ++ H ++ T ++ K ++ B).length := by
    simp only [List.length_append]
    omega
  obtain ⟨hsideHCov, hsideKCov, hbottomCov⟩ :=
    covered_deletion_square hminimal hsideH hsideK hbottom
      hsideHShort hsideKShort hbottomShort
  exact ⟨hsideHDelete, hsideKDelete, hbottomFromH,
    hbottomFromK, hsideHCov, hsideKCov, hbottomCov⟩

end SOAInstance

end NSSE
