import NSSE.StoredPlainNFAAccess

namespace NSSE.StoredAlphabetRowLabels
variable {d : Nat}

-- These are semantic label bridges, not an uncharged symbolic compiler.
namespace Marked
variable (A : StoredCapRowNFABuild.Data)
  (q r : Fin A.count) (p : Empty → Fin d)

theorem initial : (StoredMarkedNFAAccess.start A q).1 = true ↔
    ((AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) A)).initial q).Realize p := by
  simp only [AlphabetTableRows.compile,AlphabetTableRows.realize_truth,StoredMarkedNFAAccess.input,Bool.decide_coe]

theorem final : (StoredMarkedNFAAccess.final A q).1 = true ↔
    ((AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) A)).final q).Realize p := by
  simp only [AlphabetTableRows.compile,AlphabetTableRows.realize_truth,StoredMarkedNFAAccess.input,Bool.decide_coe]

theorem data (i : Fin d) : (StoredMarkedNFAAccess.step A q r (.inl i)).1 = true ↔
    ((AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) A)).data q r).Realize
      (Sum.elim p (fun _ => i)) := by
  simp only [AlphabetTableRows.compile,AlphabetTableRows.realize_unary,StoredMarkedNFAAccess.input,Bool.decide_coe]

theorem left : (StoredMarkedNFAAccess.step (d := d) A q r (.inr false)).1 = true ↔
    ((AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) A)).left q r).Realize p := by
  simp only [AlphabetTableRows.compile,AlphabetTableRows.realize_truth,StoredMarkedNFAAccess.input,Bool.decide_coe]

theorem right : (StoredMarkedNFAAccess.step (d := d) A q r (.inr true)).1 = true ↔
    ((AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) A)).right q r).Realize p := by
  simp only [AlphabetTableRows.compile,AlphabetTableRows.realize_truth,StoredMarkedNFAAccess.input,Bool.decide_coe]
end Marked

namespace Plain
variable (A : StoredRightIdealNFABuild.Data)
  (q r : Fin A.count) (p : Empty → Fin d)

theorem initial : (StoredPlainNFAAccess.start A q).1 = true ↔
    ((AlphabetTableRows.compileData (StoredPlainNFAAccess.input (d := d) A)).initial q).Realize p := by
  simp only [AlphabetTableRows.compileData,AlphabetTableRows.realize_truth,StoredPlainNFAAccess.input,Bool.decide_coe]

theorem final : (StoredPlainNFAAccess.final A q).1 = true ↔
    ((AlphabetTableRows.compileData (StoredPlainNFAAccess.input (d := d) A)).final q).Realize p := by
  simp only [AlphabetTableRows.compileData,AlphabetTableRows.realize_truth,StoredPlainNFAAccess.input,Bool.decide_coe]

theorem data (i : Fin d) : (StoredPlainNFAAccess.step A q r i).1 = true ↔
    ((AlphabetTableRows.compileData (StoredPlainNFAAccess.input (d := d) A)).data q r).Realize
      (Sum.elim p (fun _ => i)) := by
  simp only [AlphabetTableRows.compileData,AlphabetTableRows.realize_unary,StoredPlainNFAAccess.input,Bool.decide_coe]
end Plain

variable {n : Nat}
theorem marked_compile_snapshot (T : NSSE.NFA (Fin d ⊕ Bool) (Fin n)) [DecidablePred T.start]
    [DecidablePred T.accept] [∀ q x r, Decidable (T.step q x r)] :
    AlphabetTableRows.compile (StoredMarkedNFAAccess.input (d := d) (StoredCapRowNFABuild.snapshot T)) =
      AlphabetTableRows.compile T := by
  simp only [StoredMarkedNFAAccess.input_snapshot]

theorem plain_compile_snapshot (T : NSSE.NFA (Fin d) (Fin n)) [DecidablePred T.start]
    [DecidablePred T.accept] [∀ q x r, Decidable (T.step q x r)] :
    AlphabetTableRows.compileData (StoredPlainNFAAccess.input (d := d) (StoredRightIdealNFABuild.snapshot T)) =
      AlphabetTableRows.compileData T := by
  simp only [StoredPlainNFAAccess.input_snapshot]
end NSSE.StoredAlphabetRowLabels
