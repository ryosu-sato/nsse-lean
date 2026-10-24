import NSSE.FiniteControl
import Lean.Elab.Tactic.Omega

/-!
# Finite protected positions

Protected letters are separated from contractible gaps.  Replacing gaps
cannot delete or reorder the protected occurrences.
-/

namespace NSSE

universe u v

inductive MarkedLayout (α : Type u)
  | tail (gap : Word α)
  | mark (gap : Word α) (letter : α) (rest : MarkedLayout α)

namespace MarkedLayout

def decode : MarkedLayout α → Word α
  | .tail gap => gap
  | .mark gap a rest => gap ++ [a] ++ rest.decode

def marks : MarkedLayout α → Word α
  | .tail _ => []
  | .mark _ a rest => a :: rest.marks

def mapGaps (f : Word α → Word α) : MarkedLayout α → MarkedLayout α
  | .tail gap => .tail (f gap)
  | .mark gap a rest => .mark (f gap) a (rest.mapGaps f)

@[simp] theorem marks_mapGaps (f : Word α → Word α)
    (layout : MarkedLayout α) :
    (layout.mapGaps f).marks = layout.marks := by
  induction layout with
  | tail gap => rfl
  | mark gap a rest ih =>
      simp [mapGaps, marks, ih]

theorem marks_sublist_decode (layout : MarkedLayout α) :
    layout.marks.Sublist layout.decode := by
  induction layout with
  | tail gap =>
      exact List.nil_sublist gap
  | mark gap a rest ih =>
      have hmark : [a].Sublist (gap ++ [a]) := by
        exact (List.nil_sublist gap).append
          (List.Sublist.cons₂ a List.Sublist.slnil)
      have happ := hmark.append ih
      simpa [marks, decode, List.append_assoc] using happ

theorem decode_ne_nil_of_marks_ne_nil
    {layout : MarkedLayout α} (hmarks : layout.marks ≠ []) :
    layout.decode ≠ [] := by
  have hle := (marks_sublist_decode layout).length_le
  have hpos : 0 < layout.marks.length :=
    List.length_pos_iff.mpr hmarks
  apply List.length_pos_iff.mp
  omega

theorem mapGaps_decode_ne_nil
    (f : Word α → Word α) {layout : MarkedLayout α}
    (hmarks : layout.marks ≠ []) :
    (layout.mapGaps f).decode ≠ [] := by
  apply decode_ne_nil_of_marks_ne_nil
  simpa using hmarks

theorem eval_decode_mapGaps
    {M : Type v} (C : ControlMonoid M) (letter : α → M)
    (f : Word α → Word α)
    (hpreserve : ∀ gap, C.eval letter gap = C.eval letter (f gap))
    (layout : MarkedLayout α) :
    C.eval letter layout.decode =
      C.eval letter (layout.mapGaps f).decode := by
  induction layout with
  | tail gap =>
      exact hpreserve gap
  | mark gap a rest ih =>
      simp only [decode, mapGaps, C.eval_append]
      rw [hpreserve gap, ih]

/--
Two layouts with the same protected-letter list retain exactly the same
ordered protected occurrences, independently of their gaps.
-/
theorem common_marks_survive
    {left right : MarkedLayout α}
    (hmarks : left.marks = right.marks) :
    ∃ kept,
      kept = left.marks ∧
      kept.Sublist left.decode ∧
      kept.Sublist right.decode := by
  exact ⟨left.marks, rfl, left.marks_sublist_decode,
    hmarks ▸ right.marks_sublist_decode⟩

def decodeBlocks (blocks : List (MarkedLayout α)) : Word α :=
  blocks.flatMap decode

def mapBlockGaps (f : Word α → Word α)
    (blocks : List (MarkedLayout α)) : List (MarkedLayout α) :=
  blocks.map (mapGaps f)

def EveryBlockMarked (blocks : List (MarkedLayout α)) : Prop :=
  ∀ block ∈ blocks, block.marks ≠ []

@[simp] theorem mapBlockGaps_length
    (f : Word α → Word α) (blocks : List (MarkedLayout α)) :
    (mapBlockGaps f blocks).length = blocks.length := by
  simp [mapBlockGaps]

theorem everyBlockMarked_mapBlockGaps
    (f : Word α → Word α) {blocks : List (MarkedLayout α)}
    (hmarked : EveryBlockMarked blocks) :
    EveryBlockMarked (mapBlockGaps f blocks) := by
  intro block hblock
  simp only [mapBlockGaps, List.mem_map] at hblock
  obtain ⟨source, hsource, rfl⟩ := hblock
  rw [marks_mapGaps]
  exact hmarked source hsource

/--
Every distinguished factor remains nonempty after arbitrary gap
replacement, provided that factor contains one protected letter.
-/
theorem decoded_blocks_ne_nil
    (f : Word α → Word α) {blocks : List (MarkedLayout α)}
    (hmarked : EveryBlockMarked blocks) :
    ∀ block ∈ mapBlockGaps f blocks, block.decode ≠ [] := by
  intro block hblock
  apply decode_ne_nil_of_marks_ne_nil
  exact everyBlockMarked_mapBlockGaps f hmarked block hblock

theorem eval_decodeBlocks_mapBlockGaps
    {M : Type v} (C : ControlMonoid M) (letter : α → M)
    (f : Word α → Word α)
    (hpreserve : ∀ gap, C.eval letter gap = C.eval letter (f gap))
    (blocks : List (MarkedLayout α)) :
    C.eval letter (decodeBlocks blocks) =
      C.eval letter (decodeBlocks (mapBlockGaps f blocks)) := by
  induction blocks with
  | nil =>
      simp [decodeBlocks, mapBlockGaps]
  | cons block blocks ih =>
      have ih' :
          C.eval letter (List.flatMap decode blocks) =
            C.eval letter
              (List.flatMap decode (List.map (mapGaps f) blocks)) := by
        simpa [decodeBlocks, mapBlockGaps] using ih
      simp only [decodeBlocks, mapBlockGaps, List.map_cons,
        List.flatMap_cons, C.eval_append]
      rw [eval_decode_mapGaps C letter f hpreserve block, ih']

end MarkedLayout

end NSSE
