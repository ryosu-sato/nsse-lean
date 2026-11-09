import NSSE.MultiVarianceSpineLabels

/-! The actual shared Top lower bound and Bottom upper bound cannot
participate in any supported lower/upper label pair, even in an
inconsistent original program or an invalid supplied spine. -/
namespace NSSE.MultiVarianceFillClashes
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal MultiVarianceOriginalSpine
open MultiVarianceSpineSeparation MultiVarianceSpineNormal MultiVarianceSpineClasses
open MultiVariancePositionLiterals MultiVarianceRailCoordinates
open MultiVarianceLabelBounds MultiVarianceSpineAssertions MultiVarianceSpineLabels
variable {H : Type*} {arity : H → Nat} {n : Nat}

theorem fill_ne_old (Q : Query arity n) (s : Spine arity) (r : Bool) (z : Fin n) :
    fill Q s r ≠ old s.depth z := by
  apply slot_fresh Q.left Q.right s.depth (fillGlobal s r) ?_ z
  cases r <;> simp [fillGlobal,bottomAt,topAt]

theorem fill_ne_rail (Q : Query arity n) (s : Spine arity) (r : Bool)
    (d : Nat) (hd : d ≤ s.depth) (t : Bool) : fill Q s r ≠ roleVariable Q s d hd t := by
  have hh := fill_ne_role Q s (!r) d hd t
  cases r <;> simpa only [fill,fillGlobal,Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true] using hh

theorem fill_ne_opposite (Q : Query arity n) (s : Spine arity) (r : Bool) : fill Q s r ≠ fill Q s (!r) := by
  intro he
  have hv := congrArg Fin.val he
  cases r <;> simp [fill,fillGlobal,slot,bottomAt,topAt] at hv

theorem fill_tag (Q : Query arity n) (s : Spine arity) (r : Bool) :
    tag s.depth (fill Q s r) = if r then .lower else .upper := by
  change tag s.depth (slot Q.left Q.right s.depth (fillGlobal s r)) = _
  have hb : 2 ≤ (fillGlobal s r).val := by cases r <;> simp [fillGlobal,bottomAt,topAt]
  rw [tag_slot Q.left Q.right s.depth (fillGlobal s r) hb]
  cases r <;> simp [fillGlobal,bottomAt,topAt]

variable (pol : Polarity arity)

theorem no_opposite_fill_bound (Q : Query arity n) (s : Spine arity) (r : Bool) (a : Label H) :
    ¬LabelBound (extension pol Q s) (!r) (fill Q s r) a := by
  intro hb
  rcases (extension_label_origin pol Q s (!r) _ a).mp hb with
    ⟨z,hz,_⟩ | ⟨d,hd,hv,_,_⟩ | ⟨hv,_⟩
  · exact fill_ne_old Q s r z hz
  · exact fill_ne_rail Q s r d hd (!r) hv
  · exact fill_ne_opposite Q s r hv

theorem no_support_from_top_fill (Q : Query arity n) (s : Spine arity)
    (y : Fin (count n s.depth)) (b : Label H) (hu : LabelBound (extension pol Q s) true y b) :
    ¬Support pol (extension pol Q s) (fill Q s false) y := by
  intro hs
  have he := from_fresh_upper pol Q s (fill_tag Q s false) hs
  rw [← he] at hu
  exact no_opposite_fill_bound pol Q s false b hu

theorem no_support_to_bottom_fill (Q : Query arity n) (s : Spine arity)
    (x : Fin (count n s.depth)) (a : Label H) (hl : LabelBound (extension pol Q s) false x a) :
    ¬Support pol (extension pol Q s) x (fill Q s true) := by
  intro hs
  have he := into_fresh_lower pol Q s (fill_tag Q s true) hs
  rw [he] at hl
  exact no_opposite_fill_bound pol Q s true a hl

end NSSE.MultiVarianceFillClashes
