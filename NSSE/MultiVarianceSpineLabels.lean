import NSSE.MultiVarianceSpineAssertions

/-! Exhaustive actual label-bound origins after original-root aliasing:
original bounds, nontrivial rail labels, and the two shared extrema. -/
namespace NSSE.MultiVarianceSpineLabels
open MultiConstructorConstraints (Bound Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal MultiVarianceOriginalSpine
open MultiVarianceSpineSeparation MultiVarianceSpineNormal MultiVarianceSpineClasses
open MultiVarianceTokenExact MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry
open MultiVariancePositionLiterals MultiVarianceRailCoordinates
open MultiVarianceLabelBounds MultiVarianceSpineAssertions
variable {H : Type*} {arity : H → Nat} {n : Nat}

def Active (r : Bool) (a : Label H) : Prop := a ≠ extreme (!r)

theorem active_cases (r : Bool) (a : Label H) (ha : Active r a) :
    (∃ h, a=.node h) ∨ a=extreme r := by
  cases r <;> cases a <;> simp_all [Active,extreme]

theorem bound_active {m : Nat} (phi : MultiConstructorConstraints.Constraints arity m)
    (r : Bool) (x : Fin m) (a : Label H) (hb : LabelBound phi r x a) : Active r a := by
  rcases hb with ⟨b,_,_,rfl⟩ | ⟨_,rfl⟩
  all_goals cases r <;> simp [Active,extreme]

def fill (Q : Query arity n) (s : Spine arity) (r : Bool) : Fin (count n s.depth) :=
  slot Q.left Q.right s.depth (fillGlobal s r)

variable (pol : Polarity arity)

theorem rail_label_bound (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (r : Bool) (a : Label H) (hl : label (suffix s d) r=a) (ha : Active r a) :
    LabelBound (seeds pol Q s) r (roleVariable Q s d hd r) a := by
  rcases active_cases r a ha with ⟨h,rfl⟩ | rfl
  · obtain ⟨cs,hc,_⟩ := literal_exists pol Q s d hd r h hl
    exact Or.inl ⟨⟨roleVariable Q s d hd r,h,cs⟩,hc,rfl,rfl⟩
  · apply Or.inr
    refine ⟨?_,rfl⟩
    rw [seeds,assertions_remap]
    apply List.mem_map.mpr
    exact ⟨railSlot s d hd r,(assertion_origin pol s r _).mpr (Or.inr ⟨d,hd,rfl,hl⟩),rfl⟩

theorem fill_label_bound (Q : Query arity n) (s : Spine arity) (r : Bool) :
    LabelBound (seeds pol Q s) r (fill Q s r) (extreme r) := by
  apply Or.inr
  refine ⟨?_,rfl⟩
  rw [seeds,assertions_remap]
  exact List.mem_map.mpr ⟨fillGlobal s r,(assertion_origin pol s r _).mpr (Or.inl rfl),rfl⟩

theorem seed_label_origin (Q : Query arity n) (s : Spine arity) (r : Bool)
    (x : Fin (count n s.depth)) (a : Label H) : LabelBound (seeds pol Q s) r x a ↔
    (∃ d, ∃ hd : d ≤ s.depth, x=roleVariable Q s d hd r ∧ label (suffix s d) r=a ∧ Active r a) ∨
      (x=fill Q s r ∧ a=extreme r) := by
  constructor
  · intro hb
    have ha := bound_active (seeds pol Q s) r x a hb
    rcases hb with ⟨b,hb,hp,hl⟩ | ⟨hx,hl⟩
    · obtain ⟨d,hd,hs,he,_⟩ := literal_shape pol Q s r b hb
      exact Or.inl ⟨d,hd,hp.symm.trans hs,he.trans hl.symm,ha⟩
    · rw [seeds,assertions_remap] at hx
      obtain ⟨k,hk,he⟩ := List.mem_map.mp hx
      rcases (assertion_origin pol s r k).mp hk with hf | ⟨d,hd,hp,hlabel⟩
      · exact Or.inr ⟨he.symm.trans (congrArg (slot Q.left Q.right s.depth) hf),hl⟩
      · exact Or.inl ⟨d,hd,he.symm.trans (congrArg (slot Q.left Q.right s.depth) hp),hlabel.trans hl.symm,ha⟩
  · rintro (⟨d,hd,rfl,hl,ha⟩ | ⟨rfl,rfl⟩)
    · exact rail_label_bound pol Q s d hd r a hl ha
    · exact fill_label_bound pol Q s r

theorem extension_label_origin (Q : Query arity n) (s : Spine arity) (r : Bool)
    (x : Fin (count n s.depth)) (a : Label H) : LabelBound (extension pol Q s) r x a ↔
    (∃ z, x=old s.depth z ∧ LabelBound Q.constraints r z a) ∨
    (∃ d, ∃ hd : d ≤ s.depth, x=roleVariable Q s d hd r ∧ label (suffix s d) r=a ∧ Active r a) ∨
      (x=fill Q s r ∧ a=extreme r) := by
  change LabelBound (combine (remap (old s.depth) Q.constraints) (seeds pol Q s)) r x a ↔ _
  rw [labelBound_combine,labelBound_remap,seed_label_origin]

end NSSE.MultiVarianceSpineLabels
