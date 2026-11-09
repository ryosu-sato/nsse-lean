import NSSE.MultiVarianceRailCoordinates

/-! A real added child that lands on a physical rail must be selected.
This is an inversion of actual literals, including terminal heads. -/
namespace NSSE.MultiVarianceLiteralInversion
open MultiConstructorConstraints (Bound Query)
open MultiVarianceEncoding MultiVarianceGlobal MultiVarianceOriginalSpine
open MultiVarianceSpineSeparation MultiVarianceSpineNormal MultiVarianceSpineTokens
open MultiVarianceTokenExact MultiVarianceSpineSuffixes MultiVarianceLiteralGeometry
open MultiVariancePositionLiterals MultiVariancePhysicalTrace MultiVarianceRailCoordinates
variable {H : Type*} {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

theorem childSlot_selected (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (r : Bool) (h : H) (j : Fin (arity h))
    (e : Nat) (he : e ≤ s.depth) (t : Bool)
    (hv : slot Q.left Q.right s.depth (childSlot pol s d hd r h j) = roleVariable Q s e he t) :
    selected (suffix s d) = some j.val := by
  by_contra hs
  rw [unselected_child pol Q s d hd r h j hs] at hv
  apply fill_ne_role Q s (nextRole r (pol h j)) e he t
  cases hn : nextRole r (pol h j) <;> simpa only [hn,Bool.false_eq_true,if_false,if_true] using hv

theorem childSlot_inverse (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (r : Bool) (h : H) (j : Fin (arity h))
    (e : Nat) (he : e ≤ s.depth) (t : Bool)
    (hv : slot Q.left Q.right s.depth (childSlot pol s d hd r h j) = roleVariable Q s e he t) :
    selected (suffix s d) = some j.val ∧ d+1=e ∧ nextRole r (pol h j)=t := by
  have hs := childSlot_selected pol Q s d hd r h j e he t hv
  have hn : d+1 ≤ s.depth := Nat.succ_le_iff.mpr (selected_lt s d hd j.val hs)
  rw [selected_child pol Q s d hd r h j hs hn] at hv
  exact ⟨hs,roleVariable_level Q s (d+1) e hn he _ t hv,
    roleVariable_role Q s (d+1) e hn he _ t (by omega) hv⟩

theorem letter_of_geometry (s : Spine arity) (d : Nat) (r : Bool) (h : H) (j : Fin (arity h))
    (hl : label (suffix s d) r = .node h) (hs : selected (suffix s d) = some j.val) :
    (path s)[d]? = some (⟨h,j⟩ : Letter arity) := by
  rw [← suffix_first s d]
  cases ht : suffix s d with
  | stop a b => simp only [ht,selected,reduceCtorEq] at hs
  | step k i t =>
    rw [ht] at hl hs
    have hk : k = h := MultiConstructorTrees.Label.node.inj hl
    subst k
    have hi : i = j := Fin.ext (Option.some.inj hs)
    subst i
    rfl

/-- Both level and role are recovered from the actual child equality;
off-path fills and terminal children cannot satisfy it. -/
theorem literal_child_inverse (Q : Query arity n) (s : Spine arity) (r : Bool)
    (b : Bound arity (count n s.depth)) (hb : b ∈ bounds (seeds pol Q s) r)
    (j : Fin (arity b.head)) (e : Nat) (he : e ≤ s.depth) (t : Bool)
    (hv : b.children j = roleVariable Q s e he t) :
    ∃ d, ∃ hd : d ≤ s.depth, b.parent = roleVariable Q s d hd r ∧
      (path s)[d]? = some (⟨b.head,j⟩ : Letter arity) ∧ d+1=e ∧ nextRole r (pol b.head j)=t := by
  obtain ⟨d,hd,hp,hl,hc⟩ := literal_shape pol Q s r b hb
  have hv' := (hc j).symm.trans hv
  obtain ⟨hs,he',hr⟩ := childSlot_inverse pol Q s d hd r b.head j e he t hv'
  exact ⟨d,hd,hp,letter_of_geometry s d r b.head j hl hs,he',hr⟩

end NSSE.MultiVarianceLiteralInversion
