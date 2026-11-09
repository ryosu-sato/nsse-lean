import NSSE.MultiVarianceLiteralGeometry

/-! Complete actual literal lookup by level and bound role.  The selected
child advances to the next role; all other children are the shared fills. -/
namespace NSSE.MultiVariancePositionLiterals
open MultiConstructorConstraints (Bound Constraints Query)
open MultiVarianceEncoding MultiVarianceGlobal MultiVarianceSpineSeparation
open MultiVarianceOriginalSpine MultiVarianceSpineNormal MultiVarianceSpineTokens
open MultiVarianceSpineRows MultiVarianceTokenExact MultiVarianceSpineSuffixes
open MultiVarianceLiteralGeometry
variable {H : Type*} {arity : H → Nat} {n : Nat}

theorem selected_lt (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (j : Nat)
    (hs : selected (suffix s d) = some j) : d < s.depth := by
  have he := suffix_depth s d hd
  cases ht : suffix s d with
  | stop a b => simp only [ht,selected,reduceCtorEq] at hs
  | step h i t => rw [ht] at he; simp only [Spine.depth] at he; omega

variable (pol : Polarity arity)

def childSlot (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool) (h : H) (j : Fin (arity h)) :
    Fin (width s.depth) :=
  if hs : selected (suffix s d) = some j.val then
    railSlot s (d+1) (Nat.succ_le_iff.mpr (selected_lt s d hd j.val hs)) (nextRole r (pol h j))
  else if nextRole r (pol h j) then topAt s.depth else bottomAt s.depth

theorem mapped_root_shape (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool)
    (b : Bound arity (width (suffix s d).depth)) (hb : b ∈ rootBounds pol (suffix s d) r) :
    (mapBound (embed s d hd) b).parent = railSlot s d hd r ∧
      label (suffix s d) r = .node b.head ∧
      ∀ j, (mapBound (embed s d hd) b).children j = childSlot pol s d hd r b.head j := by
  obtain ⟨hp,hl,hc⟩ := embedded_shape pol s d hd r b hb
  refine ⟨Fin.ext hp,hl,?_⟩
  intro j
  apply Fin.ext
  have hj := hc j
  unfold childSlot
  split
  · simpa only [‹selected (suffix s d) = some j.val›,if_true,railSlot] using hj
  · rename_i hs
    cases hn : nextRole r (pol b.head j) <;>
      simp only [hs,if_false,hn,Bool.false_eq_true,if_true,parity,bottomAt,topAt,Fin.val_mk] at hj ⊢
    · simpa only [Nat.add_zero] using hj
    · simpa only [Nat.add_assoc] using hj

def roleVariable (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool) :
    Fin (count n s.depth) := slot Q.left Q.right s.depth (railSlot s d hd r)

theorem literal_shape (Q : Query arity n) (s : Spine arity) (r : Bool)
    (b : Bound arity (count n s.depth)) (hb : b ∈ bounds (seeds pol Q s) r) :
    ∃ d, ∃ hd : d ≤ s.depth, b.parent = roleVariable Q s d hd r ∧
      label (suffix s d) r = .node b.head ∧
      ∀ j, b.children j = slot Q.left Q.right s.depth (childSlot pol s d hd r b.head j) := by
  rw [seeds,bounds_remap] at hb
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  obtain ⟨d,hd,c,hc,rfl⟩ := bound_origin pol s r a ha
  obtain ⟨hp,hl,hj⟩ := mapped_root_shape pol s d hd r c hc
  refine ⟨d,hd,?_,hl,?_⟩
  · exact congrArg (slot Q.left Q.right s.depth) hp
  · intro j
    exact congrArg (slot Q.left Q.right s.depth) (hj j)

/-- A real constructor label at a role position supplies an actual added
literal with exactly the certified selected/fill children. -/
theorem literal_exists (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (r : Bool) (h : H) (hl : label (suffix s d) r = .node h) :
    ∃ cs : Fin (arity h) → Fin (count n s.depth),
      (⟨roleVariable Q s d hd r,h,cs⟩ : Bound arity (count n s.depth)) ∈ bounds (seeds pol Q s) r ∧
      ∀ j, cs j = slot Q.left Q.right s.depth (childSlot pol s d hd r h j) := by
  obtain ⟨⟨p,k,cs⟩,hb,he⟩ := root_exists pol (suffix s d) r hl
  dsimp only at he
  subst k
  have hm := suffix_root_mem pol s d hd r ⟨p,h,cs⟩ hb
  have hs := mapped_root_shape pol s d hd r ⟨p,h,cs⟩ hb
  refine ⟨fun j => slot Q.left Q.right s.depth (embed s d hd (cs j)),?_,?_⟩
  · rw [seeds,bounds_remap]
    apply List.mem_map.mpr
    refine ⟨mapBound (embed s d hd) ⟨p,h,cs⟩,hm,?_⟩
    dsimp only [mapBound]
    have hp : slot Q.left Q.right s.depth (embed s d hd p) = roleVariable Q s d hd r :=
      congrArg (slot Q.left Q.right s.depth) hs.1
    rw [hp]
  · intro j
    exact congrArg (slot Q.left Q.right s.depth) (hs.2.2 j)

theorem selected_child (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (r : Bool) (h : H) (j : Fin (arity h)) (hs : selected (suffix s d) = some j.val)
    (hn : d+1 ≤ s.depth) :
    slot Q.left Q.right s.depth (childSlot pol s d hd r h j) =
      roleVariable Q s (d+1) hn (nextRole r (pol h j)) := by
  simp only [childSlot,hs,dif_pos,roleVariable]

theorem unselected_child (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth)
    (r : Bool) (h : H) (j : Fin (arity h)) (hs : selected (suffix s d) ≠ some j.val) :
    slot Q.left Q.right s.depth (childSlot pol s d hd r h j) =
      if nextRole r (pol h j) then slot Q.left Q.right s.depth (topAt s.depth)
      else slot Q.left Q.right s.depth (bottomAt s.depth) := by
  unfold childSlot
  rw [dif_neg hs]
  split <;> rfl

end NSSE.MultiVariancePositionLiterals
