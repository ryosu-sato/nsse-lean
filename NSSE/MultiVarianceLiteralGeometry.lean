import NSSE.MultiVarianceSpineSuffixes

/-! Exact root-literal geometry: current labels, selected child indices
and shared fill destinations, uniformly in the bound role. -/
namespace NSSE.MultiVarianceLiteralGeometry
open MultiConstructorConstraints (Bound)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceGlobal MultiVarianceSpineSeparation
open MultiVarianceSpineTokens MultiVarianceSpineRows MultiVarianceTokenExact
open MultiVarianceSpineSuffixes
variable {H : Type*} {arity : H → Nat}

instance width_neZero (d : Nat) : NeZero (width d) := ⟨by simp [width]⟩

def label : Spine arity → Bool → Label H
  | .stop a b, r => if r then b else a
  | .step h _ _, _ => .node h

def selected : Spine arity → Option Nat
  | .stop _ _ => none
  | .step _ i _ => some i.val

variable (pol : Polarity arity)

def stepChild (r : Bool) (h : H) (i j : Fin (arity h)) : Fin 6 :=
  if r then MultiVarianceFlatStep.upperChild pol h i j else MultiVarianceFlatStep.lowerChild pol h i j

def stopChild (r : Bool) (h : H) (j : Fin (arity h)) : Fin 4 :=
  if r then MultiVarianceFlatStop.upperChild pol h j else MultiVarianceFlatStop.lowerChild pol h j

theorem rootBounds_step (h : H) (i : Fin (arity h)) (s : Spine arity) (r : Bool) :
    rootBounds pol (.step h i s) r =
      [mapBound (stepEmbed s.depth) ⟨(if r then 1 else 0),h,stepChild pol r h i⟩] := by
  cases r <;> rfl

theorem rootBounds_stop (a b : Label H) (r : Bool) :
    rootBounds pol (.stop a b : Spine arity) r =
      match label (.stop a b : Spine arity) r with
      | .node h => [⟨(if r then 1 else 0),h,stopChild pol r h⟩]
      | _ => [] := by
  cases r <;> rfl

theorem selected_value (h : H) (i : Fin (arity h)) (d : Nat) (r : Bool) :
    (stepEmbed d (stepChild pol r h i i)).val = 2+parity (nextRole r (pol h i)) := by
  rw [stepChild,selected_role_pointer]
  cases hn : nextRole r (pol h i) <;> simp [shift,rootX,rootY,parity]

theorem offpath_value (h : H) (i j : Fin (arity h)) (d : Nat) (r : Bool) (hj : j ≠ i) :
    (stepEmbed d (stepChild pol r h i j)).val = 2*(d+1)+2+parity (nextRole r (pol h j)) := by
  cases r <;> cases hn : pol h j <;>
    simp only [stepChild,MultiVarianceFlatStep.lowerChild,MultiVarianceFlatStep.upperChild,hj,
      hn,nextRole,parity,Bool.not_true,Bool.not_false,Bool.false_eq_true,if_false,if_true]
  · rw [stepEmbed_bot]; rfl
  · rw [stepEmbed_top]; rfl
  · rw [stepEmbed_top]; rfl
  · rw [stepEmbed_bot]; rfl

theorem stopChild_value (h : H) (j : Fin (arity h)) (r : Bool) :
    (stopChild pol r h j).val = 2+parity (nextRole r (pol h j)) := by
  cases r <;> cases hn : pol h j <;>
    simp only [stopChild,MultiVarianceFlatStop.lowerChild,MultiVarianceFlatStop.upperChild,
      hn,nextRole,parity,Bool.not_true,Bool.not_false,Bool.false_eq_true,if_false,if_true]
  all_goals rfl

theorem root_shape (s : Spine arity) (r : Bool) (b : Bound arity (width s.depth))
    (hb : b ∈ rootBounds pol s r) :
    b.parent.val = parity r ∧ label s r = .node b.head ∧
      ∀ j, (b.children j).val =
        if selected s = some j.val then 2+parity (nextRole r (pol b.head j))
        else 2*s.depth+2+parity (nextRole r (pol b.head j)) := by
  cases s with
  | stop a c =>
    rw [rootBounds_stop] at hb
    cases he : label (.stop a c : Spine arity) r with
    | bot => rw [he] at hb; exact False.elim (List.not_mem_nil hb)
    | top => rw [he] at hb; exact False.elim (List.not_mem_nil hb)
    | node h =>
      rw [he] at hb
      have heq := List.mem_singleton.mp hb
      subst b
      refine ⟨?_,rfl,?_⟩
      · cases r <;> rfl
      · intro j
        simpa only [selected,reduceCtorEq,if_false,Spine.depth,Nat.mul_zero,Nat.zero_add] using stopChild_value pol _ j r
  | step h i s =>
    rw [rootBounds_step] at hb
    have heq := List.mem_singleton.mp hb
    subst b
    refine ⟨?_,rfl,?_⟩
    · cases r <;> rfl
    · intro j
      dsimp only [mapBound]
      by_cases hj : j = i
      · subst j
        simp only [selected,ite_true]
        exact selected_value pol h i s.depth r
      · have hi : i.val ≠ j.val := fun he => hj (Fin.ext he.symm)
        simp only [selected,Option.some.injEq,hi,if_false,Spine.depth]
        exact offpath_value pol h i j s.depth r hj

theorem root_exists (s : Spine arity) (r : Bool) {h : H} (hl : label s r = .node h) :
    ∃ b ∈ rootBounds pol s r, b.head = h := by
  cases s with
  | stop a c =>
    rw [rootBounds_stop,hl]
    exact ⟨_,List.mem_singleton.mpr rfl,rfl⟩
  | step k i s =>
    have hk : k = h := Label.node.inj hl
    subst k
    rw [rootBounds_step]
    exact ⟨_,List.mem_singleton.mpr rfl,rfl⟩

/-- The exact global child index: selected children advance one level;
every other child is the shared B or T slot with its new bound role. -/
theorem embedded_shape (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool)
    (b : Bound arity (width (suffix s d).depth)) (hb : b ∈ rootBounds pol (suffix s d) r) :
    (mapBound (embed s d hd) b).parent.val = 2*d+parity r ∧
      label (suffix s d) r = .node b.head ∧
      ∀ j, ((mapBound (embed s d hd) b).children j).val =
        if selected (suffix s d) = some j.val then 2*(d+1)+parity (nextRole r (pol b.head j))
        else 2*s.depth+2+parity (nextRole r (pol b.head j)) := by
  obtain ⟨hp,hl,hc⟩ := root_shape pol (suffix s d) r b hb
  refine ⟨?_,hl,?_⟩
  · change 2*d+b.parent.val = _
    rw [hp]
  · intro j
    change 2*d+(b.children j).val = _
    rw [hc]
    have hd' := suffix_depth s d hd
    split <;> omega

end NSSE.MultiVarianceLiteralGeometry
