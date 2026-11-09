import NSSE.MultiVarianceSupportClasses
import NSSE.MultiVarianceOriginalSpine

/-! The class theorem is discharged for the actual x823 compiler, including
negative selected pointers, off-path fillers, terminal literals and aliases. -/
namespace NSSE.MultiVarianceSpineClasses
open MultiConstructorConstraints (Bound Constraints Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
open MultiVarianceSpineSeparation MultiVarianceSupportClasses
variable {H : Type*} {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

/-- Parity 0 is a lower slot, parity 1 an upper slot. -/
def ChildShape {m : Nat} (b : Bound arity m) (upper : Bool) : Prop :=
  ∀ i, 2 ≤ (b.children i).val ∧ (b.children i).val % 2 =
    if pol b.head i then (if upper then 0 else 1) else (if upper then 1 else 0)

theorem step_lower_shape (h : H) (i : Fin (arity h)) :
    ChildShape pol (⟨0,h,MultiVarianceFlatStep.lowerChild pol h i⟩ : Bound arity 6) false := by
  intro j
  by_cases he : j = i
  · subst j
    cases hp : pol h i <;> (norm_num [ChildShape,MultiVarianceFlatStep.lowerChild,hp]; try decide)
  · cases hp : pol h j <;> norm_num [ChildShape,MultiVarianceFlatStep.lowerChild,he,hp] <;> decide

theorem step_upper_shape (h : H) (i : Fin (arity h)) :
    ChildShape pol (⟨1,h,MultiVarianceFlatStep.upperChild pol h i⟩ : Bound arity 6) true := by
  intro j
  by_cases he : j = i
  · subst j
    cases hp : pol h i <;> (norm_num [ChildShape,MultiVarianceFlatStep.upperChild,hp]; try decide)
  · cases hp : pol h j <;> norm_num [ChildShape,MultiVarianceFlatStep.upperChild,he,hp] <;> decide

theorem stop_lower_shape (h : H) :
    ChildShape pol (⟨0,h,MultiVarianceFlatStop.lowerChild pol h⟩ : Bound arity 4) false := by
  intro i
  cases hp : pol h i <;> (norm_num [MultiVarianceFlatStop.lowerChild,hp]; try decide)

theorem stop_upper_shape (h : H) :
    ChildShape pol (⟨1,h,MultiVarianceFlatStop.upperChild pol h⟩ : Bound arity 4) true := by
  intro i
  cases hp : pol h i <;> (norm_num [MultiVarianceFlatStop.upperChild,hp]; try decide)

theorem shift_shape {d : Nat} (b : Bound arity (width d)) (u : Bool)
    (hb : ChildShape pol b u) : ChildShape pol (mapBound (shift d) b) u := by
  intro i
  dsimp only [mapBound]
  obtain ⟨hi,hp⟩ := hb i
  change 2 ≤ (b.children i).val+2 ∧ ((b.children i).val+2)%2 = _
  constructor
  · omega
  · omega

theorem embed_shape (d : Nat) (b : Bound arity 6) (u : Bool)
    (hb : ChildShape pol b u) : ChildShape pol (mapBound (stepEmbed d) b) u := by
  intro i
  dsimp only [mapBound]
  obtain ⟨hi,hp⟩ := hb i
  simp only [stepEmbed]
  split <;> simp only [Fin.val_mk]
  · exact ⟨hi,hp⟩
  · constructor <;> omega

theorem compile_shapes (s : Spine arity) :
    (∀ b ∈ (compile pol s).lower, ChildShape pol b false) ∧
    (∀ b ∈ (compile pol s).upper, ChildShape pol b true) := by
  induction s with
  | stop a b =>
    constructor
    · intro c hc
      cases a <;> simp only [compile,MultiVarianceFlatStop.stopConstraints,
        MultiVarianceFlatStop.lowerBounds,List.mem_nil_iff,List.mem_singleton] at hc
      subst c
      exact stop_lower_shape pol _
    · intro c hc
      cases b <;> simp only [compile,MultiVarianceFlatStop.stopConstraints,
        MultiVarianceFlatStop.upperBounds,List.mem_nil_iff,List.mem_singleton] at hc
      subst c
      exact stop_upper_shape pol _
  | step h i s ih =>
    constructor
    · intro c hc
      change c ∈ _ ++ _ at hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        have he : b = ⟨0,h,MultiVarianceFlatStep.lowerChild pol h i⟩ :=
          List.mem_singleton.mp hb
        subst b
        exact embed_shape pol _ _ false (step_lower_shape pol h i)
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        exact shift_shape pol b false (ih.1 b hb)
    · intro c hc
      change c ∈ _ ++ _ at hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        have he : b = ⟨1,h,MultiVarianceFlatStep.upperChild pol h i⟩ :=
          List.mem_singleton.mp hb
        subst b
        exact embed_shape pol _ _ true (step_upper_shape pol h i)
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        exact shift_shape pol b true (ih.2 b hb)

open MultiVarianceOriginalSpine

def tag (d : Nat) (k : Fin (count n d)) : Kind n :=
  if hk : k.val < n then .old ⟨k.val,hk⟩
  else if (k.val-n)%2 = 0 then .lower else .upper

@[simp] theorem tag_old (d : Nat) (x : Fin n) : tag d (old d x) = .old x := by
  simp only [tag,old,x.isLt,dif_pos]

theorem tag_slot (x y : Fin n) (d : Nat) (k : Fin (width d)) (hk : 2 ≤ k.val) :
    tag d (slot x y d k) = if k.val%2 = 0 then .lower else .upper := by
  have h0 : k.val ≠ 0 := by omega
  have h1 : k.val ≠ 1 := by omega
  have hn : ¬n+(k.val-2)<n := by omega
  simp only [slot,h0,h1,if_false,tag,hn,dif_neg,Nat.add_sub_cancel_left]
  have hp : (k.val-2)%2 = k.val%2 := by omega
  rw [hp]
  simp

theorem lower_case (Q : Query arity n) (s : Spine arity) (h : H) (p : Fin (count n s.depth))
    (cs : Fin (arity h) → Fin (count n s.depth))
    (hb : (⟨p,h,cs⟩ : Bound arity _) ∈ (extension pol Q s).lower) :
    LowerCase pol Q.constraints (old s.depth) (tag s.depth) h p cs := by
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨⟨x,k,ds⟩,hmem,he⟩ := (List.mem_map (f := mapBound (old s.depth))).mp hb
    dsimp only [mapBound] at he
    cases he
    exact Or.inl ⟨x,ds,hmem,rfl,rfl⟩
  · obtain ⟨b,hb,he⟩ := List.mem_map.mp hb
    have hs := (compile_shapes pol s).1 b hb
    cases he
    apply Or.inr
    intro i
    obtain ⟨hi,hp⟩ := hs i
    change tag s.depth (slot Q.left Q.right s.depth (b.children i)) = _
    rw [tag_slot Q.left Q.right s.depth _ hi]
    cases hn : pol b.head i <;> simp_all only [Bool.false_eq_true,if_false,if_true]
    all_goals simp

theorem upper_case (Q : Query arity n) (s : Spine arity) (h : H) (p : Fin (count n s.depth))
    (cs : Fin (arity h) → Fin (count n s.depth))
    (hb : (⟨p,h,cs⟩ : Bound arity _) ∈ (extension pol Q s).upper) :
    UpperCase pol Q.constraints (old s.depth) (tag s.depth) h p cs := by
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨⟨x,k,ds⟩,hmem,he⟩ := (List.mem_map (f := mapBound (old s.depth))).mp hb
    dsimp only [mapBound] at he
    cases he
    exact Or.inl ⟨x,ds,hmem,rfl,rfl⟩
  · obtain ⟨b,hb,he⟩ := List.mem_map.mp hb
    have hs := (compile_shapes pol s).2 b hb
    cases he
    apply Or.inr
    intro i
    obtain ⟨hi,hp⟩ := hs i
    change tag s.depth (slot Q.left Q.right s.depth (b.children i)) = _
    rw [tag_slot Q.left Q.right s.depth _ hi]
    cases hn : pol b.head i <;> simp_all only [Bool.false_eq_true,if_false,if_true]
    all_goals simp

theorem support_classes (Q : Query arity n) (s : Spine arity) {x y : Fin (count n s.depth)}
    (hs : Support pol (extension pol Q s) x y) : Relation pol Q.constraints (tag s.depth) x y :=
  support_class pol Q.constraints (old s.depth) (tag s.depth) (tag_old s.depth)
    (extension pol Q s) (lower_case pol Q s) (upper_case pol Q s) hs

/-- Exact old support, even for invalid spines and inconsistent inputs. -/
theorem old_support_iff (Q : Query arity n) (s : Spine arity) (x y : Fin n) :
    Support pol (extension pol Q s) (old s.depth x) (old s.depth y) ↔
      Support pol Q.constraints x y := by
  constructor
  · intro hs
    exact (relation_old pol Q.constraints (old s.depth) (tag s.depth) (tag_old s.depth) x y).mp
      (support_classes pol Q s hs)
  · intro hs
    apply lift_support pol Q.constraints (old s.depth) (extension pol Q s) ?_ ?_ hs
    · intro a ha
      exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
    · intro a ha
      exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)

theorem into_fresh_lower (Q : Query arity n) (s : Spine arity) {x y : Fin (count n s.depth)}
    (hy : tag s.depth y = .lower) (hs : Support pol (extension pol Q s) x y) : x = y := by
  rcases support_classes pol Q s hs with he | hr
  · exact he
  · rw [hy] at hr
    cases ht : tag s.depth x <;> simp only [ht,Allowed] at hr

theorem from_fresh_upper (Q : Query arity n) (s : Spine arity) {x y : Fin (count n s.depth)}
    (hx : tag s.depth x = .upper) (hs : Support pol (extension pol Q s) x y) : x = y := by
  rcases support_classes pol Q s hs with he | hr
  · exact he
  · rw [hx] at hr
    cases ht : tag s.depth y <;> simp only [ht,Allowed] at hr

end NSSE.MultiVarianceSpineClasses
