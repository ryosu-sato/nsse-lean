import NSSE.MultiVarianceSupportNormal

/-! All hypotheses of the signed support normal-form theorem are proved
for the actual original-root spine compiler.  No supplied support, model,
SAT, validity, rank or finite-signature assumption is needed. -/
namespace NSSE.MultiVarianceSpineNormal
open MultiConstructorConstraints (Bound Constraints Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal
open MultiVarianceSpineSeparation MultiVarianceOriginalSpine MultiVarianceSpineClasses
open MultiVarianceSupportClasses (Kind)
open MultiVarianceSupportNormal
variable {H : Type*} {arity : H → Nat} {n : Nat}
variable (pol : Polarity arity)

/-- Every extension has its two fresh extremal variables, even at depth zero. -/
instance count_neZero (n d : Nat) : NeZero (count n d) := ⟨by unfold count; omega⟩

theorem compile_parent_parity (s : Spine arity) :
    (∀ b ∈ (compile pol s).lower, b.parent.val%2 = 0) ∧
    (∀ b ∈ (compile pol s).upper, b.parent.val%2 = 1) := by
  induction s with
  | stop a b =>
    constructor
    · intro c hc
      cases a <;> simp only [compile,MultiVarianceFlatStop.stopConstraints,
        MultiVarianceFlatStop.lowerBounds,List.mem_nil_iff,List.mem_singleton] at hc
      subst c
      rfl
    · intro c hc
      cases b <;> simp only [compile,MultiVarianceFlatStop.stopConstraints,
        MultiVarianceFlatStop.upperBounds,List.mem_nil_iff,List.mem_singleton] at hc
      subst c
      rfl
  | step h i s ih =>
    constructor
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        have he : b = ⟨0,h,MultiVarianceFlatStep.lowerChild pol h i⟩ := List.mem_singleton.mp hb
        subst b
        rfl
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        have hp := ih.1 b hb
        change (b.parent.val+2)%2 = 0
        omega
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        have he : b = ⟨1,h,MultiVarianceFlatStep.upperChild pol h i⟩ := List.mem_singleton.mp hb
        subst b
        rfl
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
        have hp := ih.2 b hb
        change (b.parent.val+2)%2 = 1
        omega

theorem tag_eq_old (d : Nat) (k : Fin (count n d)) (x : Fin n) (ht : tag d k = .old x) :
    k = old d x := by
  unfold tag at ht
  split at ht
  · have he : (⟨k.val,by assumption⟩ : Fin n) = x := Kind.old.inj ht
    have hv : k.val = x.val := congrArg (fun w : Fin n => w.val) he
    exact Fin.ext hv
  · split at ht <;> contradiction

theorem slot_fresh (x y : Fin n) (d : Nat) (k : Fin (width d)) (hk : 2 ≤ k.val) (z : Fin n) :
    slot x y d k ≠ old d z := by
  intro he
  have hv := congrArg Fin.val he
  have h0 : k.val ≠ 0 := by omega
  have h1 : k.val ≠ 1 := by omega
  simp only [slot,h0,h1,if_false,old,Fin.val_mk] at hv
  have hz := z.isLt
  omega

def seeds (Q : Query arity n) (s : Spine arity) : Constraints arity (count n s.depth) :=
  remap (slot Q.left Q.right s.depth) (compile pol s)

theorem lower_parent (Q : Query arity n) (s : Spine arity) (b : Bound arity (count n s.depth))
    (hb : b ∈ (seeds pol Q s).lower) :
    (∃ z, b.parent = old s.depth z) ∨ tag s.depth b.parent = .lower := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  have hp := (compile_parent_parity pol s).1 a ha
  by_cases hz : a.parent.val = 0
  · have he : a.parent = rootX s.depth := Fin.ext hz
    exact Or.inl ⟨Q.left,by change slot _ _ _ a.parent = _; rw [he]; rfl⟩
  · apply Or.inr
    have hi : 2 ≤ a.parent.val := by omega
    change tag s.depth (slot Q.left Q.right s.depth a.parent) = _
    rw [tag_slot Q.left Q.right s.depth a.parent hi,hp]
    rfl

theorem upper_parent (Q : Query arity n) (s : Spine arity) (b : Bound arity (count n s.depth))
    (hb : b ∈ (seeds pol Q s).upper) :
    (∃ z, b.parent = old s.depth z) ∨ tag s.depth b.parent = .upper := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  have hp := (compile_parent_parity pol s).2 a ha
  by_cases hz : a.parent.val = 1
  · have he : a.parent = rootY s.depth := Fin.ext hz
    exact Or.inl ⟨Q.right,by change slot _ _ _ a.parent = _; rw [he]; rfl⟩
  · apply Or.inr
    have hi : 2 ≤ a.parent.val := by omega
    change tag s.depth (slot Q.left Q.right s.depth a.parent) = _
    rw [tag_slot Q.left Q.right s.depth a.parent hi,hp]
    rfl

/-- Concrete construction of the geometric interface, not an added premise. -/
theorem geometry (Q : Query arity n) (s : Spine arity) :
    Geometry pol Q.constraints (seeds pol Q s) (old s.depth) where
  old_exact := old_support_iff pol Q s
  middle := by
    intro p q r hp hq
    cases ht : tag s.depth q with
    | old z => exact Or.inr (Or.inr ⟨z,tag_eq_old s.depth q z ht⟩)
    | lower => exact Or.inl (into_fresh_lower pol Q s ht hp)
    | upper => exact Or.inr (Or.inl (from_fresh_upper pol Q s ht hq))
  lower_fresh := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    intro i z
    exact slot_fresh Q.left Q.right s.depth (a.children i) (((compile_shapes pol s).1 a ha) i).1 z
  upper_fresh := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    intro i z
    exact slot_fresh Q.left Q.right s.depth (a.children i) (((compile_shapes pol s).2 a ha) i).1 z
  joint_parent := by
    intro a ha b hb he
    rcases lower_parent pol Q s a ha with hold | hlo
    · exact hold
    rcases upper_parent pol Q s b hb with ⟨z,hz⟩ | hup
    · exact ⟨z,he.trans hz⟩
    have ht := congrArg (tag s.depth) he
    rw [hlo,hup] at ht
    contradiction

/-- Exact support for every actual signed spine extension. -/
theorem extension_support_iff (Q : Query arity n) (s : Spine arity) (p q : Fin (count n s.depth)) :
    Support pol (extension pol Q s) p q ↔ Normal pol Q.constraints (seeds pol Q s) (old s.depth) p q :=
  support_iff_normal pol Q.constraints (seeds pol Q s) (old s.depth) (geometry pol Q s) p q

theorem extension_lower_crossing_iff (Q : Query arity n) (s : Spine arity)
    (p : Fin (count n s.depth)) (z : Fin n) :
    Support pol (extension pol Q s) p (old s.depth z) ↔
      Crossing pol Q.constraints (seeds pol Q s) (old s.depth) false p z := by
  constructor
  · intro hs
    exact normal_to_old pol Q.constraints (seeds pol Q s) (old s.depth) (geometry pol Q s) z
      ((extension_support_iff pol Q s p (old s.depth z)).mp hs)
  · exact crossing_sound pol Q.constraints (seeds pol Q s) (old s.depth)

theorem extension_upper_crossing_iff (Q : Query arity n) (s : Spine arity)
    (p : Fin (count n s.depth)) (z : Fin n) :
    Support pol (extension pol Q s) (old s.depth z) p ↔
      Crossing pol Q.constraints (seeds pol Q s) (old s.depth) true p z := by
  constructor
  · intro hs
    exact normal_from_old pol Q.constraints (seeds pol Q s) (old s.depth) (geometry pol Q s) z
      ((extension_support_iff pol Q s (old s.depth z) p).mp hs)
  · exact crossing_sound pol Q.constraints (seeds pol Q s) (old s.depth)

theorem extension_added_pair_iff_zipper (Q : Query arity n) (s : Spine arity)
    (a : Bound arity (count n s.depth)) (ha : a ∈ (seeds pol Q s).lower)
    (b : Bound arity (count n s.depth)) (hb : b ∈ (seeds pol Q s).upper) :
    Support pol (extension pol Q s) a.parent b.parent ↔
      Zipper pol Q.constraints (seeds pol Q s) (old s.depth) a.parent b.parent := by
  constructor
  · intro hs
    exact added_zipper pol Q.constraints (seeds pol Q s) (old s.depth) (geometry pol Q s) a ha b hb
      ((extension_support_iff pol Q s a.parent b.parent).mp hs)
  · exact zipper_sound pol Q.constraints (seeds pol Q s) (old s.depth)

theorem extension_fresh_pair_iff_zipper (Q : Query arity n) (s : Spine arity)
    (p q : Fin (count n s.depth)) (hp : ∀ z, p ≠ old s.depth z) (hq : ∀ z, q ≠ old s.depth z)
    (hne : p ≠ q) :
    Support pol (extension pol Q s) p q ↔ Zipper pol Q.constraints (seeds pol Q s) (old s.depth) p q := by
  constructor
  · intro hs
    rcases (extension_support_iff pol Q s p q).mp hs with he | ⟨z,he,_⟩ | ⟨z,he,_⟩ | hz
    · exact False.elim (hne he)
    · exact False.elim (hq z he)
    · exact False.elim (hp z he)
    · exact hz
  · exact zipper_sound pol Q.constraints (seeds pol Q s) (old s.depth)

end NSSE.MultiVarianceSpineNormal
