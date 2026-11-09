import NSSE.MultiVarianceLiteralGeometry

/-! Role-sensitive remaining-depth potentials for the ACTUAL original
spine slots. Opposite-role and original slots have maximal potential;
matching fresh slots count down to their shared filler. -/
namespace NSSE.MultiVarianceSpinePotential
open MultiConstructorConstraints (Bound Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceGlobal MultiVarianceSpineSeparation
open MultiVarianceOriginalSpine MultiVarianceSpineClasses MultiVarianceSpineNormal
open MultiVarianceSupportClasses (Kind Allowed)
open MultiVarianceSpineTokens (nextRole)
open MultiVarianceSpineRows (parity)
open MultiVarianceSpineSuffixes (bounds)
variable {H : Type*} {arity : H → Nat} {n : Nat}

def value (d : Nat) (r : Bool) (x : Fin (count n d)) : Nat :=
  match tag d x with
  | .old _ => d+1
  | .lower => if r then d+1 else d-(x.val-n)/2
  | .upper => if r then d-(x.val-n)/2 else d+1

theorem value_bound (d : Nat) (r : Bool) (x : Fin (count n d)) : value d r x≤d+1 := by
  cases ht : tag d x <;> cases r <;> simp only [value,ht,Bool.false_eq_true,if_false,if_true] <;> omega

@[simp] theorem value_old (d : Nat) (r : Bool) (x : Fin n) : value d r (old d x)=d+1 := by
  simp only [value,tag_old]

theorem value_slot (x y : Fin n) (d : Nat) (r : Bool) (k : Fin (width d))
    (hp : k.val%2=parity r) : value d r (slot x y d k)=d+1-k.val/2 := by
  by_cases h0 : k.val=0
  · have he : k=rootX d := Fin.ext h0
    subst k
    rw [slot_rootX,value_old]
    simp only [h0,Nat.zero_div,Nat.sub_zero]
  by_cases h1 : k.val=1
  · have he : k=rootY d := Fin.ext h1
    subst k
    rw [slot_rootY,value_old]
    simp only [h1,Nat.reduceDiv,Nat.sub_zero]
  have hk : 2≤k.val := by omega
  have hb := k.isLt
  simp only [width] at hb
  rw [value,tag_slot x y d k hk,hp]
  have hv : (slot x y d k).val=n+(k.val-2) := by simp only [slot,h0,h1,if_false]
  cases r <;> simp only [parity,Bool.false_eq_true,if_false,if_true,reduceCtorEq,hv]
  all_goals omega

variable (pol : Polarity arity)

theorem left_support (Q : Query arity n) (s : Spine arity) {x y : Fin (count n s.depth)}
    (hs : Support pol (extension pol Q s) x y) : value s.depth false x≤value s.depth false y := by
  rcases support_classes pol Q s hs with rfl | hr
  · exact le_rfl
  · cases hx : tag s.depth x <;> cases hy : tag s.depth y <;>
      simp_all only [Allowed,value,Bool.false_eq_true,if_false] <;> omega

theorem right_support (Q : Query arity n) (s : Spine arity) {x y : Fin (count n s.depth)}
    (hs : Support pol (extension pol Q s) x y) : value s.depth true y≤value s.depth true x := by
  rcases support_classes pol Q s hs with rfl | hr
  · exact le_rfl
  · cases hx : tag s.depth x <;> cases hy : tag s.depth y <;>
      simp_all only [Allowed,value,if_true] <;> omega

theorem maximal_original (Q : Query arity n) (s : Spine arity) {x y : Fin (count n s.depth)}
    (hs : Support pol (extension pol Q s) x y)
    (hx : value s.depth false x=s.depth+1) (hy : value s.depth true y=s.depth+1) :
    ∃ a b : Fin n, x=old s.depth a ∧ y=old s.depth b := by
  have hh : ∃ a b : Fin n, tag s.depth x=.old a ∧ tag s.depth y=.old b := by
    rcases support_classes pol Q s hs with he | hr
    · subst y
      cases ht : tag s.depth x <;> simp_all [value] <;> omega
    · cases ht : tag s.depth x <;> cases hu : tag s.depth y <;> simp_all [value,Allowed] <;> omega
  obtain ⟨a,b,ha,hb⟩ := hh
  exact ⟨a,b,tag_eq_old s.depth x a ha,tag_eq_old s.depth y b hb⟩

theorem compile_parent_role (s : Spine arity) (r : Bool) (b : Bound arity (width s.depth))
    (hb : b∈bounds (compile pol s) r) : b.parent.val%2=parity r := by
  cases r
  · exact (compile_parent_parity pol s).1 b hb
  · exact (compile_parent_parity pol s).2 b hb

theorem compile_child_role (s : Spine arity) (r : Bool) (b : Bound arity (width s.depth))
    (hb : b∈bounds (compile pol s) r) (i : Fin (arity b.head)) :
    (b.children i).val%2=parity (nextRole r (pol b.head i)) := by
  cases r
  · have hh := ((compile_shapes pol s).1 b hb) i
    cases hp : pol b.head i <;> simpa only [hp,nextRole,parity,Bool.not_false,Bool.false_eq_true,if_false,if_true] using hh.2
  · have hh := ((compile_shapes pol s).2 b hb) i
    cases hp : pol b.head i <;> simpa only [hp,nextRole,parity,Bool.not_true,Bool.false_eq_true,if_false,if_true] using hh.2

theorem compile_child_deeper (s : Spine arity) (r : Bool) (b : Bound arity (width s.depth))
    (hb : b∈bounds (compile pol s) r) (i : Fin (arity b.head)) :
    b.parent.val/2<(b.children i).val/2 := by
  obtain ⟨d,hd,c,hc,rfl⟩ := MultiVarianceSpineSuffixes.bound_origin pol s r b hb
  have hg := MultiVarianceLiteralGeometry.embedded_shape pol s d hd r c hc
  have hp := hg.1
  have hi := hg.2.2 i
  have hr : parity r≤1 := by cases r <;> decide
  have hn : parity (nextRole r (pol c.head i))≤1 := by cases nextRole r (pol c.head i) <;> decide
  split at hi <;> omega

theorem added_strict (Q : Query arity n) (s : Spine arity) (r : Bool) (b : Bound arity (width s.depth))
    (hb : b∈bounds (compile pol s) r) (i : Fin (arity b.head)) :
    value s.depth (nextRole r (pol b.head i)) (slot Q.left Q.right s.depth (b.children i))<
      value s.depth r (slot Q.left Q.right s.depth b.parent) := by
  rw [value_slot _ _ _ _ _ (compile_child_role pol s r b hb i),
    value_slot _ _ _ _ _ (compile_parent_role pol s r b hb)]
  have he := compile_child_deeper pol s r b hb i
  have hb' := (b.children i).isLt
  simp only [width] at hb'
  omega

end NSSE.MultiVarianceSpinePotential
