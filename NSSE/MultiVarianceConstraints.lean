import NSSE.MultiVarianceTrees
import NSSE.MultiConstructorConstraints

/-! The original four forms with head-dependent signed decomposition.
This is a new relation; the covariant support and its proofs are intact. -/
namespace NSSE.MultiVarianceConstraints
open MultiVarianceEncoding
open MultiConstructorConstraints (Bound Constraints Query)
variable {H : Type*} {arity : H → Nat} {n : Nat}

inductive Support (pol : Polarity arity) (phi : Constraints arity n) : Fin n → Fin n → Prop
  | refl (x) : Support pol phi x x
  | trans {x y z} : Support pol phi x y → Support pol phi y z → Support pol phi x z
  | decompCov {h : H} {x y : Fin n} {a b : Fin (arity h) → Fin n}
      (lower : ⟨x,h,a⟩ ∈ phi.lower) (upper : ⟨y,h,b⟩ ∈ phi.upper)
      (parents : Support pol phi x y) (i : Fin (arity h)) (positive : pol h i = false) :
      Support pol phi (a i) (b i)
  | decompCon {h : H} {x y : Fin n} {a b : Fin (arity h) → Fin n}
      (lower : ⟨x,h,a⟩ ∈ phi.lower) (upper : ⟨y,h,b⟩ ∈ phi.upper)
      (parents : Support pol phi x y) (i : Fin (arity h)) (negative : pol h i = true) :
      Support pol phi (b i) (a i)

variable {pol : Polarity arity}

def Satisfies (phi : Constraints arity n) (rho : Fin n → MultiVarianceTrees.Tree pol) : Prop :=
  (∀ a ∈ phi.upper, rho a.parent ≤ MultiVarianceTrees.node a.head (fun i => rho (a.children i))) ∧
  (∀ a ∈ phi.lower, MultiVarianceTrees.node a.head (fun i => rho (a.children i)) ≤ rho a.parent) ∧
  (∀ x ∈ phi.bot, rho x = ⊥) ∧ (∀ x ∈ phi.top, rho x = ⊤)

def Satisfiable (pol : Polarity arity) (phi : Constraints arity n) : Prop := ∃ rho, Satisfies (pol := pol) phi rho

def Entails (pol : Polarity arity) (Q : Query arity n) : Prop :=
  ∀ rho, Satisfies (pol := pol) Q.constraints rho → rho Q.left ≤ rho Q.right

theorem support_sound (phi : Constraints arity n) (rho : Fin n → MultiVarianceTrees.Tree pol)
    (hs : Satisfies phi rho) {x y} (h : Support pol phi x y) : rho x ≤ rho y := by
  induction h with
  | refl _ => exact le_rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | @decompCov h x y a b hl hu hp i hc ih =>
    have hh := (MultiVarianceTrees.node_le_node h _ _).mp ((hs.2.1 _ hl).trans (ih.trans (hs.1 _ hu))) i
    simpa only [hc,Bool.false_eq_true,if_false] using hh
  | @decompCon h x y a b hl hu hp i hc ih =>
    have hh := (MultiVarianceTrees.node_le_node h _ _).mp ((hs.2.1 _ hl).trans (ih.trans (hs.1 _ hu))) i
    simpa only [hc,if_true] using hh

def LabelClash (pol : Polarity arity) (phi : Constraints arity n) : Prop :=
  (∃ x ∈ phi.top, ∃ y ∈ phi.bot, Support pol phi x y) ∨
  (∃ x ∈ phi.top, ∃ b ∈ phi.upper, Support pol phi x b.parent) ∨
  (∃ a ∈ phi.lower, ∃ y ∈ phi.bot, Support pol phi a.parent y) ∨
  (∃ a ∈ phi.lower, ∃ b ∈ phi.upper, Support pol phi a.parent b.parent ∧ a.head ≠ b.head)

theorem no_label_clash (phi : Constraints arity n) (rho : Fin n → MultiVarianceTrees.Tree pol)
    (hs : Satisfies phi rho) : ¬LabelClash pol phi := by
  rintro (⟨x,hx,y,hy,hxy⟩ | ⟨x,hx,b,hb,hxb⟩ | ⟨a,ha,y,hy,hay⟩ | ⟨a,ha,b,hb,hab,hne⟩)
  · have h := support_sound phi rho hs hxy
    rw [hs.2.2.2 x hx,hs.2.2.1 y hy] at h
    exact MultiVarianceTrees.top_not_le_bot h
  · have h := (support_sound phi rho hs hxb).trans (hs.1 b hb)
    rw [hs.2.2.2 x hx] at h
    exact MultiVarianceTrees.top_not_le_node b.head _ h
  · have h := (hs.2.1 a ha).trans (support_sound phi rho hs hay)
    rw [hs.2.2.1 y hy] at h
    exact MultiVarianceTrees.node_not_le_bot a.head _ h
  · exact hne (MultiVarianceTrees.node_head_eq
      ((hs.2.1 a ha).trans ((support_sound phi rho hs hab).trans (hs.1 b hb))))

theorem clash_unsatisfiable (phi : Constraints arity n) (hc : LabelClash pol phi) : ¬Satisfiable pol phi :=
  fun ⟨rho,hs⟩ => no_label_clash phi rho hs hc

end NSSE.MultiVarianceConstraints
