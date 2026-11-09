import NSSE.MultiConstructorConstraints
import Mathlib.Data.Fintype.Powerset

/-! Executable least support relation for the original four-form input.
Intersecting all finite closed relations gives a deliberately simple total
algorithm; its specification is the existing inductive Support relation. -/
namespace NSSE.MultiConstructorSupportDecision
open MultiConstructorConstraints
variable {H : Type*} {arity : H → Nat} {n : Nat}

abbrev Relation (n : Nat) := Finset (Fin n × Fin n)

def Closed (phi : Constraints arity n) (R : Relation n) : Prop :=
  (∀ x, (x,x) ∈ R) ∧
  (∀ x y z, (x,y) ∈ R → (y,z) ∈ R → (x,z) ∈ R) ∧
  (∀ a ∈ phi.lower, ∀ b ∈ phi.upper, (a.parent,b.parent) ∈ R →
    ∀ i : Fin (arity a.head), ∀ j : Fin (arity b.head),
      a.head = b.head → i.val = j.val → (a.children i,b.children j) ∈ R)

theorem support_of_closed (phi : Constraints arity n) (R : Relation n) (hc : Closed phi R)
    {x y : Fin n} (hs : Support phi x y) : (x,y) ∈ R := by
  induction hs with
  | refl x => exact hc.1 x
  | trans _ _ ih₁ ih₂ => exact hc.2.1 _ _ _ ih₁ ih₂
  | @decomp h x y a b hl hu hp i ih =>
    exact hc.2.2 ⟨x,h,a⟩ hl ⟨y,h,b⟩ hu ih i i rfl rfl

variable [DecidableEq H]

def closedDecision (phi : Constraints arity n) (R : Relation n) : Decidable (Closed phi R) := by
  unfold Closed
  infer_instance

def closure (phi : Constraints arity n) : Relation n :=
  letI := closedDecision phi
  Finset.univ.filter (fun p => ∀ R : Relation n, Closed phi R → p ∈ R)

theorem mem_closure (phi : Constraints arity n) (x y : Fin n) :
    (x,y) ∈ closure phi ↔ ∀ R : Relation n, Closed phi R → (x,y) ∈ R := by
  simp only [closure,Finset.mem_filter,Finset.mem_univ,true_and]

theorem closure_closed (phi : Constraints arity n) : Closed phi (closure phi) := by
  refine ⟨?_,?_,?_⟩
  · intro x
    exact (mem_closure phi x x).mpr (fun R hR => hR.1 x)
  · intro x y z hxy hyz
    apply (mem_closure phi x z).mpr
    intro R hR
    exact hR.2.1 x y z ((mem_closure phi x y).mp hxy R hR)
      ((mem_closure phi y z).mp hyz R hR)
  · intro a ha b hb hab i j he hij
    apply (mem_closure phi _ _).mpr
    intro R hR
    exact hR.2.2 a ha b hb ((mem_closure phi _ _).mp hab R hR) i j he hij

theorem closure_exact (phi : Constraints arity n) (x y : Fin n) :
    (x,y) ∈ closure phi ↔ Support phi x y := by
  classical
  constructor
  · intro hxy
    let S : Relation n := Finset.univ.filter (fun p => Support phi p.1 p.2)
    have hm (u v : Fin n) : (u,v) ∈ S ↔ Support phi u v := by simp [S]
    have hc : Closed phi S := by
      refine ⟨?_,?_,?_⟩
      · intro u
        exact (hm u u).mpr (.refl u)
      · intro u v w huv hvw
        exact (hm u w).mpr (.trans ((hm u v).mp huv) ((hm v w).mp hvw))
      · rintro ⟨u,h,a⟩ ha ⟨v,k,b⟩ hb hab i j he hij
        dsimp only at he hij i j hab ⊢
        subst k
        have heq : i = j := Fin.ext hij
        subst j
        exact (hm _ _).mpr (.decomp ha hb ((hm u v).mp hab) i)
    exact (hm x y).mp ((mem_closure phi x y).mp hxy S hc)
  · exact support_of_closed phi (closure phi) (closure_closed phi)

def supportDecision (phi : Constraints arity n) : DecidableRel (Support phi) := fun x y =>
  decidable_of_iff ((x,y) ∈ closure phi) (closure_exact phi x y)

def inspect (phi : Constraints arity n) (x y : Fin n) : Bool := decide ((x,y) ∈ closure phi)

theorem inspect_correct (phi : Constraints arity n) (x y : Fin n) :
    inspect phi x y = true ↔ Support phi x y := by
  rw [inspect,decide_eq_true_eq,closure_exact]

def clashDecision (phi : Constraints arity n) : Decidable (LabelClash phi) := by
  letI := supportDecision phi
  unfold LabelClash
  infer_instance

def inspectClash (phi : Constraints arity n) : Bool := @decide (LabelClash phi) (clashDecision phi)

theorem inspectClash_correct (phi : Constraints arity n) :
    inspectClash phi = true ↔ LabelClash phi := by
  unfold inspectClash
  simp only [decide_eq_true_eq]

end NSSE.MultiConstructorSupportDecision
