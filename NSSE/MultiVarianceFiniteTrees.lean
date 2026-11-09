import NSSE.MultiVarianceClasses
import NSSE.MultiVarianceConstraints
import NSSE.MultiConstructorFiniteDecision

/-! Actual finite values in the original head-dependent signed order.
The existing finite-tree data are reused; comparisons explicitly use the
signed embedding, never their pre-existing covariant order instance. -/
namespace NSSE.MultiVarianceFiniteTrees
open MultiVarianceEncoding
open MultiConstructorConstraints (Constraints Query)
abbrev Value {H : Type*} (arity : H → Nat) := MultiConstructorFiniteTrees.Tree arity
variable {H : Type*} {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def embed (t : Value arity) : MultiVarianceTrees.Tree pol := ⟨MultiConstructorFiniteTrees.embed t⟩

@[simp] theorem embed_bot : embed pol (.bot : Value arity)=⊥ := rfl
@[simp] theorem embed_top : embed pol (.top : Value arity)=⊤ := rfl
@[simp] theorem embed_node (h : H) (c : Fin (arity h) → Value arity) :
    embed pol (.node h c)=MultiVarianceTrees.node h (fun i => embed pol (c i)) := rfl

theorem embed_injective : Function.Injective (embed (arity := arity) pol) := by
  intro a b h
  exact MultiConstructorFiniteTrees.embed_injective (congrArg MultiVarianceTrees.Tree.raw h)

theorem embed_finite (t : Value arity) : MultiVarianceClasses.Finite (embed pol t).raw := ⟨t,rfl⟩

def Satisfiable (phi : Constraints arity n) : Prop :=
  ∃ rho : Fin n → Value arity, MultiVarianceConstraints.Satisfies phi (fun x => embed pol (rho x))

def Entails (Q : Query arity n) : Prop :=
  ∀ rho : Fin n → Value arity, MultiVarianceConstraints.Satisfies Q.constraints (fun x => embed pol (rho x)) →
    embed pol (rho Q.left)≤embed pol (rho Q.right)

theorem satisfiable_iff_class (phi : Constraints arity n) : Satisfiable pol phi ↔
    ∃ rho : Fin n → MultiVarianceTrees.Tree pol, MultiVarianceConstraints.Satisfies phi rho ∧
      ∀ x, MultiVarianceClasses.Finite (rho x).raw := by
  constructor
  · rintro ⟨rho,hs⟩
    exact ⟨fun x => embed pol (rho x),hs,fun x => embed_finite pol (rho x)⟩
  · rintro ⟨rho,hs,hf⟩
    choose f he using hf
    have hh : (fun x => embed pol (f x))=rho := funext (fun x => MultiVarianceTrees.Tree.ext (he x))
    exact ⟨f,hh.symm ▸ hs⟩

theorem entails_iff_class (Q : Query arity n) : Entails pol Q ↔
    ∀ rho : Fin n → MultiVarianceTrees.Tree pol, MultiVarianceConstraints.Satisfies Q.constraints rho →
      (∀ x, MultiVarianceClasses.Finite (rho x).raw) → rho Q.left≤rho Q.right := by
  constructor
  · intro h rho hs hf
    choose f he using hf
    have hh : (fun x => embed pol (f x))=rho := funext (fun x => MultiVarianceTrees.Tree.ext (he x))
    rw [← hh]
    exact h f (hh.symm ▸ hs)
  · intro h rho hs
    exact h _ hs (fun x => embed_finite pol (rho x))

variable [DecidableEq H]

def leBool (a b : Value arity) : Bool := MultiConstructorFiniteDecision.leBool
  (MultiVarianceClasses.finiteEncode pol false a) (MultiVarianceClasses.finiteEncode pol false b)

theorem leBool_correct (a b : Value arity) : leBool pol a b=true ↔ embed pol a≤embed pol b := by
  rw [leBool,MultiConstructorFiniteDecision.leBool_correct,← MultiConstructorFiniteTrees.embed_le_embed,
    MultiVarianceClasses.finite_embed,MultiVarianceClasses.finite_embed]
  rfl

end NSSE.MultiVarianceFiniteTrees
