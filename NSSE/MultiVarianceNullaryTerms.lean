import NSSE.MultiVarianceTerms
import NSSE.MultiConstructorNullaryDecision

/-! All-nullary signed terms have the exact finite label semantics.
Every original tree is finite/regular here, including the empty signature. -/
namespace NSSE.MultiVarianceNullaryTerms
open MultiConstructorTerms (Term Literal Query)
open MultiConstructorNullaryValues (allValue finiteValue all_value_surjective embed_value)
open MultiConstructorNullaryTerms (labelEval LabelHolds LabelSatisfies LabelSatisfiable LabelEntails)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceTrees MultiVarianceTerms
variable {H : Type*} {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def value (l : Label H) : Tree pol := ⟨allValue l⟩

theorem encoded_eq (hn : ∀ h, arity h=0) (t : Tree pol) : encoded t=t.raw := by
  calc
    encoded t=allValue ((encoded t).label []) := (all_value_surjective hn _).symm
    _=allValue (t.raw.label []) := rfl
    _=t.raw := all_value_surjective hn _

theorem value_surjective (hn : ∀ h, arity h=0) (t : Tree pol) : value pol (t.raw.label [])=t :=
  Tree.ext (all_value_surjective hn t.raw)

theorem value_le (hn : ∀ h, arity h=0) (a b : Label H) : value pol a≤value pol b ↔ a≤b := by
  change encoded (value pol a)≤encoded (value pol b) ↔ _
  rw [encoded_eq pol hn,encoded_eq pol hn]
  exact MultiConstructorNullaryValues.all_value_le a b

theorem value_eq (a b : Label H) : value pol a=value pol b ↔ a=b := by
  constructor
  · intro h
    exact congrArg (fun t : Tree pol => t.raw.label []) h
  · exact congrArg (value pol)

theorem finite_value (hn : ∀ h, arity h=0) (a : Label H) :
    MultiVarianceFiniteTrees.embed pol (finiteValue hn a)=value pol a := Tree.ext (embed_value hn a)

theorem all_finite (hn : ∀ h, arity h=0) (t : Tree pol) : MultiVarianceClasses.Finite t.raw :=
  ⟨finiteValue hn (t.raw.label []),(embed_value hn _).trans (all_value_surjective hn _)⟩

theorem all_regular (hn : ∀ h, arity h=0) (t : Tree pol) : MultiConstructorRegularTrees.Regular t.raw :=
  MultiConstructorNullaryValues.all_regular hn t.raw

theorem eval_value (hn : ∀ h, arity h=0) (env : Fin n → Label H) (t : Term arity n) :
    eval pol (fun x => value pol (env x)) t=value pol (labelEval env t) := by
  rw [← value_surjective pol hn (eval pol _ t)]
  congr 1
  cases t <;> rfl

theorem holds_value (hn : ∀ h, arity h=0) (env : Fin n → Label H) (l : Literal arity n) :
    Holds pol (fun x => value pol (env x)) l ↔ LabelHolds env l := by
  cases l <;> simp only [Holds,LabelHolds,eval_value pol hn,value_le pol hn,value_eq]

theorem satisfies_value (hn : ∀ h, arity h=0) (Q : Query arity n) (env : Fin n → Label H) :
    Satisfies pol Q (fun x => value pol (env x)) ↔ LabelSatisfies Q env := by
  simp only [Satisfies,LabelSatisfies,holds_value pol hn]

theorem all_sat_iff (hn : ∀ h, arity h=0) (Q : Query arity n) : Satisfiable pol Q ↔ LabelSatisfiable Q := by
  constructor
  · rintro ⟨rho,hs⟩
    refine ⟨fun x => (rho x).raw.label [],(satisfies_value pol hn Q _).mp ?_⟩
    simpa only [value_surjective pol hn] using hs
  · rintro ⟨env,he⟩
    exact ⟨fun x => value pol (env x),(satisfies_value pol hn Q env).mpr he⟩

theorem all_entails_iff (hn : ∀ h, arity h=0) (Q : Query arity n) : Entails pol Q ↔ LabelEntails Q := by
  constructor
  · intro he env hs
    have hh := he _ ((satisfies_value pol hn Q env).mpr hs)
    simpa only [eval_value pol hn,value_le pol hn] using hh
  · intro he rho hs
    let env := fun x => (rho x).raw.label []
    have hr : (fun x => value pol (env x))=rho := funext (fun x => value_surjective pol hn (rho x))
    have henv := (satisfies_value pol hn Q env).mp (hr.symm ▸ hs)
    have hh := (value_le pol hn _ _).mpr (he env henv)
    rw [← eval_value pol hn env Q.left,← eval_value pol hn env Q.right,hr] at hh
    exact hh

theorem class_sat_iff (P : Tree pol → Prop) (hp : ∀ t, P t) (Q : Query arity n) :
    ClassSatisfiable pol P Q ↔ Satisfiable pol Q :=
  ⟨fun ⟨rho,hs,_⟩ => ⟨rho,hs⟩,fun ⟨rho,hs⟩ => ⟨rho,hs,fun x => hp (rho x)⟩⟩
theorem class_entails_iff (P : Tree pol → Prop) (hp : ∀ t, P t) (Q : Query arity n) :
    ClassEntails pol P Q ↔ Entails pol Q :=
  ⟨fun he rho hs => he rho hs (fun x => hp (rho x)),fun he rho hs _ => he rho hs⟩

theorem finite_sat_iff (hn : ∀ h, arity h=0) (Q : Query arity n) : FiniteSatisfiable pol Q ↔ LabelSatisfiable Q := by
  rw [finite_sat_iff_class,class_sat_iff pol _ (all_finite pol hn),all_sat_iff pol hn]
theorem finite_entails_iff (hn : ∀ h, arity h=0) (Q : Query arity n) : FiniteEntails pol Q ↔ LabelEntails Q := by
  rw [finite_entails_iff_class,class_entails_iff pol _ (all_finite pol hn),all_entails_iff pol hn]
theorem regular_sat_iff (hn : ∀ h, arity h=0) (Q : Query arity n) : RegularSatisfiable pol Q ↔ LabelSatisfiable Q :=
  (class_sat_iff pol _ (all_regular pol hn) Q).trans (all_sat_iff pol hn Q)
theorem regular_entails_iff (hn : ∀ h, arity h=0) (Q : Query arity n) : RegularEntails pol Q ↔ LabelEntails Q :=
  (class_entails_iff pol _ (all_regular pol hn) Q).trans (all_entails_iff pol hn Q)

end NSSE.MultiVarianceNullaryTerms
