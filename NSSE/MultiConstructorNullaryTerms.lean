import NSSE.MultiConstructorNullaryValues
import NSSE.MultiConstructorTermSemantics

/-! All-nullary nested terms have exact finite label-domain semantics.
Every actual valuation is represented, across all three tree classes. -/
namespace NSSE.MultiConstructorNullaryTerms
open MultiConstructorTerms MultiConstructorNullaryValues
open MultiConstructorTrees (Label)
open MultiConstructorConstraints (finiteAlgebra allAlgebra)
variable {H : Type*} {arity : H → Nat} {n : Nat}

def labelEval (env : Fin n → Label H) : Term arity n → Label H
  | .var v => env v
  | .bot => .bot
  | .top => .top
  | .node h _ => .node h

def LabelHolds (env : Fin n → Label H) : Literal arity n → Prop
  | .le a b => labelEval env a ≤ labelEval env b
  | .eq a b => labelEval env a = labelEval env b

def LabelSatisfies (Q : Query arity n) (env : Fin n → Label H) : Prop := ∀ l ∈ Q.premises, LabelHolds env l
def LabelSatisfiable (Q : Query arity n) : Prop := ∃ env, LabelSatisfies Q env
def LabelEntails (Q : Query arity n) : Prop :=
  ∀ env, LabelSatisfies Q env → labelEval env Q.left ≤ labelEval env Q.right

theorem finite_eval (hn : ∀ h, arity h = 0) (env : Fin n → Label H) (t : Term arity n) :
    eval finiteAlgebra (fun v => finiteValue hn (env v)) t = finiteValue hn (labelEval env t) := by
  cases t with
  | var v => rfl
  | bot => rfl
  | top => rfl
  | node h c =>
    apply congrArg (MultiConstructorFiniteTrees.Tree.node h)
    funext i
    exact Fin.elim0 (Fin.cast (hn h) i)

theorem all_eval (hn : ∀ h, arity h = 0) (env : Fin n → Label H) (t : Term arity n) :
    eval allAlgebra (fun v => allValue (env v)) t = allValue (labelEval env t) := by
  rw [← all_value_surjective hn (eval allAlgebra _ t)]
  congr 1
  cases t <;> rfl

theorem finite_holds (hn : ∀ h, arity h = 0) (env : Fin n → Label H) (l : Literal arity n) :
    Holds finiteAlgebra (fun v => finiteValue hn (env v)) l ↔ LabelHolds env l := by
  cases l <;> simp only [Holds,LabelHolds,finite_eval,finite_value_le,finite_value_eq]

theorem all_holds (hn : ∀ h, arity h = 0) (env : Fin n → Label H) (l : Literal arity n) :
    Holds allAlgebra (fun v => allValue (env v)) l ↔ LabelHolds env l := by
  cases l <;> simp only [Holds,LabelHolds,all_eval hn,all_value_le,all_value_eq]

theorem finite_satisfies (hn : ∀ h, arity h = 0) (Q : Query arity n) (env : Fin n → Label H) :
    Satisfies finiteAlgebra Q (fun v => finiteValue hn (env v)) ↔ LabelSatisfies Q env := by
  simp only [Satisfies,LabelSatisfies,finite_holds]

theorem all_satisfies (hn : ∀ h, arity h = 0) (Q : Query arity n) (env : Fin n → Label H) :
    Satisfies allAlgebra Q (fun v => allValue (env v)) ↔ LabelSatisfies Q env := by
  simp only [Satisfies,LabelSatisfies,all_holds hn]

theorem finite_sat_iff (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    Satisfiable finiteAlgebra Q ↔ LabelSatisfiable Q := by
  constructor
  · rintro ⟨rho,hr⟩
    refine ⟨fun v => finiteRoot (rho v),(finite_satisfies hn Q _).mp ?_⟩
    simpa only [finite_value_surjective] using hr
  · rintro ⟨env,he⟩
    exact ⟨fun v => finiteValue hn (env v),(finite_satisfies hn Q env).mpr he⟩

theorem all_sat_iff (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    Satisfiable allAlgebra Q ↔ LabelSatisfiable Q := by
  constructor
  · rintro ⟨rho,hr⟩
    refine ⟨fun v => (rho v).label [],(all_satisfies hn Q _).mp ?_⟩
    simpa only [all_value_surjective hn] using hr
  · rintro ⟨env,he⟩
    exact ⟨fun v => allValue (env v),(all_satisfies hn Q env).mpr he⟩

theorem finite_entails_iff (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    Entails finiteAlgebra Q ↔ LabelEntails Q := by
  constructor
  · intro he env hs
    have hh := he _ ((finite_satisfies hn Q env).mpr hs)
    simpa only [finite_eval,finite_value_le] using hh
  · intro he rho hs
    let env := fun v => finiteRoot (rho v)
    have hr : (fun v => finiteValue hn (env v)) = rho := funext (fun v => finite_value_surjective hn (rho v))
    have henv : LabelSatisfies Q env := (finite_satisfies hn Q env).mp (hr.symm ▸ hs)
    have hh := (finite_value_le hn _ _).mpr (he env henv)
    rw [← finite_eval hn env Q.left,← finite_eval hn env Q.right,hr] at hh
    exact hh

theorem all_entails_iff (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    Entails allAlgebra Q ↔ LabelEntails Q := by
  constructor
  · intro he env hs
    have hh := he _ ((all_satisfies hn Q env).mpr hs)
    simpa only [all_eval hn,all_value_le] using hh
  · intro he rho hs
    let env := fun v => (rho v).label []
    have hr : (fun v => allValue (env v)) = rho := funext (fun v => all_value_surjective hn (rho v))
    have henv : LabelSatisfies Q env := (all_satisfies hn Q env).mp (hr.symm ▸ hs)
    have hh := (all_value_le (arity := arity) _ _).mpr (he env henv)
    rw [← all_eval hn env Q.left,← all_eval hn env Q.right,hr] at hh
    exact hh

theorem regular_sat_iff (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    MultiConstructorTermSemantics.RegularSatisfiable Q ↔ LabelSatisfiable Q := by
  constructor
  · rintro ⟨rho,_,hs⟩
    exact (all_sat_iff hn Q).mp ⟨rho,hs⟩
  · intro hs
    obtain ⟨rho,hr⟩ := (all_sat_iff hn Q).mpr hs
    exact ⟨rho,fun v => all_regular hn (rho v),hr⟩

theorem regular_entails_iff (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    MultiConstructorTermSemantics.RegularEntails Q ↔ LabelEntails Q := by
  constructor
  · intro he
    apply (all_entails_iff hn Q).mp
    exact fun rho hs => he rho (fun v => all_regular hn (rho v)) hs
  · intro he rho _ hs
    exact (all_entails_iff hn Q).mpr he rho hs

end NSSE.MultiConstructorNullaryTerms
