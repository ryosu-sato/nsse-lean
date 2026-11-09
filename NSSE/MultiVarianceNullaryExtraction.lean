import NSSE.MultiVarianceNullaryDecision
import NSSE.MultiVariancePositiveTermExtraction
import NSSE.MultiConstructorNullaryExtraction

/-! Original nullary countermodels selected from the finite label domain.
Graph roots are singleton first-token sets; native values have height <=1. -/
namespace NSSE.MultiVarianceNullaryExtraction
open MultiConstructorTerms (Query)
open MultiConstructorNullaryValues (finiteValue)
open MultiConstructorNullaryExtraction (select)
open MultiConstructorNullaryDecision (inspect)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceTerms MultiVarianceNullaryTerms
open MultiVarianceFiniteTrees (Value embed)
open MultiVarianceBranchFamilyExtraction (GraphCode realize)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def labelCode (env : Fin n → Label H) : GraphCode arity n :=
  ⟨n,⟨⟨fun S => S.1.sup env,fun S _ => S⟩,fun x => ({x},∅)⟩⟩

variable (pol : Polarity arity)

theorem code_value (hn : ∀ h, arity h=0) (env : Fin n → Label H) (x : Fin n) :
    realize pol (labelCode (arity := arity) env) x=value pol (env x) := by
  rw [← value_surjective pol hn (realize pol (labelCode env) x)]
  apply congrArg (value pol)
  change ({x} : Finset (Fin n)).sup env=env x
  exact Finset.sup_singleton

variable [Fintype H] [Encodable H]

def finiteNegative (hn : ∀ h, arity h=0) (Q : Query arity n) (hi : inspect Q=false) : Fin n → Value arity :=
  fun x => finiteValue hn ((select Q hi).val x)
def allNegative (Q : Query arity n) (hi : inspect Q=false) : GraphCode arity n := labelCode (select Q hi).val

theorem finiteNegative_correct (hn : ∀ h, arity h=0) (Q : Query arity n) (hi : inspect Q=false) :
    Satisfies pol Q (fun x => embed pol (finiteNegative hn Q hi x)) ∧
      ¬embed pol (finiteEval (finiteNegative hn Q hi) Q.left)≤embed pol (finiteEval (finiteNegative hn Q hi) Q.right) := by
  have hp := (select Q hi).property
  have he : (fun x => embed pol (finiteNegative hn Q hi x))=(fun x => value pol ((select Q hi).val x)) :=
    funext (fun x => finite_value pol hn _)
  rw [finite_eval_embed,finite_eval_embed,he,eval_value pol hn,eval_value pol hn,value_le pol hn]
  exact ⟨(satisfies_value pol hn Q _).mpr hp.1,hp.2⟩

theorem allNegative_correct (hn : ∀ h, arity h=0) (Q : Query arity n) (hi : inspect Q=false) :
    Satisfies pol Q (realize pol (allNegative Q hi)) ∧
      ¬eval pol (realize pol (allNegative Q hi)) Q.left≤eval pol (realize pol (allNegative Q hi)) Q.right ∧
      ∀ x, MultiConstructorRegularTrees.Regular (realize pol (allNegative Q hi) x).raw := by
  have he : realize pol (allNegative Q hi)=(fun x => value pol ((select Q hi).val x)) :=
    funext (code_value pol hn (select Q hi).val)
  rw [he]
  have hp := (select Q hi).property
  exact ⟨(satisfies_value pol hn Q _).mpr hp.1,
    by simpa only [eval_value pol hn,value_le pol hn] using hp.2,fun x => all_regular pol hn _⟩

def extractFinite (hn : ∀ h, arity h=0) (Q : Query arity n) : Option (Fin n → Value arity) :=
  if hi : inspect Q=false then some (finiteNegative hn Q hi) else none
def extractAll (Q : Query arity n) : Option (GraphCode arity n) :=
  if hi : inspect Q=false then some (allNegative Q hi) else none

theorem finite_none (hn : ∀ h, arity h=0) (Q : Query arity n) : extractFinite hn Q=none ↔ FiniteEntails pol Q := by
  unfold extractFinite
  split_ifs with hi
  · simp only [Option.some_ne_none,false_iff]
    intro he
    have hh := (MultiVarianceNullaryDecision.inspectFinite_correct pol hn Q).mpr he
    change inspect Q=true at hh
    rw [hi] at hh
    cases hh
  · simp only [true_iff]
    exact (MultiVarianceNullaryDecision.inspectFinite_correct pol hn Q).mp (Bool.eq_true_of_not_eq_false hi)

theorem all_none (hn : ∀ h, arity h=0) (Q : Query arity n) : extractAll Q=none ↔ Entails pol Q := by
  unfold extractAll
  split_ifs with hi
  · simp only [Option.some_ne_none,false_iff]
    intro he
    have hh := (MultiVarianceNullaryDecision.inspectAll_correct pol hn Q).mpr he
    change inspect Q=true at hh
    rw [hi] at hh
    cases hh
  · simp only [true_iff]
    exact (MultiVarianceNullaryDecision.inspectAll_correct pol hn Q).mp (Bool.eq_true_of_not_eq_false hi)

theorem finite_some (hn : ∀ h, arity h=0) (Q : Query arity n) (rho : Fin n → Value arity)
    (he : extractFinite hn Q=some rho) : Satisfies pol Q (fun x => embed pol (rho x)) ∧
      ¬embed pol (finiteEval rho Q.left)≤embed pol (finiteEval rho Q.right) := by
  unfold extractFinite at he
  split_ifs at he with hi
  have hr := Option.some.inj he
  subst rho
  exact finiteNegative_correct pol hn Q hi

theorem all_some (hn : ∀ h, arity h=0) (Q : Query arity n) (M : GraphCode arity n) (he : extractAll Q=some M) :
    Satisfies pol Q (realize pol M) ∧ ¬eval pol (realize pol M) Q.left≤eval pol (realize pol M) Q.right ∧
      ∀ x, MultiConstructorRegularTrees.Regular (realize pol M x).raw := by
  unfold extractAll at he
  split_ifs at he with hi
  have hr := Option.some.inj he
  subst M
  exact allNegative_correct pol hn Q hi

theorem finite_height (hn : ∀ h, arity h=0) (Q : Query arity n) (rho : Fin n → Value arity)
    (he : extractFinite hn Q=some rho) (x : Fin n) : MultiConstructorFiniteTrees.height (rho x)≤1 := by
  unfold extractFinite at he
  split_ifs at he with hi
  have hr := Option.some.inj he
  subst rho
  exact MultiConstructorNullaryValues.finite_height hn _

theorem all_states (Q : Query arity n) (M : GraphCode arity n) (he : extractAll Q=some M) :
    Fintype.card (MultiVarianceModelTokens.State M.1)=4^n := by
  unfold extractAll at he
  split_ifs at he with hi
  have hr := Option.some.inj he
  subst M
  exact MultiVarianceModelTokens.card_states

end NSSE.MultiVarianceNullaryExtraction
