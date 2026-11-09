import NSSE.MultiConstructorNullaryDecision
import NSSE.MultiConstructorWitnessCode
import NSSE.MultiConstructorGraphCode

/-! Actual original countermodels for the all-nullary branch. Finite
values have height at most one; graph roots are singleton original tokens. -/
namespace NSSE.MultiConstructorNullaryExtraction
open MultiConstructorTerms MultiConstructorNullaryTerms MultiConstructorNullaryValues
open MultiConstructorNullaryDecision
open MultiConstructorTrees (Label)
open MultiConstructorConstraints (finiteAlgebra allAlgebra)
open MultiConstructorGraphCode (Code)
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def labelCode (env : Fin n → Label H) : Code arity n where
  basisSize := n
  graph := ⟨fun S => S.sup env,fun S _ => S⟩
  roots v := {v}

theorem code_unfold (hn : ∀ h, arity h = 0) (env : Fin n → Label H) (v : Fin n) :
    MultiConstructorGraphCode.unfold (labelCode (arity := arity) env) v = allValue (env v) := by
  rw [← all_value_surjective hn (MultiConstructorGraphCode.unfold (labelCode env) v)]
  congr 1
  change ({v} : Finset (Fin n)).sup env = env v
  exact Finset.sup_singleton

variable [Fintype H] [Encodable H]

def select (Q : Query arity n) (hi : inspect Q = false) : {env : Fin n → Label H // Bad Q env} :=
  @Encodable.chooseX _ (Bad Q) inferInstance (badDecision Q) (negative_assignment Q hi)

def finiteNegative (hn : ∀ h, arity h = 0) (Q : Query arity n) (hi : inspect Q = false) :
    Fin n → MultiConstructorFiniteTrees.Tree arity := fun v => finiteValue hn ((select Q hi).val v)

def allNegative (Q : Query arity n) (hi : inspect Q = false) : Code arity n := labelCode (select Q hi).val

theorem finiteNegative_correct (hn : ∀ h, arity h = 0) (Q : Query arity n) (hi : inspect Q = false) :
    Satisfies finiteAlgebra Q (finiteNegative hn Q hi) ∧
      ¬eval finiteAlgebra (finiteNegative hn Q hi) Q.left ≤ eval finiteAlgebra (finiteNegative hn Q hi) Q.right := by
  have hp := (select Q hi).property
  refine ⟨(finite_satisfies hn Q _).mpr hp.1,?_⟩
  change ¬eval finiteAlgebra (fun v => finiteValue hn ((select Q hi).val v)) Q.left ≤
    eval finiteAlgebra (fun v => finiteValue hn ((select Q hi).val v)) Q.right
  rw [finite_eval,finite_eval,finite_value_le]
  exact hp.2

theorem allNegative_correct (hn : ∀ h, arity h = 0) (Q : Query arity n) (hi : inspect Q = false) :
    (∀ v, MultiConstructorRegularTrees.Regular (MultiConstructorGraphCode.unfold (allNegative Q hi) v)) ∧
      Satisfies allAlgebra Q (MultiConstructorGraphCode.unfold (allNegative Q hi)) ∧
      ¬eval allAlgebra (MultiConstructorGraphCode.unfold (allNegative Q hi)) Q.left ≤
        eval allAlgebra (MultiConstructorGraphCode.unfold (allNegative Q hi)) Q.right := by
  have hu : MultiConstructorGraphCode.unfold (allNegative Q hi) = (fun v => allValue ((select Q hi).val v)) :=
    funext (code_unfold hn (select Q hi).val)
  rw [hu]
  have hp := (select Q hi).property
  refine ⟨fun v => all_regular hn _,(all_satisfies hn Q _).mpr hp.1,?_⟩
  simpa only [all_eval hn,all_value_le] using hp.2

def extractFinite (hn : ∀ h, arity h = 0) (Q : Query arity n) : Option (Fin n → MultiConstructorFiniteTrees.Tree arity) :=
  if hi : inspect Q = false then some (finiteNegative hn Q hi) else none

def extractAll (Q : Query arity n) : Option (Code arity n) :=
  if hi : inspect Q = false then some (allNegative Q hi) else none

theorem finite_none (hn : ∀ h, arity h = 0) (Q : Query arity n) : extractFinite hn Q = none ↔ Entails finiteAlgebra Q := by
  unfold extractFinite
  split_ifs with hi
  · simp only [Option.some_ne_none,false_iff]
    exact (inspectFinite_false hn Q).mp hi
  · simp only [true_iff]
    exact (inspectFinite_correct hn Q).mp (Bool.eq_true_of_not_eq_false hi)

theorem all_none (hn : ∀ h, arity h = 0) (Q : Query arity n) : extractAll Q = none ↔ Entails allAlgebra Q := by
  unfold extractAll
  split_ifs with hi
  · simp only [Option.some_ne_none,false_iff]
    exact (inspectAll_false hn Q).mp hi
  · simp only [true_iff]
    exact (inspectAll_correct hn Q).mp (Bool.eq_true_of_not_eq_false hi)

theorem regular_none (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    extractAll Q = none ↔ MultiConstructorTermSemantics.RegularEntails Q :=
  (all_none hn Q).trans ((all_entails_iff hn Q).trans (regular_entails_iff hn Q).symm)

theorem finite_some (hn : ∀ h, arity h = 0) (Q : Query arity n) (rho : Fin n → MultiConstructorFiniteTrees.Tree arity)
    (he : extractFinite hn Q = some rho) : Satisfies finiteAlgebra Q rho ∧ ¬eval finiteAlgebra rho Q.left ≤ eval finiteAlgebra rho Q.right := by
  unfold extractFinite at he
  split_ifs at he with hi
  have hr : finiteNegative hn Q hi = rho := Option.some.inj he
  exact hr ▸ finiteNegative_correct hn Q hi

theorem all_some (hn : ∀ h, arity h = 0) (Q : Query arity n) (C : Code arity n) (he : extractAll Q = some C) :
    (∀ v, MultiConstructorRegularTrees.Regular (MultiConstructorGraphCode.unfold C v)) ∧
      Satisfies allAlgebra Q (MultiConstructorGraphCode.unfold C) ∧
      ¬eval allAlgebra (MultiConstructorGraphCode.unfold C) Q.left ≤ eval allAlgebra (MultiConstructorGraphCode.unfold C) Q.right := by
  unfold extractAll at he
  split_ifs at he with hi
  have hr : allNegative Q hi = C := Option.some.inj he
  exact hr ▸ allNegative_correct hn Q hi

theorem finite_height_bound (hn : ∀ h, arity h = 0) (Q : Query arity n) (rho : Fin n → MultiConstructorFiniteTrees.Tree arity)
    (he : extractFinite hn Q = some rho) (v : Fin n) : MultiConstructorFiniteTrees.height (rho v) ≤ 1 := by
  unfold extractFinite at he
  split_ifs at he with hi
  have hr : finiteNegative hn Q hi = rho := Option.some.inj he
  rw [← hr]
  exact finite_height hn _

theorem all_basis (Q : Query arity n) (C : Code arity n) (he : extractAll Q = some C) : C.basisSize = n := by
  unfold extractAll at he
  split_ifs at he with hi
  have hr : allNegative Q hi = C := Option.some.inj he
  rw [← hr]
  rfl

theorem all_states (Q : Query arity n) (C : Code arity n) (he : extractAll Q = some C) :
    Fintype.card (MultiConstructorTokens.Tokens C.basisSize) = 2^n := by
  rw [MultiConstructorGraphCode.card_states,all_basis Q C he]

theorem finite_returns_iff (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    (∃ rho, extractFinite hn Q = some rho) ↔ ¬Entails finiteAlgebra Q := by
  rw [← finite_none hn Q]
  cases extractFinite hn Q <;> simp

theorem all_returns_iff (hn : ∀ h, arity h = 0) (Q : Query arity n) :
    (∃ C, extractAll Q = some C) ↔ ¬Entails allAlgebra Q := by
  rw [← all_none hn Q]
  cases extractAll Q <;> simp

end NSSE.MultiConstructorNullaryExtraction
