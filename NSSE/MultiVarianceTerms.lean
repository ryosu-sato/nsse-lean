import NSSE.MultiConstructorTermDefinitions
import NSSE.MultiVarianceFiniteTrees

/-! Original finite nested terms with head-dependent signed semantics.
Only syntax/layout data are reused from the covariant development. -/
namespace NSSE.MultiVarianceTerms
open MultiConstructorTerms (Term Literal Query inequalities expanded)
open MultiVarianceEncoding MultiVarianceTrees
open MultiVarianceFiniteTrees (Value embed)
variable {H : Type*} {arity : H → Nat} {n : Nat} (pol : Polarity arity)

def eval (rho : Fin n → Tree pol) : Term arity n → Tree pol
  | .var x => rho x
  | .bot => ⊥
  | .top => ⊤
  | .node h c => node h (fun i => eval rho (c i))

def finiteEval (rho : Fin n → Value arity) : Term arity n → Value arity
  | .var x => rho x
  | .bot => .bot
  | .top => .top
  | .node h c => .node h (fun i => finiteEval rho (c i))

theorem finite_eval_embed (rho : Fin n → Value arity) (t : Term arity n) :
    embed pol (finiteEval rho t)=eval pol (fun x => embed pol (rho x)) t := by
  induction t with
  | var x => rfl
  | bot => rfl
  | top => rfl
  | node h c ih => exact congrArg (node h) (funext ih)

def Holds (rho : Fin n → Tree pol) : Literal arity n → Prop
  | .le a b => eval pol rho a≤eval pol rho b
  | .eq a b => eval pol rho a=eval pol rho b
def Satisfies (Q : Query arity n) (rho : Fin n → Tree pol) : Prop := ∀ l∈Q.premises, Holds pol rho l
def Satisfiable (Q : Query arity n) : Prop := ∃ rho, Satisfies pol Q rho
def Entails (Q : Query arity n) : Prop := ∀ rho, Satisfies pol Q rho → eval pol rho Q.left≤eval pol rho Q.right
def ClassSatisfiable (P : Tree pol → Prop) (Q : Query arity n) : Prop :=
  ∃ rho, Satisfies pol Q rho ∧ ∀ x, P (rho x)
def ClassEntails (P : Tree pol → Prop) (Q : Query arity n) : Prop :=
  ∀ rho, Satisfies pol Q rho → (∀ x, P (rho x)) → eval pol rho Q.left≤eval pol rho Q.right
def RegularSatisfiable (Q : Query arity n) : Prop :=
  ClassSatisfiable pol (fun t => MultiConstructorRegularTrees.Regular t.raw) Q
def RegularEntails (Q : Query arity n) : Prop :=
  ClassEntails pol (fun t => MultiConstructorRegularTrees.Regular t.raw) Q
def FiniteSatisfiable (Q : Query arity n) : Prop :=
  ∃ rho : Fin n → Value arity, Satisfies pol Q (fun x => embed pol (rho x))
def FiniteEntails (Q : Query arity n) : Prop :=
  ∀ rho : Fin n → Value arity, Satisfies pol Q (fun x => embed pol (rho x)) →
    embed pol (finiteEval rho Q.left)≤embed pol (finiteEval rho Q.right)

theorem holds_iff_inequalities (rho : Fin n → Tree pol) (l : Literal arity n) :
    Holds pol rho l ↔ ∀ p∈inequalities l, eval pol rho p.1≤eval pol rho p.2 := by
  have heq (a b : Tree pol) : a=b ↔ a≤b ∧ b≤a :=
    ⟨fun h => ⟨le_of_eq h,le_of_eq h.symm⟩,fun h => le_antisymm h.1 h.2⟩
  cases l <;> simp [Holds,inequalities,heq]

theorem satisfies_iff_expanded (Q : Query arity n) (rho : Fin n → Tree pol) :
    Satisfies pol Q rho ↔ ∀ p∈expanded Q, eval pol rho p.1≤eval pol rho p.2 := by
  simp only [Satisfies,expanded,List.forall_mem_flatMap,holds_iff_inequalities]

theorem eval_closed (P : Tree pol → Prop) (hb : P ⊥) (ht : P ⊤)
    (hn : ∀ h c, (∀ i, P (c i)) → P (node h c)) (rho : Fin n → Tree pol)
    (hr : ∀ x, P (rho x)) (t : Term arity n) : P (eval pol rho t) := by
  induction t with
  | var x => exact hr x
  | bot => exact hb
  | top => exact ht
  | node h c ih => exact hn h _ ih

theorem eval_regular (rho : Fin n → Tree pol) (hr : ∀ x, MultiConstructorRegularTrees.Regular (rho x).raw)
    (t : Term arity n) : MultiConstructorRegularTrees.Regular (eval pol rho t).raw :=
  eval_closed pol (fun t => MultiConstructorRegularTrees.Regular t.raw)
    MultiConstructorRegularTrees.bot_regular MultiConstructorRegularTrees.top_regular
    (fun h c hc => MultiConstructorRegularTrees.node_regular h (fun i => (c i).raw) hc) rho hr t

theorem finite_sat_iff_class (Q : Query arity n) : FiniteSatisfiable pol Q ↔
    ClassSatisfiable pol (fun t => MultiVarianceClasses.Finite t.raw) Q := by
  constructor
  · rintro ⟨rho,hs⟩
    exact ⟨fun x => embed pol (rho x),hs,fun x => MultiVarianceFiniteTrees.embed_finite pol (rho x)⟩
  · rintro ⟨rho,hs,hf⟩
    choose f he using hf
    have hh : (fun x => embed pol (f x))=rho := funext (fun x => Tree.ext (he x))
    exact ⟨f,hh.symm ▸ hs⟩

theorem finite_entails_iff_class (Q : Query arity n) : FiniteEntails pol Q ↔
    ClassEntails pol (fun t => MultiVarianceClasses.Finite t.raw) Q := by
  constructor
  · intro h rho hs hf
    choose f he using hf
    have hh : (fun x => embed pol (f x))=rho := funext (fun x => Tree.ext (he x))
    simpa only [finite_eval_embed,hh] using h f (hh.symm ▸ hs)
  · intro h rho hs
    rw [finite_eval_embed,finite_eval_embed]
    exact h _ hs (fun x => MultiVarianceFiniteTrees.embed_finite pol (rho x))

end NSSE.MultiVarianceTerms
