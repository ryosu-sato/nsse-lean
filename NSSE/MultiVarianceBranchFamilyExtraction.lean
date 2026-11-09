import NSSE.MultiVarianceBranchExtraction
import Mathlib.Logic.Encodable.Pi

/-! Total constructive extraction from the finite supplied-word branch
family. Constructor encodings are representation data; numbered finite
signatures provide them automatically. No witness/rank/model is supplied. -/
namespace NSSE.MultiVarianceBranchFamilyExtraction
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceConstraints MultiVarianceOriginalSpine
open MultiVarianceSpineTokens MultiVarianceBranch MultiVarianceBranchFamily
open MultiVarianceBranchLocal MultiVarianceBranchLetters MultiVarianceBranchSpine
variable {H : Type*} {arity : H → Nat} {n D : Nat}

def frameEquiv (n : Nat) : Frame n ≃ Bool × (Fin n → Bool) × (Fin n → Bool) where
  toFun F := (F.sign,fun x => decide (x ∈ F.x),fun x => decide (x ∈ F.y))
  invFun p := ⟨p.1,Finset.univ.filter (fun x => p.2.1 x),Finset.univ.filter (fun x => p.2.2 x)⟩
  left_inv F := by
    cases F with
    | mk r x y =>
      dsimp only
      have hx : Finset.univ.filter (fun a => decide (a ∈ x))=x := by ext a; simp
      have hy : Finset.univ.filter (fun a => decide (a ∈ y))=y := by ext a; simp
      rw [hx,hy]
  right_inv p := by
    rcases p with ⟨r,x,y⟩
    dsimp only
    simp

instance frameEncodable : Encodable (Frame n) := Encodable.ofEquiv _ (frameEquiv n)

abbrev GraphCode (arity : H → Nat) (n : Nat) := Σ m : Nat, MultiVarianceSpineDecision.Code arity n m

variable [DecidableEq H] [Fintype H] [Encodable H] (pol : Polarity arity)

def select (Q : Query arity n) (w : List (Fin D))
    (hi : MultiVarianceBranchExtraction.inspectAny pol Q w=true) :
    {k : Key H n // MultiVarianceBranchSoundness.inspect pol (parameters Q k) w=true} :=
  @Encodable.chooseX _ (fun k : Key H n => MultiVarianceBranchSoundness.inspect pol (parameters Q k) w=true)
    inferInstance (fun _ => inferInstance) (by
      obtain ⟨C,hq,hc⟩ := (MultiVarianceBranchExtraction.inspectAny_correct pol Q w).mp hi
      refine ⟨key C,?_⟩
      change MultiVarianceBranchSoundness.inspect pol (parameters Q (key C)) w=true
      rw [← hq,parameters_key]
      exact hc)

def selectedCode (Q : Query arity n) (w : List (Fin D))
    (hi : MultiVarianceBranchExtraction.inspectAny pol Q w=true) : GraphCode arity n :=
  ⟨_,MultiVarianceBranchExtraction.code pol (parameters Q (select pol Q w hi).val) w⟩

def realize (M : GraphCode arity n) (x : Fin n) : MultiVarianceTrees.Tree pol :=
  MultiVarianceSpineDecision.realize pol M.2 x

theorem selected_spec (Q : Query arity n) (w : List (Fin D))
    (hi : MultiVarianceBranchExtraction.inspectAny pol Q w=true) :
    Satisfies Q.constraints (realize pol (selectedCode pol Q w hi)) ∧
      ¬realize pol (selectedCode pol Q w hi) Q.left ≤ realize pol (selectedCode pol Q w hi) Q.right :=
  MultiVarianceBranchExtraction.code_spec pol (parameters Q (select pol Q w hi).val) w (select pol Q w hi).property

theorem selected_size (Q : Query arity n) (w : List (Fin D))
    (hi : MultiVarianceBranchExtraction.inspectAny pol Q w=true) :
    (selectedCode pol Q w hi).1=n+2*w.length+2 := by
  let C := parameters Q (select pol Q w hi).val
  have hc := ((MultiVarianceBranchSoundness.inspect_correct pol C w).mp (select pol Q w hi).property).2.1
  change count n (spine pol C w).depth = _
  rw [depth_spine pol C w (local_arities pol C _ w ((complete_iff pol C w).mp hc))]
  rfl

omit [DecidableEq H] [Fintype H] [Encodable H] in
theorem realize_regular (M : GraphCode arity n) (x : Fin n) :
    MultiConstructorRegularTrees.Regular (realize pol M x).raw :=
  MultiVarianceSpineDecision.realize_regular pol M.2 x

def extract (Q : Query arity n) (w : List (Fin D)) : Option (GraphCode arity n) :=
  if hi : MultiVarianceBranchExtraction.inspectAny pol Q w=true then some (selectedCode pol Q w hi) else none

theorem none_iff (Q : Query arity n) (w : List (Fin D)) :
    extract pol Q w=none ↔ MultiVarianceBranchExtraction.inspectAny pol Q w=false := by
  unfold extract
  split_ifs with hi
  · simp only [Option.some_ne_none,hi,Bool.true_eq_false]
  · simp only [true_iff]
    exact Bool.eq_false_iff.mpr hi

theorem some_spec (Q : Query arity n) (w : List (Fin D)) (M : GraphCode arity n)
    (he : extract pol Q w=some M) :
    Satisfies Q.constraints (realize pol M) ∧ ¬realize pol M Q.left ≤ realize pol M Q.right ∧
      ∀ x, MultiConstructorRegularTrees.Regular (realize pol M x).raw := by
  unfold extract at he
  split_ifs at he with hi
  · have hh := Option.some.inj he
    subst M
    exact ⟨(selected_spec pol Q w hi).1,(selected_spec pol Q w hi).2,realize_regular pol _⟩

theorem some_size (Q : Query arity n) (w : List (Fin D)) (M : GraphCode arity n)
    (he : extract pol Q w=some M) : M.1=n+2*w.length+2 := by
  unfold extract at he
  split_ifs at he with hi
  · have hh := Option.some.inj he
    subst M
    exact selected_size pol Q w hi

theorem some_states (Q : Query arity n) (w : List (Fin D)) (M : GraphCode arity n)
    (he : extract pol Q w=some M) :
    Fintype.card (MultiVarianceModelTokens.State M.1)=4^(n+2*w.length+2) := by
  rw [MultiVarianceModelTokens.card_states,some_size pol Q w M he]

theorem returns_iff (Q : Query arity n) (w : List (Fin D)) :
    (∃ M, extract pol Q w=some M) ↔ MultiVarianceBranchExtraction.inspectAny pol Q w=true := by
  rw [← Bool.not_eq_false,← none_iff]
  cases extract pol Q w <;> simp

def extractNumbered {h : Nat} {arity : Fin h → Nat} (pol : Polarity arity)
    (Q : Query arity n) (w : List (Fin D)) : Option (GraphCode arity n) := extract pol Q w

end NSSE.MultiVarianceBranchFamilyExtraction
