import NSSE.MultiConstructorFiniteModel

/-! Executable original finite-tree satisfiability: construct the bounded
shape model and validate every literal. Constructor equality is sufficient;
neither a finite constructor universe nor a supplied semantic bound is used. -/
namespace NSSE.MultiConstructorFiniteDecision
open MultiConstructorConstraints MultiConstructorFiniteTrees MultiConstructorShapeGrammar
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n : Nat}

def leBool : Tree arity → Tree arity → Bool
  | .bot, _ => true
  | .top, .top => true
  | .top, .bot => false
  | .top, .node _ _ => false
  | .node _ _, .bot => false
  | .node _ _, .top => true
  | .node h a, .node g b =>
    if he : h = g then (List.finRange (arity h)).all (fun i => leBool (a i) (b (Fin.cast (congrArg arity he) i)))
    else false

theorem leBool_correct (a b : Tree arity) : leBool a b = true ↔ a ≤ b := by
  induction a generalizing b with
  | bot => exact ⟨fun _ => bot_le,fun _ => rfl⟩
  | top =>
    cases b with
    | bot => constructor <;> intro h <;> cases h
    | top => exact ⟨fun _ => le_rfl,fun _ => rfl⟩
    | node g b => constructor <;> intro h <;> cases h
  | node h a ih =>
    cases b with
    | bot => constructor <;> intro h <;> cases h
    | top => exact ⟨fun _ => le_top,fun _ => rfl⟩
    | node g b =>
      by_cases he : h = g
      · subst g
        simp [leBool,ih]
      · simp only [leBool,dif_neg he,Bool.false_eq_true,false_iff]
        exact fun hab => he (node_head_eq hab)

def checkSolution (phi : Constraints arity n) (rho : Fin n → Tree arity) : Bool :=
  phi.upper.all (fun a => leBool (rho a.parent) (.node a.head (fun i => rho (a.children i)))) &&
  phi.lower.all (fun a => leBool (.node a.head (fun i => rho (a.children i))) (rho a.parent)) &&
  phi.bot.all (fun x => leBool (rho x) .bot) &&
  phi.top.all (fun x => leBool .top (rho x))

theorem checkSolution_correct (phi : Constraints arity n) (rho : Fin n → Tree arity) :
    checkSolution phi rho = true ↔ Satisfies finiteAlgebra phi rho := by
  have hb (t : Tree arity) : t ≤ Tree.bot ↔ t = (⊥ : Tree arity) := eq_bot_iff.symm
  have ht (t : Tree arity) : Tree.top ≤ t ↔ t = (⊤ : Tree arity) := eq_top_iff.symm
  simp only [checkSolution,Bool.and_eq_true,List.all_eq_true,leBool_correct,hb,ht,
    Satisfies,finiteAlgebra,and_assoc]

def inspect (phi : Constraints arity n) : Bool := checkSolution phi (model phi)

theorem inspect_correct (phi : Constraints arity n) :
    inspect phi = true ↔ Satisfiable finiteAlgebra phi :=
  (checkSolution_correct phi (model phi)).trans (MultiConstructorFiniteModel.satisfiable_iff_model phi).symm

theorem inspect_false (phi : Constraints arity n) :
    inspect phi = false ↔ ¬Satisfiable finiteAlgebra phi := by
  rw [← inspect_correct]
  cases inspect phi <;> simp

def satisfiabilityDecision (phi : Constraints arity n) : Decidable (Satisfiable finiteAlgebra phi) :=
  decidable_of_iff (inspect phi = true) (inspect_correct phi)

theorem positive_model (phi : Constraints arity n) (hi : inspect phi = true) :
    Satisfies finiteAlgebra phi (model phi) ∧ ∀ x, height (model phi x) ≤ n*n :=
  MultiConstructorFiniteModel.small_model phi ((inspect_correct phi).mp hi)

def extract (phi : Constraints arity n) : Option (Fin n → Tree arity) :=
  if inspect phi then some (model phi) else none

theorem extract_none (phi : Constraints arity n) :
    extract phi = none ↔ ¬Satisfiable finiteAlgebra phi := by
  rw [← inspect_false]
  unfold extract
  cases inspect phi <;> simp

theorem extract_some (phi : Constraints arity n) (rho : Fin n → Tree arity)
    (he : extract phi = some rho) :
    Satisfies finiteAlgebra phi rho ∧ ∀ x, height (rho x) ≤ n*n := by
  unfold extract at he
  split_ifs at he with hi
  have hr : model phi = rho := Option.some.inj he
  rw [← hr]
  exact positive_model phi hi

end NSSE.MultiConstructorFiniteDecision
