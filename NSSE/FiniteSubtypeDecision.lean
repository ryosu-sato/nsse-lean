import NSSE.FiniteSubtypeSmallModel

/-! # A total satisfiability decision for the original finite-tree constraints

Compute the input-only finite shape model, then check all original literals.
The small-model theorem proves the negative direction too. There is no
satisfiability oracle, search termination premise, or supplied finite bound.
-/

namespace NSSE.FiniteSubtypeDecision

open FiniteSubtypeTrees FiniteSubtypeSmallModel SubtypeConstraints

variable {n d : Nat}

def leBool : Tree d → Tree d → Bool
  | .bot, _ => true
  | .top, .top => true
  | .top, .bot => false
  | .top, .node _ => false
  | .node _, .bot => false
  | .node _, .top => true
  | .node a, .node b => (List.finRange d).all (fun i => leBool (a i) (b i))

theorem leBool_correct (a b : Tree d) : leBool a b = true ↔ a ≤ b := by
  induction a generalizing b with
  | bot => exact ⟨fun _ => bot_le, fun _ => rfl⟩
  | top =>
      cases b with
      | bot => constructor <;> intro h <;> cases h
      | top => exact ⟨fun _ => le_rfl, fun _ => rfl⟩
      | node b => constructor <;> intro h <;> cases h
  | node a ih =>
      cases b with
      | bot => constructor <;> intro h <;> cases h
      | top => exact ⟨fun _ => le_top, fun _ => rfl⟩
      | node b => simp only [leBool, List.all_eq_true, List.mem_finRange, true_implies,
          ih, node_le_node]

def checkSolution (φ : Constraints n d) (ρ : Fin n → Tree d) : Bool :=
  φ.upper.all (fun a => leBool (ρ a.1) (.node (fun i => ρ (a.2 i)))) &&
  φ.lower.all (fun a => leBool (.node (fun i => ρ (a.2 i))) (ρ a.1)) &&
  φ.bot.all (fun x => leBool (ρ x) .bot) &&
  φ.top.all (fun x => leBool .top (ρ x))

theorem checkSolution_correct (φ : Constraints n d) (ρ : Fin n → Tree d) :
    checkSolution φ ρ = true ↔ Satisfies (constructor d) φ ρ := by
  have hb (t : Tree d) : t ≤ Tree.bot ↔ t = (⊥ : Tree d) := eq_bot_iff.symm
  have ht (t : Tree d) : Tree.top ≤ t ↔ t = (⊤ : Tree d) := eq_top_iff.symm
  simp only [checkSolution, Bool.and_eq_true, List.all_eq_true, leBool_correct, hb, ht,
    Satisfies, constructor, and_assoc]

def decideSatisfiable (φ : Constraints n d) : Bool := checkSolution φ (model φ)

theorem decideSatisfiable_correct (φ : Constraints n d) :
    decideSatisfiable φ = true ↔ Satisfiable (constructor d) φ :=
  (checkSolution_correct φ (model φ)).trans (satisfiable_iff_model φ).symm

theorem decideSatisfiable_false (φ : Constraints n d) :
    decideSatisfiable φ = false ↔ ¬ Satisfiable (constructor d) φ := by
  rw [← decideSatisfiable_correct]
  cases decideSatisfiable φ <;> simp

def satisfiabilityDecision (φ : Constraints n d) : Decidable (Satisfiable (constructor d) φ) :=
  decidable_of_iff (decideSatisfiable φ = true) (decideSatisfiable_correct φ)

/-- A general positive-arity cyclic family, not a bounded enumeration:
the finite-tree decision really rejects the two-sided self-node equation. -/
def selfNode (d : Nat) : Constraints 1 d where
  upper := [(0, fun _ => 0)]
  lower := [(0, fun _ => 0)]
  bot := []
  top := []

theorem selfNode_unsatisfiable (hd : 0 < d) : ¬ Satisfiable (constructor d) (selfNode d) := by
  rintro ⟨ρ,hρ⟩
  have hu := hρ.1 (0, fun _ => 0) (by simp [selfNode])
  have hl := hρ.2.1 (0, fun _ => 0) (by simp [selfNode])
  exact no_two_way_self_node hd (ρ 0) ⟨hu,hl⟩

theorem selfNode_decision (hd : 0 < d) : decideSatisfiable (selfNode d) = false :=
  (decideSatisfiable_false (selfNode d)).mpr (selfNode_unsatisfiable hd)

end NSSE.FiniteSubtypeDecision
