import NSSE.SubtypeTerms
import NSSE.ContraConstraints

/-! # Original nested terms under the contravariant constructor law (S7)

The SYNTAX is reused verbatim from the covariant development: `SubtypeTerms.Term n d`
(`var`, `bot`, `top`, `node`), `SubtypeTerms.Literal` (`le`, `eq`) and
`SubtypeTerms.Query` (premises, query `left ≤ right`). These are signature-agnostic:
nothing in them refers to the order or to the constructor law.

The SEMANTICS is new: terms are evaluated through a `ContraConstructor` (the
contravariant law of the polarity vector `POL`), and `Holds` / `Satisfies` /
`Satisfiable` / `Entails` are defined DIRECTLY by evaluation, before any flattening.
The three tree kinds are

* arbitrary raw trees: `F = treeConstructor POL` on `CTree POL`;
* regular raw trees: valuations with `∀ x, CRegular (ρ x)` (`RegularSatisfiable`,
  `RegularEntails` below);
* finite trees: `F = finiteConstructor POL` on `FTree POL`.
-/

namespace NSSE.ContraTermSemantics

open SubtypeTerms (Term Literal Query inequalities expanded)
open ContraTrees ContraFiniteTrees ContraRegularTrees ContraConstraints

variable {n d : Nat} {POL : Polarity d}

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

/-- Evaluation of an original nested term through a contravariant constructor. -/
def eval (F : ContraConstructor T POL) (ρ : Fin n → T) : Term n d → T
  | .var x => ρ x
  | .bot => ⊥
  | .top => ⊤
  | .node children => F.node (fun i => eval F ρ (children i))

@[simp] theorem eval_var (F : ContraConstructor T POL) (ρ : Fin n → T) (x : Fin n) :
    eval F ρ (.var x) = ρ x := rfl
@[simp] theorem eval_bot (F : ContraConstructor T POL) (ρ : Fin n → T) :
    eval F ρ (.bot : Term n d) = ⊥ := rfl
@[simp] theorem eval_top (F : ContraConstructor T POL) (ρ : Fin n → T) :
    eval F ρ (.top : Term n d) = ⊤ := rfl
@[simp] theorem eval_node (F : ContraConstructor T POL) (ρ : Fin n → T) (c : Fin d → Term n d) :
    eval F ρ (.node c) = F.node (fun i => eval F ρ (c i)) := rfl

/-- A premise literal holds: `≤` in the contravariant order, or equality. -/
def Holds (F : ContraConstructor T POL) (ρ : Fin n → T) : Literal n d → Prop
  | .le a b => eval F ρ a ≤ eval F ρ b
  | .eq a b => eval F ρ a = eval F ρ b

def Satisfies (F : ContraConstructor T POL) (Q : Query n d) (ρ : Fin n → T) : Prop :=
  ∀ l ∈ Q.premises, Holds F ρ l

def Satisfiable (F : ContraConstructor T POL) (Q : Query n d) : Prop := ∃ ρ, Satisfies F Q ρ

def Entails (F : ContraConstructor T POL) (Q : Query n d) : Prop :=
  ∀ ρ, Satisfies F Q ρ → eval F ρ Q.left ≤ eval F ρ Q.right

theorem holds_iff_inequalities (F : ContraConstructor T POL) (ρ : Fin n → T) (l : Literal n d) :
    Holds F ρ l ↔ ∀ p ∈ inequalities l, eval F ρ p.1 ≤ eval F ρ p.2 := by
  have heq (a b : T) : a = b ↔ a ≤ b ∧ b ≤ a :=
    ⟨fun h => ⟨le_of_eq h, le_of_eq h.symm⟩, fun h => le_antisymm h.1 h.2⟩
  cases l <;> simp [Holds, inequalities, heq]

/-- Satisfaction is satisfaction of the expanded inequality list (equalities as two
inequalities). -/
theorem satisfies_iff_expanded (F : ContraConstructor T POL) (Q : Query n d) (ρ : Fin n → T) :
    Satisfies F Q ρ ↔ ∀ p ∈ expanded Q, eval F ρ p.1 ≤ eval F ρ p.2 := by
  simp only [Satisfies, expanded, List.forall_mem_flatMap, holds_iff_inequalities]

theorem entails_of_unsatisfiable (F : ContraConstructor T POL) (Q : Query n d)
    (h : ¬ Satisfiable F Q) : Entails F Q :=
  fun ρ hρ => False.elim (h ⟨ρ, hρ⟩)

/-- Values of terms stay in any class closed under `⊥`, `⊤` and the constructor. -/
theorem eval_closed (F : ContraConstructor T POL) (P : T → Prop)
    (hb : P ⊥) (ht : P ⊤) (hn : ∀ c, (∀ i, P (c i)) → P (F.node c))
    (ρ : Fin n → T) (hρ : ∀ x, P (ρ x)) (t : Term n d) : P (eval F ρ t) := by
  induction t with
  | var x => exact hρ x
  | bot => exact hb
  | top => exact ht
  | node children ih => exact hn _ ih

/-- Transport of term evaluation and satisfaction along an order embedding preserving
`⊥`, `⊤` and the constructor. -/
theorem eval_map {T' : Type*} [PartialOrder T'] [OrderBot T'] [OrderTop T']
    (F : ContraConstructor T POL) (F' : ContraConstructor T' POL) (g : T ↪o T')
    (hbot : g ⊥ = ⊥) (htop : g ⊤ = ⊤) (hnode : ∀ a, g (F.node a) = F'.node (fun i => g (a i)))
    (ρ : Fin n → T) (t : Term n d) :
    eval F' (fun x => g (ρ x)) t = g (eval F ρ t) := by
  induction t with
  | var x => rfl
  | bot => exact hbot.symm
  | top => exact htop.symm
  | node c ih =>
      simp only [eval_node, hnode]
      exact congrArg F'.node (funext ih)

theorem satisfies_map {T' : Type*} [PartialOrder T'] [OrderBot T'] [OrderTop T']
    (F : ContraConstructor T POL) (F' : ContraConstructor T' POL) (g : T ↪o T')
    (hbot : g ⊥ = ⊥) (htop : g ⊤ = ⊤) (hnode : ∀ a, g (F.node a) = F'.node (fun i => g (a i)))
    (Q : Query n d) (ρ : Fin n → T) :
    Satisfies F Q ρ ↔ Satisfies F' Q (fun x => g (ρ x)) := by
  simp only [satisfies_iff_expanded, eval_map F F' g hbot htop hnode, g.le_iff_le]

end Semantics

/-! ## Regular trees and the relations between the three kinds -/

def RegularSatisfiable (POL : Polarity d) (Q : Query n d) : Prop :=
  ∃ ρ : Fin n → CTree POL, (∀ x, CRegular (ρ x)) ∧ Satisfies (treeConstructor POL) Q ρ

def RegularEntails (POL : Polarity d) (Q : Query n d) : Prop :=
  ∀ ρ : Fin n → CTree POL, (∀ x, CRegular (ρ x)) → Satisfies (treeConstructor POL) Q ρ →
    eval (treeConstructor POL) ρ Q.left ≤ eval (treeConstructor POL) ρ Q.right

theorem eval_regular (ρ : Fin n → CTree POL) (hρ : ∀ x, CRegular (ρ x)) (t : Term n d) :
    CRegular (eval (treeConstructor POL) ρ t) :=
  eval_closed (treeConstructor POL) CRegular cregular_bot cregular_top
    (fun _ h => cregular_node h) ρ hρ t

theorem eval_toC (ρ : Fin n → FTree POL) (t : Term n d) :
    eval (treeConstructor POL) (fun x => toC (ρ x)) t = toC (eval (finiteConstructor POL) ρ t) :=
  eval_map (finiteConstructor POL) (treeConstructor POL) (toCEmb POL) rfl rfl (fun _ => rfl) ρ t

/-- Finite term satisfaction is satisfaction of the embedded raw valuation. -/
theorem finite_satisfies_iff (Q : Query n d) (ρ : Fin n → FTree POL) :
    Satisfies (finiteConstructor POL) Q ρ ↔
      Satisfies (treeConstructor POL) Q (fun x => toC (ρ x)) :=
  satisfies_map (finiteConstructor POL) (treeConstructor POL) (toCEmb POL) rfl rfl
    (fun _ => rfl) Q ρ

theorem regularSatisfiable_of_finite {Q : Query n d}
    (h : Satisfiable (finiteConstructor POL) Q) : RegularSatisfiable POL Q := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨fun x => toC (ρ x), fun x => cregular_toC (ρ x), (finite_satisfies_iff Q ρ).mp hρ⟩

theorem satisfiable_of_regularSatisfiable {Q : Query n d} (h : RegularSatisfiable POL Q) :
    Satisfiable (treeConstructor POL) Q := by
  obtain ⟨ρ, _, hρ⟩ := h
  exact ⟨ρ, hρ⟩

theorem regularEntails_of_entails (Q : Query n d) (h : Entails (treeConstructor POL) Q) :
    RegularEntails POL Q :=
  fun ρ _ hρ => h ρ hρ

theorem finiteEntails_of_regularEntails (Q : Query n d) (h : RegularEntails POL Q) :
    Entails (finiteConstructor POL) Q := by
  intro ρ hρ
  rw [← toC_le_iff, ← eval_toC, ← eval_toC]
  exact h (fun x => toC (ρ x)) (fun x => cregular_toC (ρ x)) ((finite_satisfies_iff Q ρ).mp hρ)

end NSSE.ContraTermSemantics
