import NSSE.ContraRegularTrees

/-! # Flat contravariant constraints: satisfaction and entailment

The SYNTAX is literally the covariant one (`SubtypeConstraints.Constraints`,
`Query`): the four flat literal forms `x ≤ f(ā)`, `f(ā) ≤ x`, `x = ⊥`, `x = ⊤`
and a query `x ≤ y`. Only the semantics changes: the constructor obeys the
contravariant law of the polarity vector `POL`.

Models: arbitrary raw trees (`CTree POL`), regular raw trees (`CRegular`), and
finite trees (`FTree POL`). The transported form says that a contravariant
valuation satisfies a system iff its `E`-image satisfies the covariant system in
which every contravariant child is dualized.

NOTE (main session, 2026-10-23): the naive sign split (`x⁺`, `x⁻ = dual x⁺`, then
the covariant decider) is NOT equivalent to contravariant entailment; the
transported condition below keeps the dualization inside the constructor, which
is not a covariant flat system over independent variables.
-/

namespace NSSE.ContraConstraints

open SubtypeConstraints (Constraints Query BoundLiteral)
open AbsorbingSubtypeTrees RegularSubtypeTrees ContraTrees ContraFiniteTrees ContraRegularTrees

variable {n d : Nat} {POL : Polarity d}

/-- The algebraic contravariant constructor law. -/
structure ContraConstructor (T : Type*) [PartialOrder T] (POL : Polarity d) where
  node : (Fin d → T) → T
  le_iff : ∀ a b, node a ≤ node b ↔
    ∀ i, (POL i = true → b i ≤ a i) ∧ (POL i = false → a i ≤ b i)

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

def Satisfies (F : ContraConstructor T POL) (φ : Constraints n d) (ρ : Fin n → T) : Prop :=
  (∀ a ∈ φ.upper, ρ a.1 ≤ F.node (fun i => ρ (a.2 i))) ∧
  (∀ a ∈ φ.lower, F.node (fun i => ρ (a.2 i)) ≤ ρ a.1) ∧
  (∀ x ∈ φ.bot, ρ x = ⊥) ∧ (∀ x ∈ φ.top, ρ x = ⊤)

def Satisfiable (F : ContraConstructor T POL) (φ : Constraints n d) : Prop := ∃ ρ, Satisfies F φ ρ

def Entails (F : ContraConstructor T POL) (Q : Query n d) : Prop :=
  ∀ ρ, Satisfies F Q.constraints ρ → ρ Q.left ≤ ρ Q.right

theorem entails_of_unsatisfiable (F : ContraConstructor T POL) (Q : Query n d)
    (h : ¬ Satisfiable F Q.constraints) : Entails F Q :=
  fun ρ hρ => False.elim (h ⟨ρ, hρ⟩)

/-- Transport of satisfaction along an order embedding that preserves `⊥`, `⊤`
and the constructor. -/
theorem satisfies_map {T' : Type*} [PartialOrder T'] [OrderBot T'] [OrderTop T']
    (F : ContraConstructor T POL) (F' : ContraConstructor T' POL) (g : T ↪o T')
    (hbot : g ⊥ = ⊥) (htop : g ⊤ = ⊤) (hnode : ∀ a, g (F.node a) = F'.node (fun i => g (a i)))
    (φ : Constraints n d) (ρ : Fin n → T) :
    Satisfies F φ ρ ↔ Satisfies F' φ (fun x => g (ρ x)) := by
  unfold Satisfies
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · refine forall₂_congr fun a _ => ?_
    rw [← hnode, g.le_iff_le]
  · refine forall₂_congr fun a _ => ?_
    rw [← hnode, g.le_iff_le]
  · refine forall₂_congr fun x _ => ?_
    rw [← hbot, g.injective.eq_iff]
  · refine forall₂_congr fun x _ => ?_
    rw [← htop, g.injective.eq_iff]

end Semantics

/-! ## The three models -/

/-- Arbitrary (possibly infinite) raw trees with the original order. -/
def treeConstructor (POL : Polarity d) : ContraConstructor (CTree POL) POL :=
  ⟨CTree.node, CTree.node_le_node⟩

/-- Finite trees with the structural order. -/
def finiteConstructor (POL : Polarity d) : ContraConstructor (FTree POL) POL :=
  ⟨FTree.node, FTree.node_le_node⟩

def RegularSatisfiable (POL : Polarity d) (φ : Constraints n d) : Prop :=
  ∃ ρ : Fin n → CTree POL, (∀ x, CRegular (ρ x)) ∧ Satisfies (treeConstructor POL) φ ρ

def RegularEntails (POL : Polarity d) (Q : Query n d) : Prop :=
  ∀ ρ : Fin n → CTree POL, (∀ x, CRegular (ρ x)) →
    Satisfies (treeConstructor POL) Q.constraints ρ → ρ Q.left ≤ ρ Q.right

/-- Finite satisfaction is satisfaction of the embedded raw valuation. -/
theorem finite_satisfies_iff (φ : Constraints n d) (ρ : Fin n → FTree POL) :
    Satisfies (finiteConstructor POL) φ ρ ↔
      Satisfies (treeConstructor POL) φ (fun x => toC (ρ x)) :=
  satisfies_map (finiteConstructor POL) (treeConstructor POL) (toCEmb POL) rfl rfl
    (fun _ => rfl) φ ρ

/-- A finite model is in particular a regular model. -/
theorem regularSatisfiable_of_finite {φ : Constraints n d}
    (h : Satisfiable (finiteConstructor POL) φ) : RegularSatisfiable POL φ := by
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨fun x => toC (ρ x), fun x => cregular_toC (ρ x), (finite_satisfies_iff φ ρ).mp hρ⟩

theorem regularSatisfiable_imp (φ : Constraints n d) (h : RegularSatisfiable POL φ) :
    Satisfiable (treeConstructor POL) φ := by
  obtain ⟨ρ, _, hρ⟩ := h
  exact ⟨ρ, hρ⟩

/-- Arbitrary-tree entailment implies regular-tree entailment implies
finite-tree entailment. -/
theorem regularEntails_of_entails (Q : Query n d) (h : Entails (treeConstructor POL) Q) :
    RegularEntails POL Q :=
  fun ρ _ hρ => h ρ hρ

theorem finiteEntails_of_regularEntails (Q : Query n d) (h : RegularEntails POL Q) :
    Entails (finiteConstructor POL) Q := by
  intro ρ hρ
  rw [← toC_le_iff]
  exact h (fun x => toC (ρ x)) (fun x => cregular_toC (ρ x)) ((finite_satisfies_iff _ ρ).mp hρ)

/-! ## Transport through the encoding `E` -/

/-- The dualized-child covariant condition satisfied by the `E`-image. -/
def EncSatisfies (POL : Polarity d) (φ : Constraints n d) (τ : Fin n → Tree d) : Prop :=
  (∀ a ∈ φ.upper, τ a.1 ≤ node (fun i => dualIf (POL i) (τ (a.2 i)))) ∧
  (∀ a ∈ φ.lower, node (fun i => dualIf (POL i) (τ (a.2 i))) ≤ τ a.1) ∧
  (∀ x ∈ φ.bot, τ x = ⊥) ∧ (∀ x ∈ φ.top, τ x = ⊤)

/-- **Transport.** A contravariant valuation satisfies `φ` iff its `E`-image
satisfies the dualized-child covariant condition. -/
theorem satisfies_iff_enc (φ : Constraints n d) (ρ : Fin n → CTree POL) :
    Satisfies (treeConstructor POL) φ ρ ↔ EncSatisfies POL φ (fun x => E POL (ρ x)) := by
  unfold Satisfies EncSatisfies
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · refine forall₂_congr fun a _ => ?_
    rw [← E_le_iff, show (treeConstructor POL).node = CTree.node from rfl, E_node]
  · refine forall₂_congr fun a _ => ?_
    rw [← E_le_iff, show (treeConstructor POL).node = CTree.node from rfl, E_node]
  · refine forall₂_congr fun x _ => ?_
    rw [← E_bot (POL := POL), (E POL).injective.eq_iff]
  · refine forall₂_congr fun x _ => ?_
    rw [← E_top (POL := POL), (E POL).injective.eq_iff]

theorem encSatisfies_iff (φ : Constraints n d) (τ : Fin n → Tree d) :
    EncSatisfies POL φ τ ↔ Satisfies (treeConstructor POL) φ (fun x => (E POL).symm (τ x)) := by
  rw [satisfies_iff_enc]
  simp only [OrderIso.apply_symm_apply]

theorem satisfiable_iff_enc (φ : Constraints n d) :
    Satisfiable (treeConstructor POL) φ ↔ ∃ τ : Fin n → Tree d, EncSatisfies POL φ τ := by
  constructor
  · rintro ⟨ρ, hρ⟩; exact ⟨_, (satisfies_iff_enc φ ρ).mp hρ⟩
  · rintro ⟨τ, hτ⟩; exact ⟨_, (encSatisfies_iff φ τ).mp hτ⟩

theorem entails_iff_enc (Q : Query n d) :
    Entails (treeConstructor POL) Q ↔
      ∀ τ : Fin n → Tree d, EncSatisfies POL Q.constraints τ → τ Q.left ≤ τ Q.right := by
  constructor
  · intro h τ hτ
    have := h _ ((encSatisfies_iff _ τ).mp hτ)
    rwa [← E_le_iff, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply] at this
  · intro h ρ hρ
    rw [← E_le_iff]
    exact h _ ((satisfies_iff_enc _ ρ).mp hρ)

theorem regularSatisfiable_iff_enc (φ : Constraints n d) :
    RegularSatisfiable POL φ ↔
      ∃ τ : Fin n → Tree d, (∀ x, Regular (τ x)) ∧ EncSatisfies POL φ τ := by
  constructor
  · rintro ⟨ρ, hr, hρ⟩
    exact ⟨_, fun x => (regular_E_iff (ρ x)).mpr (hr x), (satisfies_iff_enc φ ρ).mp hρ⟩
  · rintro ⟨τ, hr, hτ⟩
    exact ⟨_, fun x => (cregular_symm_iff (τ x)).mpr (hr x), (encSatisfies_iff φ τ).mp hτ⟩

theorem regularEntails_iff_enc (Q : Query n d) :
    RegularEntails POL Q ↔
      ∀ τ : Fin n → Tree d, (∀ x, Regular (τ x)) →
        EncSatisfies POL Q.constraints τ → τ Q.left ≤ τ Q.right := by
  constructor
  · intro h τ hr hτ
    have := h _ (fun x => (cregular_symm_iff (τ x)).mpr (hr x)) ((encSatisfies_iff _ τ).mp hτ)
    rwa [← E_le_iff, OrderIso.apply_symm_apply, OrderIso.apply_symm_apply] at this
  · intro h ρ hr hρ
    rw [← E_le_iff]
    exact h _ (fun x => (regular_E_iff (ρ x)).mpr (hr x)) ((satisfies_iff_enc _ ρ).mp hρ)

/-- Literal-wise transport for the two bound forms (useful for later stages). -/
theorem upper_iff_enc (x : CTree POL) (a : Fin d → CTree POL) :
    x ≤ CTree.node a ↔ E POL x ≤ node (fun i => dualIf (POL i) (E POL (a i))) := by
  rw [← E_le_iff, E_node]

theorem lower_iff_enc (x : CTree POL) (a : Fin d → CTree POL) :
    CTree.node a ≤ x ↔ node (fun i => dualIf (POL i) (E POL (a i))) ≤ E POL x := by
  rw [← E_le_iff, E_node]

/-! ## Sanity: the covariant special case -/

/-- With all positions covariant, the transported condition IS the covariant
satisfaction relation of `SubtypeConstraints` on the carrier. -/
theorem encSatisfies_covariant (hPOL : ∀ i, POL i = false) (φ : Constraints n d)
    (τ : Fin n → Tree d) :
    EncSatisfies POL φ τ ↔ SubtypeConstraints.Satisfies (AbsorbingSubtypeTrees.constructor d) φ τ := by
  have h : ∀ (c : Fin d → Fin n), (fun i => dualIf (POL i) (τ (c i))) = fun i => τ (c i) := by
    intro c; funext i; simp [hPOL i]
  unfold EncSatisfies SubtypeConstraints.Satisfies
  simp only [h]
  rfl

end NSSE.ContraConstraints
