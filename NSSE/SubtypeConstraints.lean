import NSSE.ForwardTableAutomaton

/-! # Original flat subtype constraints and syntactic support

The four lists encode conjunctions of the four literal forms of the
one-constructor signature. Support is exactly journal Table 1, including
decomposition against the ORIGINAL lower and upper literals.
-/

namespace NSSE.SubtypeConstraints

abbrev Children (n d : Nat) := Fin d → Fin n
abbrev BoundLiteral (n d : Nat) := Fin n × Children n d

structure Constraints (n d : Nat) where
  upper : List (BoundLiteral n d)
  lower : List (BoundLiteral n d)
  bot : List (Fin n)
  top : List (Fin n)

structure Query (n d : Nat) where
  constraints : Constraints n d
  left : Fin n
  right : Fin n

variable {n d : Nat}

inductive Support (φ : Constraints n d) : Fin n → Fin n → Prop
  | refl (x : Fin n) : Support φ x x
  | trans {x y z : Fin n} : Support φ x y → Support φ y z → Support φ x z
  | decomp {a b : BoundLiteral n d} (ha : a ∈ φ.lower) (hb : b ∈ φ.upper)
      (h : Support φ a.1 b.1) (i : Fin d) : Support φ (a.2 i) (b.2 i)

def SupportedUpper (φ : Constraints n d) (x : Fin n) (i : Fin d) (z : Fin n) : Prop :=
  ∃ a ∈ φ.upper, Support φ x a.1 ∧ Support φ (a.2 i) z

def SupportedLower (φ : Constraints n d) (x : Fin n) (i : Fin d) (z : Fin n) : Prop :=
  ∃ a ∈ φ.lower, Support φ z (a.2 i) ∧ Support φ a.1 x

def SupportedBot (φ : Constraints n d) (x : Fin n) : Prop := ∃ y ∈ φ.bot, Support φ x y
def SupportedTop (φ : Constraints n d) (x : Fin n) : Prop := ∃ y ∈ φ.top, Support φ y x

section Semantics

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

/-- The algebraic property of the single covariant constructor used in
support soundness. Concrete tree models are supplied in separate modules. -/
structure Constructor (T : Type*) [PartialOrder T] (d : Nat) where
  node : (Fin d → T) → T
  le_iff : ∀ a b, node a ≤ node b ↔ ∀ i, a i ≤ b i

def Satisfies (F : Constructor T d) (φ : Constraints n d) (ρ : Fin n → T) : Prop :=
  (∀ a ∈ φ.upper, ρ a.1 ≤ F.node (fun i => ρ (a.2 i))) ∧
  (∀ a ∈ φ.lower, F.node (fun i => ρ (a.2 i)) ≤ ρ a.1) ∧
  (∀ x ∈ φ.bot, ρ x = ⊥) ∧ (∀ x ∈ φ.top, ρ x = ⊤)

def Satisfiable (F : Constructor T d) (φ : Constraints n d) : Prop := ∃ ρ, Satisfies F φ ρ

def Entails (F : Constructor T d) (Q : Query n d) : Prop :=
  ∀ ρ, Satisfies F Q.constraints ρ → ρ Q.left ≤ ρ Q.right

theorem support_sound (F : Constructor T d) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x y : Fin n} (h : Support φ x y) : ρ x ≤ ρ y := by
  induction h with
  | refl x => exact le_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @decomp a b ha hb _ i ih =>
      exact (F.le_iff _ _).mp ((hρ.2.1 a ha).trans (ih.trans (hρ.1 b hb))) i

/-- Journal Lemma 3, with the other constructor children explicitly chosen
from the witnessing literal rather than existentially hidden in a guard. -/
theorem supportedUpper_sound (F : Constructor T d) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x z : Fin n} {i : Fin d} (h : SupportedUpper φ x i z) :
    ∃ children : Fin d → T, children i = ρ z ∧ ρ x ≤ F.node children := by
  obtain ⟨a, ha, hx, hz⟩ := h
  let children : Fin d → T := fun j => if j = i then ρ z else ρ (a.2 j)
  refine ⟨children, by simp [children], ?_⟩
  apply (support_sound F φ ρ hρ hx).trans ((hρ.1 a ha).trans ?_)
  apply (F.le_iff _ _).mpr
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [children, ↓reduceIte] using support_sound F φ ρ hρ hz
  · simp [children, hj]

theorem supportedLower_sound (F : Constructor T d) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x z : Fin n} {i : Fin d} (h : SupportedLower φ x i z) :
    ∃ children : Fin d → T, children i = ρ z ∧ F.node children ≤ ρ x := by
  obtain ⟨a, ha, hz, hx⟩ := h
  let children : Fin d → T := fun j => if j = i then ρ z else ρ (a.2 j)
  refine ⟨children, by simp [children], ?_⟩
  apply le_trans ?_ ((hρ.2.1 a ha).trans (support_sound F φ ρ hρ hx))
  apply (F.le_iff _ _).mpr
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [children, ↓reduceIte] using support_sound F φ ρ hρ hz
  · simp [children, hj]

theorem supportedBot_sound (F : Constructor T d) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x : Fin n} (h : SupportedBot φ x) : ρ x = ⊥ := by
  obtain ⟨y, hy, hs⟩ := h
  apply le_antisymm ?_ bot_le
  simpa only [hρ.2.2.1 y hy] using support_sound F φ ρ hρ hs

theorem supportedTop_sound (F : Constructor T d) (φ : Constraints n d) (ρ : Fin n → T)
    (hρ : Satisfies F φ ρ) {x : Fin n} (h : SupportedTop φ x) : ρ x = ⊤ := by
  obtain ⟨y, hy, hs⟩ := h
  apply le_antisymm le_top
  simpa only [hρ.2.2.2 y hy] using support_sound F φ ρ hρ hs

theorem entails_of_unsatisfiable (F : Constructor T d) (Q : Query n d)
    (h : ¬ Satisfiable F Q.constraints) : Entails F Q :=
  fun ρ hρ => False.elim (h ⟨ρ, hρ⟩)

end Semantics

end NSSE.SubtypeConstraints
