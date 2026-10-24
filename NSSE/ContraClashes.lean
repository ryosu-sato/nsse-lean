import NSSE.ContraSupport

/-! # The polarity-aware label clashes C1–C3 (stage S2)

Notes v1361 §2, v1362 §2/§4. The clashes concern the roots only, so they are
literally the covariant C1–C3 read with the polarity-aware closure `≤s`:

* C1: `x = ⊤`, `y = ⊥`, `x ≤s y`;
* C2: `x = ⊤`, `v ≤ f(d̄)` original, `x ≤s v`;
* C3: `f(c̄) ≤ v` original, `y = ⊥`, `v ≤s y`.

A clash makes the system unsatisfiable over arbitrary contravariant trees, hence
over regular and over finite trees. The Boolean `clashBool` is computed from the
exact support table.
-/

namespace NSSE.ContraClashes

open SubtypeConstraints (Constraints Query BoundLiteral)
open ContraTrees ContraFiniteTrees ContraConstraints ContraSupport

variable {n d : Nat} {POL : Polarity d}

def C1 (POL : Polarity d) (φ : Constraints n d) : Prop :=
  ∃ x ∈ φ.top, ∃ y ∈ φ.bot, Support POL φ x y

def C2 (POL : Polarity d) (φ : Constraints n d) : Prop :=
  ∃ x ∈ φ.top, ∃ a ∈ φ.upper, Support POL φ x a.1

def C3 (POL : Polarity d) (φ : Constraints n d) : Prop :=
  ∃ a ∈ φ.lower, ∃ y ∈ φ.bot, Support POL φ a.1 y

def Clash (POL : Polarity d) (φ : Constraints n d) : Prop := C1 POL φ ∨ C2 POL φ ∨ C3 POL φ

def clashBool (POL : Polarity d) (φ : Constraints n d) : Bool :=
  let rel := table POL φ
  φ.top.any (fun x => φ.bot.any (fun y => rel x y)) ||
  φ.top.any (fun x => φ.upper.any (fun a => rel x a.1)) ||
  φ.lower.any (fun a => φ.bot.any (fun y => rel a.1 y))

theorem clashBool_correct (φ : Constraints n d) : clashBool POL φ = true ↔ Clash POL φ := by
  simp only [clashBool, Bool.or_eq_true, List.any_eq_true, table_correct, Clash, C1, C2, C3,
    or_assoc]

instance (φ : Constraints n d) : Decidable (Clash POL φ) :=
  decidable_of_iff _ (clashBool_correct φ)

/-- A clash is excluded by every solution over arbitrary contravariant trees. -/
theorem solution_no_clash (φ : Constraints n d) (ρ : Fin n → CTree POL)
    (hρ : Satisfies (treeConstructor POL) φ ρ) : ¬ Clash POL φ := by
  rintro (⟨x, hx, y, hy, hs⟩ | ⟨x, hx, a, ha, hs⟩ | ⟨a, ha, y, hy, hs⟩)
  · have he := support_sound (treeConstructor POL) φ ρ hρ hs
    rw [hρ.2.2.2 x hx, hρ.2.2.1 y hy] at he
    exact not_top_le_bot he
  · have he := (support_sound (treeConstructor POL) φ ρ hρ hs).trans (hρ.1 a ha)
    rw [hρ.2.2.2 x hx] at he
    exact not_top_le_node _ he
  · have he := (hρ.2.1 a ha).trans (support_sound (treeConstructor POL) φ ρ hρ hs)
    rw [hρ.2.2.1 y hy] at he
    exact not_node_le_bot _ he

/-- **Clash ⇒ unsatisfiable** (arbitrary trees). -/
theorem unsatisfiable_of_clash {φ : Constraints n d} (h : Clash POL φ) :
    ¬ Satisfiable (treeConstructor POL) φ := by
  rintro ⟨ρ, hρ⟩
  exact solution_no_clash φ ρ hρ h

theorem not_regularSatisfiable_of_clash {φ : Constraints n d} (h : Clash POL φ) :
    ¬ RegularSatisfiable POL φ :=
  fun hr => unsatisfiable_of_clash h (regularSatisfiable_imp φ hr)

theorem not_finiteSatisfiable_of_clash {φ : Constraints n d} (h : Clash POL φ) :
    ¬ Satisfiable (finiteConstructor POL) φ :=
  fun hf => not_regularSatisfiable_of_clash h (regularSatisfiable_of_finite hf)

theorem no_clash_of_satisfiable {φ : Constraints n d} (h : Satisfiable (treeConstructor POL) φ) :
    ¬ Clash POL φ :=
  fun hc => unsatisfiable_of_clash hc h

end NSSE.ContraClashes
