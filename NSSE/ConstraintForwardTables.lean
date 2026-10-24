import NSSE.FiniteSubtypeSupport

/-! # The original constraint query computes every forward-automaton table

No support table is supplied by the caller. The exact closure is computed
once and the journal's child-bound and escape rules are finite list queries.
-/

namespace NSSE.ConstraintForwardTables

open SubtypeConstraints FiniteSubtypeSupport

variable {n d : Nat}

def tables (Q : Query n d) : ForwardTableAutomaton.Tables n d :=
  let rel := table Q.constraints
  { queryLeft := Q.left
    queryRight := Q.right
    le := rel
    upper := fun x i z => Q.constraints.upper.any (fun a => rel x a.1 && rel (a.2 i) z)
    lower := fun x i z => Q.constraints.lower.any (fun a => rel z (a.2 i) && rel a.1 x)
    bot := fun x => Q.constraints.bot.any (fun y => rel x y)
    top := fun x => Q.constraints.top.any (fun y => rel y x) }

theorem le_correct (Q : Query n d) (x y : Fin n) :
    (tables Q).le x y = true ↔ Support Q.constraints x y := table_correct Q.constraints x y

theorem upper_correct (Q : Query n d) (x : Fin n) (i : Fin d) (z : Fin n) :
    (tables Q).upper x i z = true ↔ SupportedUpper Q.constraints x i z := by
  simp [tables, List.any_eq_true, table_correct, SupportedUpper]

theorem lower_correct (Q : Query n d) (x : Fin n) (i : Fin d) (z : Fin n) :
    (tables Q).lower x i z = true ↔ SupportedLower Q.constraints x i z := by
  simp [tables, List.any_eq_true, table_correct, SupportedLower]

theorem bot_correct (Q : Query n d) (x : Fin n) :
    (tables Q).bot x = true ↔ SupportedBot Q.constraints x := by
  simp [tables, List.any_eq_true, table_correct, SupportedBot]

theorem top_correct (Q : Query n d) (x : Fin n) :
    (tables Q).top x = true ↔ SupportedTop Q.constraints x := by
  simp [tables, List.any_eq_true, table_correct, SupportedTop]

def automaton (Q : Query n d) (side : ForwardTableAutomaton.Side) :
    ForwardCapAutomaton.Input (Fin d) := ForwardTableAutomaton.compile (tables Q) side

theorem automaton_gap (Q : Query n d) (side : ForwardTableAutomaton.Side) :
    ForwardCapAutomaton.GapUniversal (automaton Q side) := ForwardTableAutomaton.compile_gap (tables Q) side

theorem automaton_strict (Q : Query n d) (side : ForwardTableAutomaton.Side) :
    ForwardCapAutomaton.StrictCap (automaton Q side) := ForwardTableAutomaton.compile_strict (tables Q) side

/-- The actual two-side Boolean FROM CONSTRAINT SYNTAX. Its theorem below
certifies the automaton meanings; entailment still requires the forward
semantic equivalence and the tree-kind-specific satisfiability branch. -/
def decideBothSides (Q : Query n d) : Bool :=
  let D := tables Q
  ForwardTableAutomaton.decideUniversal D .left && ForwardTableAutomaton.decideUniversal D .right

theorem decideBothSides_correct (Q : Query n d) : decideBothSides Q = true ↔
    ForwardCapAutomaton.Universal (automaton Q .left) ∧
    ForwardCapAutomaton.Universal (automaton Q .right) := by
  simp only [decideBothSides, Bool.and_eq_true, ForwardTableAutomaton.decideUniversal_correct]
  rfl

section Soundness

variable {T : Type*} [PartialOrder T] [OrderBot T] [OrderTop T]

theorem computed_le_sound (F : Constructor T d) (Q : Query n d) (ρ : Fin n → T)
    (hρ : Satisfies F Q.constraints ρ) {x y : Fin n} (h : (tables Q).le x y = true) : ρ x ≤ ρ y :=
  support_sound F Q.constraints ρ hρ ((le_correct Q x y).mp h)

theorem computed_upper_sound (F : Constructor T d) (Q : Query n d) (ρ : Fin n → T)
    (hρ : Satisfies F Q.constraints ρ) {x z : Fin n} {i : Fin d}
    (h : (tables Q).upper x i z = true) :
    ∃ children : Fin d → T, children i = ρ z ∧ ρ x ≤ F.node children :=
  supportedUpper_sound F Q.constraints ρ hρ ((upper_correct Q x i z).mp h)

theorem computed_lower_sound (F : Constructor T d) (Q : Query n d) (ρ : Fin n → T)
    (hρ : Satisfies F Q.constraints ρ) {x z : Fin n} {i : Fin d}
    (h : (tables Q).lower x i z = true) :
    ∃ children : Fin d → T, children i = ρ z ∧ F.node children ≤ ρ x :=
  supportedLower_sound F Q.constraints ρ hρ ((lower_correct Q x i z).mp h)

theorem computed_bot_sound (F : Constructor T d) (Q : Query n d) (ρ : Fin n → T)
    (hρ : Satisfies F Q.constraints ρ) {x : Fin n} (h : (tables Q).bot x = true) : ρ x = ⊥ :=
  supportedBot_sound F Q.constraints ρ hρ ((bot_correct Q x).mp h)

theorem computed_top_sound (F : Constructor T d) (Q : Query n d) (ρ : Fin n → T)
    (hρ : Satisfies F Q.constraints ρ) {x : Fin n} (h : (tables Q).top x = true) : ρ x = ⊤ :=
  supportedTop_sound F Q.constraints ρ hρ ((top_correct Q x).mp h)

end Soundness

end NSSE.ConstraintForwardTables
