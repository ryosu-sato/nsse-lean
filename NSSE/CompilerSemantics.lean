import NSSE.TaggedCompiler

/-!
# Semantic extraction and realization for finite compiler rules

This is the well-founded semantic kernel of v417.  Local extraction may
emit a terminal or one finite rule whose recursive witnesses are all
strictly smaller.  Strong induction turns those local decompositions
into finite derivations.  Conversely, terminal soundness and rule
soundness realize every finite derivation.
-/

namespace NSSE

universe u v

structure CompilerRule (State : Type u) where
  parent : State
  children : List State

inductive ListRel (R : α → β → Prop) : List α → List β → Prop
  | nil : ListRel R [] []
  | cons {x y xs ys} :
      R x y → ListRel R xs ys → ListRel R (x :: xs) (y :: ys)

theorem listRel_map_pairs
    (pairs : List (α × β))
    (h : ∀ pair ∈ pairs, R pair.1 pair.2) :
    ListRel R (pairs.map Prod.fst) (pairs.map Prod.snd) := by
  induction pairs with
  | nil => exact .nil
  | cons pair pairs ih =>
      exact .cons (h pair (by simp))
        (ih (fun p hp => h p (by simp [hp])))

/--
A rule derivation stores a finite list of paired child
state/witnesses.  Recursive derivations are addressed by membership,
avoiding any dependence on a chosen order of proof construction.
-/
inductive CompilerDerives
    {State : Type u} {Witness : Type v}
    (Terminal : State → Witness → Prop)
    (Compose : CompilerRule State → List Witness → Witness → Prop) :
    State → Witness → Prop where
  | terminal {state witness} :
      Terminal state witness →
      CompilerDerives Terminal Compose state witness
  | rule {rule : CompilerRule State}
      {children : List (State × Witness)} {witness : Witness} :
      children.map Prod.fst = rule.children →
      (∀ child ∈ children,
        CompilerDerives Terminal Compose child.1 child.2) →
      Compose rule (children.map Prod.snd) witness →
      CompilerDerives Terminal Compose rule.parent witness

namespace CompilerDerives

theorem sound
    {Semantic : State → Witness → Prop}
    {Terminal : State → Witness → Prop}
    {Compose : CompilerRule State → List Witness → Witness → Prop}
    (hterminal :
      ∀ {state witness}, Terminal state witness →
        Semantic state witness)
    (hrule :
      ∀ {rule : CompilerRule State} {witnesses witness},
        ListRel Semantic rule.children witnesses →
        Compose rule witnesses witness →
        Semantic rule.parent witness)
    {state witness}
    (hderive : CompilerDerives Terminal Compose state witness) :
    Semantic state witness := by
  induction hderive with
  | terminal h => exact hterminal h
  | @rule rule children witness hstates hchildren hcompose ih =>
      apply hrule _ hcompose
      rw [← hstates]
      exact listRel_map_pairs children
        (fun child hmem => ih child hmem)

end CompilerDerives

structure LocalCompilerSemantics
    (State : Type u) (Witness : Type v) where
  Semantic : State → Witness → Prop
  Terminal : State → Witness → Prop
  Compose : CompilerRule State → List Witness → Witness → Prop
  size : Witness → Nat
  terminal_sound :
    ∀ {state witness}, Terminal state witness →
      Semantic state witness
  rule_sound :
    ∀ {rule : CompilerRule State} {witnesses witness},
      ListRel Semantic rule.children witnesses →
      Compose rule witnesses witness →
      Semantic rule.parent witness
  extract :
    ∀ {state witness}, Semantic state witness →
      Terminal state witness ∨
      ∃ (rule : CompilerRule State)
          (children : List (State × Witness)),
        rule.parent = state ∧
        children.map Prod.fst = rule.children ∧
        (∀ child ∈ children, Semantic child.1 child.2) ∧
        (∀ child ∈ children, size child.2 < size witness) ∧
        Compose rule (children.map Prod.snd) witness

namespace LocalCompilerSemantics

/--
Global extraction: every concrete semantic witness admits a finite
tagged derivation.  No coinductive cycle is accepted; every recursive
premise decreases `size`.
-/
theorem extract_derivation
    (C : LocalCompilerSemantics State Witness)
    {state : State} {witness : Witness}
    (hsemantic : C.Semantic state witness) :
    CompilerDerives C.Terminal C.Compose state witness := by
  have main :
      ∀ n, ∀ (state : State) (witness : Witness),
        C.size witness = n →
        C.Semantic state witness →
        CompilerDerives C.Terminal C.Compose state witness := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro state witness hsize hsemantic
        rcases C.extract hsemantic with hterminal | hstep
        · exact .terminal hterminal
        · obtain ⟨rule, children, hparent, hstates, hchildren,
              hstrict, hcompose⟩ := hstep
          subst state
          apply CompilerDerives.rule hstates
          · intro child hmem
            exact ih (C.size child.2)
              (by simpa [hsize] using hstrict child hmem)
              child.1 child.2 rfl (hchildren child hmem)
          · exact hcompose
  exact main (C.size witness) state witness rfl hsemantic

/-- Global realization of every extracted finite derivation. -/
theorem realize_derivation
    (C : LocalCompilerSemantics State Witness)
    {state : State} {witness : Witness}
    (hderive : CompilerDerives C.Terminal C.Compose state witness) :
    C.Semantic state witness :=
  hderive.sound C.terminal_sound C.rule_sound

theorem semantic_iff_derives
    (C : LocalCompilerSemantics State Witness)
    (state : State) (witness : Witness) :
    C.Semantic state witness ↔
      CompilerDerives C.Terminal C.Compose state witness :=
  ⟨C.extract_derivation, C.realize_derivation⟩

end LocalCompilerSemantics

end NSSE
