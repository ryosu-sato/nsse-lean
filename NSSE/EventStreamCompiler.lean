import NSSE.GuardedCompiler
import NSSE.CompilerSemantics

/-!
# Well-founded compiler skeleton for restoration streams

This module packages the exact structural recursion used by the guarded
compiler.  A problem stores the current word, selected cuts, and the
remaining restoration events.  Processing the head updates the cuts
according to the executable three-way placement classifier and leaves a
strictly shorter tail problem.
-/

namespace NSSE

universe u

structure RestorationProblem (α : Type u) where
  events : List (InsertionEvent α)
  word : Word α
  source : Nat
  target : Nat

def advanceSource (event : InsertionEvent α) (j t : Nat) : Nat :=
  match classifyCutPlacement event.slot j t with
  | .beforeSource => j + event.payload.length
  | .betweenCuts => j
  | .afterTarget => j

def advanceTarget (event : InsertionEvent α) (j t : Nat) : Nat :=
  match classifyCutPlacement event.slot j t with
  | .beforeSource => t + event.payload.length
  | .betweenCuts => t + event.payload.length
  | .afterTarget => t

def restorationTail
    (event : InsertionEvent α) (events : List (InsertionEvent α))
    (w : Word α) (j t : Nat) : RestorationProblem α where
  events := events
  word := event.apply w
  source := advanceSource event j t
  target := advanceTarget event j t

theorem advanceSource_lt_advanceTarget
    (event : InsertionEvent α) (j t : Nat) (hjt : j < t) :
    advanceSource event j t < advanceTarget event j t := by
  generalize hplacement :
    classifyCutPlacement event.slot j t = placement
  cases placement <;>
    simp [advanceSource, advanceTarget, hplacement] <;> omega

theorem advanceTarget_lt_apply_length
    (event : InsertionEvent α) (w : Word α) (j t : Nat)
    (hslot : event.slot ≤ w.length) (ht : t < w.length) :
    advanceTarget event j t < (event.apply w).length := by
  have hlength :
      (event.apply w).length = w.length + event.payload.length := by
    exact Word.insertAt_length w event.payload hslot
  generalize hplacement :
    classifyCutPlacement event.slot j t = placement
  cases placement <;>
    simp [advanceTarget, hplacement] <;>
    rw [hlength] <;> omega

inductive ValidRestorationStream :
    List (InsertionEvent α) → Word α → Prop where
  | nil (w : Word α) :
      ValidRestorationStream [] w
  | cons
      (event : InsertionEvent α) (events : List (InsertionEvent α))
      (w : Word α)
      (slot_le_length : event.slot ≤ w.length)
      (tail : ValidRestorationStream events (event.apply w)) :
      ValidRestorationStream (event :: events) w

inductive RestorationWellFormed : RestorationProblem α → Prop where
  | nil (w : Word α) (j t : Nat)
      (source_lt_target : j < t)
      (target_lt_length : t < w.length) :
      RestorationWellFormed ⟨[], w, j, t⟩
  | cons
      (event : InsertionEvent α) (events : List (InsertionEvent α))
      (w : Word α) (j t : Nat)
      (slot_le_length : event.slot ≤ w.length)
      (source_lt_target : j < t)
      (target_lt_length : t < w.length)
      (tail :
        RestorationWellFormed
          (restorationTail event events w j t)) :
      RestorationWellFormed ⟨event :: events, w, j, t⟩

theorem restorationWellFormed_of_validStream
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hvalid : ValidRestorationStream events w)
    (hjt : j < t) (ht : t < w.length) :
    RestorationWellFormed ⟨events, w, j, t⟩ := by
  induction hvalid generalizing j t with
  | nil w =>
      exact .nil w j t hjt ht
  | cons event events w hslot tail ih =>
      exact .cons event events w j t hslot hjt ht
        (ih
          (advanceSource event j t)
          (advanceTarget event j t)
          (advanceSource_lt_advanceTarget event j t hjt)
          (advanceTarget_lt_apply_length event w j t hslot ht))

def restorationRule : CompilerRule Unit where
  parent := ()
  children := [()]

def RestorationTerminal (_state : Unit)
    (problem : RestorationProblem α) : Prop :=
  problem.events = [] ∧ RestorationWellFormed problem

inductive RestorationCompose :
    CompilerRule Unit → List (RestorationProblem α) →
      RestorationProblem α → Prop where
  | step
      (event : InsertionEvent α) (events : List (InsertionEvent α))
      (w : Word α) (j t : Nat)
      (slot_le_length : event.slot ≤ w.length)
      (source_lt_target : j < t)
      (target_lt_length : t < w.length) :
      RestorationCompose restorationRule
        [restorationTail event events w j t]
        ⟨event :: events, w, j, t⟩

def restorationCompiler :
    LocalCompilerSemantics Unit (RestorationProblem α) where
  Semantic := fun _ problem => RestorationWellFormed problem
  Terminal := RestorationTerminal
  Compose := RestorationCompose
  size := fun problem => problem.events.length
  terminal_sound := by
    intro state problem hterminal
    exact hterminal.2
  rule_sound := by
    intro rule witnesses problem hchildren hcompose
    cases hcompose with
    | step event events w j t hslot hjt ht =>
        cases hchildren with
        | cons htail hrest =>
            cases hrest
            exact .cons event events w j t hslot hjt ht htail
  extract := by
    intro state problem hsemantic
    cases hsemantic with
    | nil w j t hjt ht =>
        exact Or.inl ⟨rfl, .nil w j t hjt ht⟩
    | cons event events w j t hslot hjt ht htail =>
        apply Or.inr
        refine ⟨restorationRule,
          [((), restorationTail event events w j t)],
          rfl, rfl, ?_, ?_, ?_⟩
        · intro child hmem
          simp only [List.mem_cons, List.mem_singleton] at hmem
          rcases hmem with rfl | hfalse
          · exact htail
          · contradiction
        · intro child hmem
          simp only [List.mem_cons, List.mem_singleton] at hmem
          rcases hmem with rfl | hfalse
          · simp [restorationTail]
          · contradiction
        · exact .step event events w j t hslot hjt ht

theorem restoration_derives
    (problem : RestorationProblem α)
    (hwellFormed : RestorationWellFormed problem) :
    CompilerDerives RestorationTerminal RestorationCompose () problem :=
  restorationCompiler.extract_derivation hwellFormed

theorem validStream_derives
    (events : List (InsertionEvent α)) (w : Word α) (j t : Nat)
    (hvalid : ValidRestorationStream events w)
    (hjt : j < t) (ht : t < w.length) :
    CompilerDerives RestorationTerminal RestorationCompose ()
      ⟨events, w, j, t⟩ :=
  restoration_derives ⟨events, w, j, t⟩
    (restorationWellFormed_of_validStream
      events w j t hvalid hjt ht)

theorem restoration_derives_iff_wellFormed
    (problem : RestorationProblem α) :
    CompilerDerives RestorationTerminal RestorationCompose () problem ↔
      RestorationWellFormed problem := by
  constructor
  · exact restorationCompiler.realize_derivation
  · exact restorationCompiler.extract_derivation

end NSSE
