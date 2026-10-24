import NSSE

/-!
# Finite tagged-compiler syntax

Constructive finite syntax from v417--v419.  The six tag classes and four
terminal strata are disjoint inductive constructors.  Guarded atoms and
forbidden query sets are represented by fixed-length Boolean masks, so
the generalized state space can be enumerated without assuming a
nonconstructive finite-set library.
-/

namespace NSSE

universe u

structure Enumeration (α : Type u) where
  values : List α
  complete : ∀ x, x ∈ values

namespace Enumeration

/-- Image enumeration when every target comes with a chosen preimage. -/
def mapOnto (E : Enumeration α) (f : α → β)
    (preimage : β → α) (rightInv : ∀ y, f (preimage y) = y) :
    Enumeration β where
  values := E.values.map f
  complete := by
    intro y
    simp only [List.mem_map]
    exact ⟨preimage y, E.complete (preimage y), rightInv y⟩

def product (Eα : Enumeration α) (Eβ : Enumeration β) :
    Enumeration (α × β) where
  values := Eα.values.flatMap
    (fun x => Eβ.values.map (fun y => (x, y)))
  complete := by
    intro pair
    rcases pair with ⟨x, y⟩
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨x, Eα.complete x, y, Eβ.complete y, rfl⟩

def sum (Eα : Enumeration α) (Eβ : Enumeration β) :
    Enumeration (Sum α β) where
  values := Eα.values.map Sum.inl ++ Eβ.values.map Sum.inr
  complete := by
    intro value
    cases value with
    | inl x =>
        apply List.mem_append_left
        simp only [List.mem_map]
        exact ⟨x, Eα.complete x, rfl⟩
    | inr y =>
        apply List.mem_append_right
        simp only [List.mem_map]
        exact ⟨y, Eβ.complete y, rfl⟩

end Enumeration

def boolVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (boolVectors n).map (false :: ·) ++
      (boolVectors n).map (true :: ·)

theorem mem_boolVectors_of_length :
    ∀ {n : Nat} (bits : List Bool),
      bits.length = n → bits ∈ boolVectors n
  | 0, [], _ => by simp [boolVectors]
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | n + 1, bit :: bits, h => by
      have htail : bits.length = n := by simp at h; exact h
      cases bit with
      | false =>
          apply List.mem_append_left
          simp only [List.mem_map]
          exact ⟨bits, mem_boolVectors_of_length bits htail, rfl⟩
      | true =>
          apply List.mem_append_right
          simp only [List.mem_map]
          exact ⟨bits, mem_boolVectors_of_length bits htail, rfl⟩

inductive CompilerTag
    (Ctl Cut Ori LCA Macro Wire Atom QClass : Type u) where
  | nonstrong : Ctl → Cut → LCA → Macro → Wire →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass
  | strong : Ctl → Cut → Macro → Wire → QClass →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass
  | hub : Ctl → Cut → Macro → Wire →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass
  | copy : Ctl → Cut → Ori → Macro → Wire →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass
  | side : Ctl → Cut → LCA →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass
  | bounded : Ctl → Cut → Atom →
      CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass
deriving DecidableEq

namespace CompilerTag

def enumerate
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass) :
    List (CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass) :=
  (ctl.values.flatMap fun c =>
    cut.values.flatMap fun k =>
      lca.values.flatMap fun l =>
        macros.values.flatMap fun m =>
          wire.values.map fun w => .nonstrong c k l m w) ++
  (ctl.values.flatMap fun c =>
    cut.values.flatMap fun k =>
      macros.values.flatMap fun m =>
        wire.values.flatMap fun w =>
          quotient.values.map fun q => .strong c k m w q) ++
  (ctl.values.flatMap fun c =>
    cut.values.flatMap fun k =>
      macros.values.flatMap fun m =>
        wire.values.map fun w => .hub c k m w) ++
  (ctl.values.flatMap fun c =>
    cut.values.flatMap fun k =>
      ori.values.flatMap fun o =>
        macros.values.flatMap fun m =>
          wire.values.map fun w => .copy c k o m w) ++
  (ctl.values.flatMap fun c =>
    cut.values.flatMap fun k =>
      lca.values.map fun l => .side c k l) ++
  (ctl.values.flatMap fun c =>
    cut.values.flatMap fun k =>
      atom.values.map fun a => .bounded c k a)

theorem mem_enumerate
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass)
    (tag : CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass) :
    tag ∈ enumerate ctl cut ori lca macros wire atom quotient := by
  cases tag <;>
    simp [enumerate, ctl.complete, cut.complete, ori.complete,
      lca.complete, macros.complete, wire.complete, atom.complete,
      quotient.complete]

def enumeration
    (ctl : Enumeration Ctl) (cut : Enumeration Cut)
    (ori : Enumeration Ori) (lca : Enumeration LCA)
    (macros : Enumeration Macro) (wire : Enumeration Wire)
    (atom : Enumeration Atom) (quotient : Enumeration QClass) :
    Enumeration (CompilerTag Ctl Cut Ori LCA Macro Wire Atom QClass) where
  values := enumerate ctl cut ori lca macros wire atom quotient
  complete := mem_enumerate ctl cut ori lca macros wire atom quotient

end CompilerTag

structure GeneralizedState (Tag : Type u) where
  tag : Tag
  guarded : List Bool
  forbidden : List Bool

def GeneralizedState.Valid
    (atomCount queryCount : Nat) (state : GeneralizedState Tag) : Prop :=
  state.guarded.length = atomCount ∧
  state.forbidden.length = queryCount

def enumerateStates (tags : List Tag) (atomCount queryCount : Nat) :
    List (GeneralizedState Tag) :=
  tags.flatMap fun tag =>
    (boolVectors atomCount).flatMap fun guarded =>
      (boolVectors queryCount).map fun forbidden =>
        ⟨tag, guarded, forbidden⟩

theorem mem_enumerateStates
    (tagEnum : Enumeration Tag)
    (atomCount queryCount : Nat)
    (state : GeneralizedState Tag)
    (hvalid : state.Valid atomCount queryCount) :
    state ∈ enumerateStates tagEnum.values atomCount queryCount := by
  rcases state with ⟨tag, guarded, forbidden⟩
  simp only [GeneralizedState.Valid] at hvalid
  simp only [enumerateStates, List.mem_flatMap, List.mem_map]
  exact ⟨tag, tagEnum.complete tag, guarded,
    mem_boolVectors_of_length guarded hvalid.1,
    forbidden, mem_boolVectors_of_length forbidden hvalid.2, rfl⟩

/--
The v418 terminal separation is enforced by constructors: a PWE carries
only word-equation data, PEL only length/whole-block data, VBRP only
named-token/Parikh data, and periodic terminals only fixed-base data.
-/
inductive CompilerTerminal
    (PWE PEL VBRP FixedPeriodic : Type u) where
  | pwe : PWE → CompilerTerminal PWE PEL VBRP FixedPeriodic
  | pel : PEL → CompilerTerminal PWE PEL VBRP FixedPeriodic
  | vbrp : VBRP → CompilerTerminal PWE PEL VBRP FixedPeriodic
  | fixedPeriodic : FixedPeriodic →
      CompilerTerminal PWE PEL VBRP FixedPeriodic

namespace CompilerTerminal

def enumerate
    (pwe : Enumeration PWE) (pel : Enumeration PEL)
    (vbrp : Enumeration VBRP) (periodic : Enumeration FixedPeriodic) :
    List (CompilerTerminal PWE PEL VBRP FixedPeriodic) :=
  pwe.values.map .pwe ++
  pel.values.map .pel ++
  vbrp.values.map .vbrp ++
  periodic.values.map .fixedPeriodic

theorem mem_enumerate
    (pwe : Enumeration PWE) (pel : Enumeration PEL)
    (vbrp : Enumeration VBRP) (periodic : Enumeration FixedPeriodic)
    (terminal : CompilerTerminal PWE PEL VBRP FixedPeriodic) :
    terminal ∈ enumerate pwe pel vbrp periodic := by
  cases terminal <;>
    simp [enumerate, pwe.complete, pel.complete, vbrp.complete,
      periodic.complete]

def enumeration
    (pwe : Enumeration PWE) (pel : Enumeration PEL)
    (vbrp : Enumeration VBRP) (periodic : Enumeration FixedPeriodic) :
    Enumeration (CompilerTerminal PWE PEL VBRP FixedPeriodic) where
  values := enumerate pwe pel vbrp periodic
  complete := mem_enumerate pwe pel vbrp periodic

def CompilerTerminal.fold
    (onPWE : PWE → R) (onPEL : PEL → R)
    (onVBRP : VBRP → R) (onPeriodic : FixedPeriodic → R) :
    CompilerTerminal PWE PEL VBRP FixedPeriodic → R
  | .pwe x => onPWE x
  | .pel x => onPEL x
  | .vbrp x => onVBRP x
  | .fixedPeriodic x => onPeriodic x

end CompilerTerminal

/--
An executable solver together with its exact semantic specification.
For the four terminal classes these are respectively the PWE, PEL,
VBRP, and fixed-base periodic procedures.
-/
structure ExactSolver (Input : Type u) where
  formula : Input → Prop
  decide : Input → Bool
  correct : ∀ input, decide input ↔ formula input

def terminalFormula
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP) (periodic : ExactSolver FixedPeriodic) :
    CompilerTerminal PWE PEL VBRP FixedPeriodic → Prop
  | .pwe input => pwe.formula input
  | .pel input => pel.formula input
  | .vbrp input => vbrp.formula input
  | .fixedPeriodic input => periodic.formula input

def decideTerminal
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP) (periodic : ExactSolver FixedPeriodic) :
    CompilerTerminal PWE PEL VBRP FixedPeriodic → Bool
  | .pwe input => pwe.decide input
  | .pel input => pel.decide input
  | .vbrp input => vbrp.decide input
  | .fixedPeriodic input => periodic.decide input

theorem decideTerminal_correct
    (pwe : ExactSolver PWE) (pel : ExactSolver PEL)
    (vbrp : ExactSolver VBRP) (periodic : ExactSolver FixedPeriodic)
    (terminal : CompilerTerminal PWE PEL VBRP FixedPeriodic) :
    decideTerminal pwe pel vbrp periodic terminal ↔
      terminalFormula pwe pel vbrp periodic terminal := by
  cases terminal with
  | pwe input => exact pwe.correct input
  | pel input => exact pel.correct input
  | vbrp input => exact vbrp.correct input
  | fixedPeriodic input => exact periodic.correct input

structure ExactEqTest (α : Type u) where
  eqb : α → α → Bool
  correct : ∀ x y, eqb x y ↔ x = y

def allZero : List Int → Bool
  | [] => true
  | displacement :: rest =>
      decide (displacement = 0) && allZero rest

theorem allZero_correct (displacements : List Int) :
    allZero displacements ↔ ∀ x ∈ displacements, x = 0 := by
  induction displacements with
  | nil => simp [allZero]
  | cons displacement rest ih =>
      simp [allZero, ih]

/--
Post-compression loop data.  `sourceWire` and `targetWire` are already
alpha-normalized finite signed wirings; numeric information is only the
finite counter-displacement vector.
-/
structure LoopSummary (Wire : Type u) where
  sourceWire : Wire
  targetWire : Wire
  displacement : List Int
deriving DecidableEq

def isIdentityLoop (wireEq : ExactEqTest Wire)
    (loop : LoopSummary Wire) : Bool :=
  wireEq.eqb loop.sourceWire loop.targetWire &&
    allZero loop.displacement

def IdentityLoop (loop : LoopSummary Wire) : Prop :=
  loop.sourceWire = loop.targetWire ∧
    ∀ x ∈ loop.displacement, x = 0

theorem isIdentityLoop_correct
    (wireEq : ExactEqTest Wire) (loop : LoopSummary Wire) :
    isIdentityLoop wireEq loop ↔ IdentityLoop loop := by
  simp [isIdentityLoop, IdentityLoop, wireEq.correct, allZero_correct]

/--
Finite transition enumeration.  `enabled` is the executable local
compiler test (including its finite control and symbolic-label class).
-/
def enumerateTransitions (states : List State)
    (enabled : State → State → Bool) : List (State × State) :=
  states.flatMap fun source =>
    (states.filter (enabled source)).map fun target => (source, target)

theorem mem_enumerateTransitions
    (states : List State) (enabled : State → State → Bool)
    (source target : State) :
    (source, target) ∈ enumerateTransitions states enabled ↔
      source ∈ states ∧ target ∈ states ∧ enabled source target := by
  simp [enumerateTransitions]

end NSSE
