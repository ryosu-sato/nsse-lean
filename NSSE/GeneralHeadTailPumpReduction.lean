import NSSE.GeneralFirstEmptyPumpReduction

/-!
# Retaining a nonempty leading pump during arbitrary-arity reduction

This is the second induction step for empty-pump normalization.  The first
pump is retained, while an arbitrary nonempty-pump reduction of the tail is
recombined with it.  The reduced tail's initial word is absorbed into the
separator following the retained pump.
-/

namespace NSSE

namespace LinearWordFamily

def tailFamily
    (family : LinearWordFamily α (arity + 1)) :
    LinearWordFamily α arity where
  initial := []
  pump := fun index => family.pump index.succ
  separator := fun index => family.separator index.succ

def tailParameters
    (parameters : Fin (arity + 1) → Nat) :
    Fin arity → Nat :=
  fun index => parameters index.succ

theorem word_eq_head_append_tail
    (family : LinearWordFamily α (arity + 1))
    (parameters : Fin (arity + 1) → Nat) :
    family.word parameters =
      family.initial ++
        Word.power (family.pump 0) (parameters 0) ++
        family.separator 0 ++
        family.tailFamily.word (tailParameters parameters) := by
  simp [word, tailFamily, tailParameters,
    List.finRange_succ_eq_map, List.flatMap_map,
    List.append_assoc, Function.comp_def]

def prependHeadToReductionFamily
    (family : LinearWordFamily α (arity + 1))
    (tailReduction :
      NonemptyPumpReduction family.tailFamily) :
    LinearWordFamily α (tailReduction.reducedArity + 1) where
  initial := family.initial
  pump :=
    Fin.cases (family.pump 0)
      tailReduction.reducedFamily.pump
  separator :=
    Fin.cases
      (family.separator 0 ++
        tailReduction.reducedFamily.initial)
      tailReduction.reducedFamily.separator

def prependHeadProject
    (family : LinearWordFamily α (arity + 1))
    (tailReduction :
      NonemptyPumpReduction family.tailFamily)
    (parameters : Fin (arity + 1) → Nat) :
    Fin (tailReduction.reducedArity + 1) → Nat :=
  Fin.cases (parameters 0)
    (tailReduction.project (tailParameters parameters))

def prependHeadLift
    (family : LinearWordFamily α (arity + 1))
    (tailReduction :
      NonemptyPumpReduction family.tailFamily)
    (parameters :
      Fin (tailReduction.reducedArity + 1) → Nat) :
    Fin (arity + 1) → Nat :=
  Fin.cases (parameters 0)
    (tailReduction.lift (fun index => parameters index.succ))

@[simp] theorem tailParameters_prependHeadLift
    (family : LinearWordFamily α (arity + 1))
    (tailReduction :
      NonemptyPumpReduction family.tailFamily)
    (parameters :
      Fin (tailReduction.reducedArity + 1) → Nat) :
    tailParameters
        (family.prependHeadLift tailReduction parameters) =
      tailReduction.lift
        (fun index => parameters index.succ) := by
  funext index
  simp [tailParameters, prependHeadLift]

@[simp] theorem prependHeadProject_lift
    (family : LinearWordFamily α (arity + 1))
    (tailReduction :
      NonemptyPumpReduction family.tailFamily)
    (parameters :
      Fin (tailReduction.reducedArity + 1) → Nat) :
    family.prependHeadProject tailReduction
        (family.prependHeadLift tailReduction parameters) =
      parameters := by
  funext index
  refine Fin.cases ?_ (fun tailIndex => ?_) index
  · simp [prependHeadProject, prependHeadLift]
  · simp [prependHeadProject, tailReduction.project_lift]

theorem word_prependHeadToReductionFamily
    (family : LinearWordFamily α (arity + 1))
    (tailReduction :
      NonemptyPumpReduction family.tailFamily)
    (parameters : Fin (arity + 1) → Nat) :
    (family.prependHeadToReductionFamily tailReduction).word
        (family.prependHeadProject tailReduction parameters) =
      family.word parameters := by
  rw [family.word_eq_head_append_tail parameters,
    ← tailReduction.word_project
      (tailParameters parameters)]
  simp [prependHeadToReductionFamily, prependHeadProject,
    word, List.finRange_succ_eq_map, List.flatMap_map,
    List.append_assoc, Function.comp_def]

theorem prependHeadToReductionFamily_pumpsNonempty
    (family : LinearWordFamily α (arity + 1))
    (hhead : family.pump 0 ≠ [])
    (tailReduction :
      NonemptyPumpReduction family.tailFamily) :
    (family.prependHeadToReductionFamily
      tailReduction).PumpsNonempty := by
  intro index
  refine Fin.cases ?_ (fun tailIndex => ?_) index
  · simpa [prependHeadToReductionFamily] using hhead
  · simpa [prependHeadToReductionFamily] using
      tailReduction.pumpsNonempty tailIndex

def retainHeadReduction
    (family : LinearWordFamily α (arity + 1))
    (hhead : family.pump 0 ≠ [])
    (tailReduction :
      NonemptyPumpReduction family.tailFamily) :
    NonemptyPumpReduction family where
  reducedArity := tailReduction.reducedArity + 1
  reducedFamily :=
    family.prependHeadToReductionFamily tailReduction
  project := family.prependHeadProject tailReduction
  lift := family.prependHeadLift tailReduction
  word_project :=
    family.word_prependHeadToReductionFamily tailReduction
  project_lift :=
    family.prependHeadProject_lift tailReduction
  pumpsNonempty :=
    family.prependHeadToReductionFamily_pumpsNonempty
      hhead tailReduction

end LinearWordFamily

end NSSE
