import NSSE.LinearFamilyReductionPresburger

/-!
# Removing a leading empty pump at arbitrary arity

This is the uniform induction step for empty-pump normalization.  A family
of arity `n+1` whose first pump is empty reduces to arity `n` by appending
the first separator to the initial fixed word and shifting every remaining
coordinate down by one.
-/

namespace NSSE

namespace LinearWordFamily

def eraseFirstPump
    (family : LinearWordFamily α (arity + 1)) :
    LinearWordFamily α arity where
  initial := family.initial ++ family.separator 0
  pump := fun index => family.pump index.succ
  separator := fun index => family.separator index.succ

def eraseFirstPumpParameters
    (parameters : Fin (arity + 1) → Nat) :
    Fin arity → Nat :=
  fun index => parameters index.succ

def liftAfterErasingFirstPumpParameters
    (parameters : Fin arity → Nat) :
    Fin (arity + 1) → Nat :=
  Fin.cases 0 parameters

@[simp] theorem eraseFirstPump_lift_parameters
    (parameters : Fin arity → Nat) :
    eraseFirstPumpParameters
      (liftAfterErasingFirstPumpParameters parameters) =
        parameters := by
  funext index
  simp [eraseFirstPumpParameters,
    liftAfterErasingFirstPumpParameters]

theorem word_eraseFirstPump_eq
    (family : LinearWordFamily α (arity + 1))
    (hempty : family.pump 0 = [])
    (parameters : Fin (arity + 1) → Nat) :
    family.eraseFirstPump.word
        (eraseFirstPumpParameters parameters) =
      family.word parameters := by
  simp [eraseFirstPump, eraseFirstPumpParameters,
    word, List.finRange_succ_eq_map, hempty,
    List.append_assoc, Function.comp_def,
    List.flatMap_map]

def TailPumpsNonempty
    (family : LinearWordFamily α (arity + 1)) : Prop :=
  ∀ index : Fin arity, family.pump index.succ ≠ []

theorem eraseFirstPump_pumpsNonempty
    (family : LinearWordFamily α (arity + 1))
    (htail : family.TailPumpsNonempty) :
    family.eraseFirstPump.PumpsNonempty := by
  intro index
  exact htail index

def eraseFirstPumpReduction
    (family : LinearWordFamily α (arity + 1))
    (hempty : family.pump 0 = [])
    (htail : family.TailPumpsNonempty) :
    NonemptyPumpReduction family where
  reducedArity := arity
  reducedFamily := family.eraseFirstPump
  project := eraseFirstPumpParameters
  lift := liftAfterErasingFirstPumpParameters
  word_project := family.word_eraseFirstPump_eq hempty
  project_lift := eraseFirstPump_lift_parameters
  pumpsNonempty := family.eraseFirstPump_pumpsNonempty htail

def liftEraseFirstPumpReduction
    (family : LinearWordFamily α (arity + 1))
    (hempty : family.pump 0 = [])
    (tailReduction :
      NonemptyPumpReduction family.eraseFirstPump) :
    NonemptyPumpReduction family where
  reducedArity := tailReduction.reducedArity
  reducedFamily := tailReduction.reducedFamily
  project := fun parameters =>
    tailReduction.project
      (eraseFirstPumpParameters parameters)
  lift := fun parameters =>
    liftAfterErasingFirstPumpParameters
      (tailReduction.lift parameters)
  word_project := by
    intro parameters
    rw [tailReduction.word_project,
      family.word_eraseFirstPump_eq hempty parameters]
  project_lift := by
    intro parameters
    rw [eraseFirstPump_lift_parameters,
      tailReduction.project_lift]
  pumpsNonempty := tailReduction.pumpsNonempty

end LinearWordFamily

end NSSE
