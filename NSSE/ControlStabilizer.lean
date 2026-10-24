import NSSE.FiniteControlSubmonoid

/-!
# Stabilizer control submonoids

Equal prefix controls force the intervening factor into a right
stabilizer.  Stabilizers are closed control submonoids, hence a proper
one is eligible for the finite-size induction.  If a right stabilizer is
not proper, its anchor absorbs every value on the right and is therefore
idempotent.  The left-handed statements are included symmetrically.
-/

namespace NSSE

universe u v

namespace ControlMonoid

def boolAndControlMonoid : ControlMonoid Bool where
  one := true
  mul := (· && ·)
  one_mul := by
    intro value
    cases value <;> decide
  mul_one := by
    intro value
    cases value <;> decide
  mul_assoc := by
    intro left middle right
    cases left <;> cases middle <;> cases right <;> decide

theorem boolAnd_false_right_absorbing :
    ∀ value : Bool,
      boolAndControlMonoid.mul false value = false := by
  intro value
  cases value <;> rfl

theorem boolAnd_false_idempotent :
    boolAndControlMonoid.Idempotent false :=
  rfl

theorem right_absorbing_idempotent_does_not_force_value_eq :
    boolAndControlMonoid.Idempotent false ∧
      (∀ value : Bool,
        boolAndControlMonoid.mul false value = false) ∧
      true ≠ false := by
  exact ⟨boolAnd_false_idempotent,
    boolAnd_false_right_absorbing, by decide⟩

def rightStabilizer (C : ControlMonoid M) (anchor : M) :
    ControlSubmonoid C where
  carrier value := C.mul anchor value = anchor
  one_mem := C.mul_one anchor
  mul_mem := by
    intro left right hleft hright
    rw [← C.mul_assoc, hleft, hright]

def leftStabilizer (C : ControlMonoid M) (anchor : M) :
    ControlSubmonoid C where
  carrier value := C.mul value anchor = anchor
  one_mem := C.one_mul anchor
  mul_mem := by
    intro left right hleft hright
    rw [C.mul_assoc, hright, hleft]

@[simp] theorem mem_rightStabilizer
    (C : ControlMonoid M) (anchor value : M) :
    (C.rightStabilizer anchor).carrier value ↔
      C.mul anchor value = anchor :=
  Iff.rfl

@[simp] theorem mem_leftStabilizer
    (C : ControlMonoid M) (anchor value : M) :
    (C.leftStabilizer anchor).carrier value ↔
      C.mul value anchor = anchor :=
  Iff.rfl

theorem rightStabilizer_proper_iff
    (C : ControlMonoid M) (anchor : M) :
    (C.rightStabilizer anchor).Proper ↔
      ∃ value : M, C.mul anchor value ≠ anchor :=
  Iff.rfl

theorem leftStabilizer_proper_iff
    (C : ControlMonoid M) (anchor : M) :
    (C.leftStabilizer anchor).Proper ↔
      ∃ value : M, C.mul value anchor ≠ anchor :=
  Iff.rfl

theorem right_absorbing_of_not_stabilizer_proper
    (C : ControlMonoid M) (anchor : M)
    (hnot : ¬ (C.rightStabilizer anchor).Proper) :
    ∀ value : M, C.mul anchor value = anchor := by
  exact (ControlSubmonoid.not_proper_iff
    (C.rightStabilizer anchor)).1 hnot

theorem left_absorbing_of_not_stabilizer_proper
    (C : ControlMonoid M) (anchor : M)
    (hnot : ¬ (C.leftStabilizer anchor).Proper) :
    ∀ value : M, C.mul value anchor = anchor := by
  exact (ControlSubmonoid.not_proper_iff
    (C.leftStabilizer anchor)).1 hnot

theorem eval_append_eq_of_right_absorbing
    (C : ControlMonoid M) (letter : α → M)
    (anchor : M)
    (habsorbing : ∀ value : M, C.mul anchor value = anchor)
    (before after : Word α)
    (hbefore : C.eval letter before = anchor) :
    C.eval letter (before ++ after) = anchor := by
  rw [C.eval_append, hbefore]
  exact habsorbing (C.eval letter after)

theorem eval_context_eq_of_twoSidedAbsorbing
    (C : ControlMonoid M) (letter : α → M)
    (zero : M)
    (hright :
      ∀ value : M, C.mul zero value = zero)
    (hleft :
      ∀ value : M, C.mul value zero = zero)
    (before middle after : Word α)
    (hmiddle : C.eval letter middle = zero) :
    C.eval letter (before ++ middle ++ after) =
      zero := by
  simp only [C.eval_append]
  rw [hmiddle, hleft, hright]

theorem eval_take_eq_of_right_absorbing
    (C : ControlMonoid M) (letter : α → M)
    (anchor : M)
    (habsorbing : ∀ value : M, C.mul anchor value = anchor)
    (word : Word α) {cut later : Nat}
    (hcut : cut ≤ later)
    (hcontrol : C.eval letter (word.take cut) = anchor) :
    C.eval letter (word.take later) = anchor := by
  have htake :
      word.take later =
        word.take cut ++
          (word.drop cut).take (later - cut) := by
    have hlater : later = cut + (later - cut) := by omega
    calc
      word.take later =
          word.take (cut + (later - cut)) :=
        congrArg (fun index => word.take index) hlater
      _ = word.take cut ++
          (word.drop cut).take (later - cut) :=
        List.take_add
  rw [htake]
  exact C.eval_append_eq_of_right_absorbing
    letter anchor habsorbing _ _ hcontrol

theorem idempotent_of_not_rightStabilizer_proper
    (C : ControlMonoid M) (anchor : M)
    (hnot : ¬ (C.rightStabilizer anchor).Proper) :
    C.Idempotent anchor :=
  C.right_absorbing_of_not_stabilizer_proper anchor hnot anchor

theorem idempotent_of_not_leftStabilizer_proper
    (C : ControlMonoid M) (anchor : M)
    (hnot : ¬ (C.leftStabilizer anchor).Proper) :
    C.Idempotent anchor :=
  C.left_absorbing_of_not_stabilizer_proper anchor hnot anchor

instance instDecidablePredRightStabilizer
    [DecidableEq M] (C : ControlMonoid M) (anchor : M) :
    DecidablePred (C.rightStabilizer anchor).carrier :=
  fun value => inferInstanceAs
    (Decidable (C.mul anchor value = anchor))

instance instDecidablePredLeftStabilizer
    [DecidableEq M] (C : ControlMonoid M) (anchor : M) :
    DecidablePred (C.leftStabilizer anchor).carrier :=
  fun value => inferInstanceAs
    (Decidable (C.mul value anchor = anchor))

theorem rightStabilizer_normalized_length_lt
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (anchor : M)
    (hproper : (C.rightStabilizer anchor).Proper) :
    ((C.rightStabilizer anchor).enumeration elements
      ).normalized.values.length <
      elements.normalized.values.length := by
  exact
    (C.rightStabilizer anchor
      ).normalized_enumeration_length_lt_of_proper
        elements hproper

theorem leftStabilizer_normalized_length_lt
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (anchor : M)
    (hproper : (C.leftStabilizer anchor).Proper) :
    ((C.leftStabilizer anchor).enumeration elements
      ).normalized.values.length <
      elements.normalized.values.length := by
  exact
    (C.leftStabilizer anchor
      ).normalized_enumeration_length_lt_of_proper
        elements hproper

theorem eval_mem_rightStabilizer_of_prefix_eq
    (C : ControlMonoid M) (letter : α → M)
    (anchor : M) (before middle : Word α)
    (hbefore : C.eval letter before = anchor)
    (hextended : C.eval letter (before ++ middle) = anchor) :
    (C.rightStabilizer anchor).carrier
      (C.eval letter middle) := by
  rw [C.eval_append, hbefore] at hextended
  exact hextended

theorem eval_mem_leftStabilizer_of_suffix_eq
    (C : ControlMonoid M) (letter : α → M)
    (anchor : M) (middle suffix : Word α)
    (hsuffix : C.eval letter suffix = anchor)
    (hextended : C.eval letter (middle ++ suffix) = anchor) :
    (C.leftStabilizer anchor).carrier
      (C.eval letter middle) := by
  rw [C.eval_append, hsuffix] at hextended
  exact hextended

def liftLetterToRightStabilizer
    (C : ControlMonoid M) (anchor : M)
    (letter : α → M)
    (hletter : ∀ symbol, (C.rightStabilizer anchor).carrier
      (letter symbol)) :
    α → {value : M //
      (C.rightStabilizer anchor).carrier value} :=
  fun symbol => ⟨letter symbol, hletter symbol⟩

def liftLetterToLeftStabilizer
    (C : ControlMonoid M) (anchor : M)
    (letter : α → M)
    (hletter : ∀ symbol, (C.leftStabilizer anchor).carrier
      (letter symbol)) :
    α → {value : M //
      (C.leftStabilizer anchor).carrier value} :=
  fun symbol => ⟨letter symbol, hletter symbol⟩

end ControlMonoid

end NSSE
