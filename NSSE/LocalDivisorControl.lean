import NSSE.FiniteControlSubmonoid

/-!
# Local-divisor control monoids

For `c : M`, the local divisor has carrier `cM ∩ Mc`, unit `c`, and product

`a ∘ b = a y` whenever `b = c y`.

The right quotient `y` is chosen classically.  Membership in `Mc` makes the
result independent enough for the monoid laws: if `a = x c`, then replacing
`c y` by an equal value preserves `a y = x (c y)`.
-/

namespace NSSE

universe u v

namespace ControlMonoid

def localDivisorCarrier
    (C : ControlMonoid M) (pivot value : M) : Prop :=
  (∃ after, value = C.mul pivot after) ∧
  ∃ before, value = C.mul before pivot

def HasTwoSidedInverse
    (C : ControlMonoid M) (value : M) : Prop :=
  (∃ right, C.mul value right = C.one) ∧
  ∃ left, C.mul left value = C.one

theorem localDivisorCarrier_one_iff
    (C : ControlMonoid M) (pivot : M) :
    C.localDivisorCarrier pivot C.one ↔
      C.HasTwoSidedInverse pivot := by
  simp only [localDivisorCarrier, HasTwoSidedInverse]
  constructor
  · rintro ⟨⟨right, hright⟩, left, hleft⟩
    exact ⟨⟨right, hright.symm⟩,
      left, hleft.symm⟩
  · rintro ⟨⟨right, hright⟩, left, hleft⟩
    exact ⟨⟨right, hright.symm⟩,
      left, hleft.symm⟩

theorem localDivisorCarrier_pivot
    (C : ControlMonoid M) (pivot : M) :
    C.localDivisorCarrier pivot pivot := by
  constructor
  · exact ⟨C.one, (C.mul_one pivot).symm⟩
  · exact ⟨C.one, (C.one_mul pivot).symm⟩

noncomputable def localAfter
    (C : ControlMonoid M) (pivot : M)
    (value : {value : M // C.localDivisorCarrier pivot value}) : M :=
  Classical.choose value.2.1

theorem localAfter_spec
    (C : ControlMonoid M) (pivot : M)
    (value : {value : M // C.localDivisorCarrier pivot value}) :
    value.1 = C.mul pivot (C.localAfter pivot value) :=
  Classical.choose_spec value.2.1

noncomputable def localBefore
    (C : ControlMonoid M) (pivot : M)
    (value : {value : M // C.localDivisorCarrier pivot value}) : M :=
  Classical.choose value.2.2

theorem localBefore_spec
    (C : ControlMonoid M) (pivot : M)
    (value : {value : M // C.localDivisorCarrier pivot value}) :
    value.1 = C.mul (C.localBefore pivot value) pivot :=
  Classical.choose_spec value.2.2

theorem localMul_mem
    (C : ControlMonoid M) (pivot : M)
    (left right :
      {value : M // C.localDivisorCarrier pivot value}) :
    C.localDivisorCarrier pivot
      (C.mul left.1 (C.localAfter pivot right)) := by
  let leftAfter := C.localAfter pivot left
  let leftBefore := C.localBefore pivot left
  let rightBefore := C.localBefore pivot right
  let rightAfter := C.localAfter pivot right
  have hleftAfter : left.1 = C.mul pivot leftAfter :=
    C.localAfter_spec pivot left
  have hleftBefore : left.1 = C.mul leftBefore pivot :=
    C.localBefore_spec pivot left
  have hrightAfter : right.1 = C.mul pivot rightAfter :=
    C.localAfter_spec pivot right
  have hrightBefore : right.1 = C.mul rightBefore pivot :=
    C.localBefore_spec pivot right
  constructor
  · refine ⟨C.mul leftAfter rightAfter, ?_⟩
    rw [hleftAfter, C.mul_assoc]
  · refine ⟨C.mul leftBefore rightBefore, ?_⟩
    calc
      C.mul left.1 rightAfter =
          C.mul leftBefore (C.mul pivot rightAfter) := by
            rw [hleftBefore, C.mul_assoc]
      _ = C.mul leftBefore right.1 := by
            rw [hrightAfter]
      _ = C.mul leftBefore (C.mul rightBefore pivot) := by
            rw [hrightBefore]
      _ = C.mul (C.mul leftBefore rightBefore) pivot := by
            rw [C.mul_assoc]

noncomputable def localMul
    (C : ControlMonoid M) (pivot : M)
    (left right :
      {value : M // C.localDivisorCarrier pivot value}) :
    {value : M // C.localDivisorCarrier pivot value} :=
  ⟨C.mul left.1 (C.localAfter pivot right),
    C.localMul_mem pivot left right⟩

noncomputable def localDivisor
    (C : ControlMonoid M) (pivot : M) :
    ControlMonoid
      {value : M // C.localDivisorCarrier pivot value} where
  one := ⟨pivot, C.localDivisorCarrier_pivot pivot⟩
  mul := C.localMul pivot
  one_mul := by
    intro value
    apply Subtype.ext
    exact (C.localAfter_spec pivot value).symm
  mul_one := by
    intro value
    apply Subtype.ext
    let pivotValue :
        {value : M // C.localDivisorCarrier pivot value} :=
      ⟨pivot, C.localDivisorCarrier_pivot pivot⟩
    let after := C.localAfter pivot pivotValue
    have hpivot : pivot = C.mul pivot after :=
      C.localAfter_spec pivot pivotValue
    have hbefore :
        value.1 =
          C.mul (C.localBefore pivot value) pivot :=
      C.localBefore_spec pivot value
    calc
      C.mul value.1 after =
          C.mul (C.mul (C.localBefore pivot value) pivot)
            after := by rw [hbefore]
      _ = C.mul (C.localBefore pivot value)
          (C.mul pivot after) := C.mul_assoc _ _ _
      _ = C.mul (C.localBefore pivot value) pivot := by
          rw [← hpivot]
      _ = value.1 := hbefore.symm
  mul_assoc := by
    intro first second third
    apply Subtype.ext
    let secondAfter := C.localAfter pivot second
    let thirdAfter := C.localAfter pivot third
    let combined :=
      C.localMul pivot second third
    let combinedAfter := C.localAfter pivot combined
    have hcombined :
        C.mul second.1 thirdAfter =
          C.mul pivot combinedAfter := by
      have hspec := C.localAfter_spec pivot combined
      dsimp [combined, localMul] at hspec
      change
        C.mul second.1 thirdAfter =
          C.mul pivot combinedAfter at hspec
      exact hspec
    have hfirstBefore :
        first.1 =
          C.mul (C.localBefore pivot first) pivot :=
      C.localBefore_spec pivot first
    dsimp only [localMul]
    change
      C.mul (C.mul first.1 secondAfter) thirdAfter =
        C.mul first.1 combinedAfter
    calc
      C.mul (C.mul first.1 secondAfter) thirdAfter =
          C.mul first.1 (C.mul secondAfter thirdAfter) :=
        C.mul_assoc _ _ _
      _ = C.mul (C.mul (C.localBefore pivot first) pivot)
          (C.mul secondAfter thirdAfter) := by
            rw [hfirstBefore]
      _ = C.mul (C.localBefore pivot first)
          (C.mul (C.mul pivot secondAfter) thirdAfter) := by
            simp only [C.mul_assoc]
      _ = C.mul (C.localBefore pivot first)
          (C.mul second.1 thirdAfter) := by
            rw [← C.localAfter_spec pivot second]
      _ = C.mul (C.localBefore pivot first)
          (C.mul pivot combinedAfter) := by
            rw [hcombined]
      _ = C.mul
          (C.mul (C.localBefore pivot first) pivot)
          combinedAfter := by
            rw [C.mul_assoc]
      _ = C.mul first.1 combinedAfter := by
            rw [hfirstBefore]

noncomputable def localDivisorEnumeration
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (pivot : M) :
    Enumeration
      {value : M // C.localDivisorCarrier pivot value} :=
  by
    letI : DecidablePred (C.localDivisorCarrier pivot) :=
      fun _ => Classical.propDecidable _
    exact elements.restrict (C.localDivisorCarrier pivot)

theorem localDivisor_normalized_length_lt_of_one_not_mem
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (pivot : M)
    (hone :
      ¬ C.localDivisorCarrier pivot C.one) :
    (C.localDivisorEnumeration elements pivot
      ).normalized.values.length <
      elements.normalized.values.length :=
  by
    letI : DecidablePred (C.localDivisorCarrier pivot) :=
      fun _ => Classical.propDecidable _
    exact Enumeration.normalized_restrict_length_lt_of_not
      elements (C.localDivisorCarrier pivot) C.one hone

theorem localDivisor_normalized_length_lt_of_not_twoSidedInverse
    [DecidableEq M]
    (C : ControlMonoid M) (elements : Enumeration M)
    (pivot : M)
    (hnonunit : ¬ C.HasTwoSidedInverse pivot) :
    (C.localDivisorEnumeration elements pivot
      ).normalized.values.length <
      elements.normalized.values.length := by
  apply C.localDivisor_normalized_length_lt_of_one_not_mem
    elements pivot
  rwa [C.localDivisorCarrier_one_iff]

theorem localMul_val_eq_of_after
    (C : ControlMonoid M) (pivot : M)
    (left right :
      {value : M // C.localDivisorCarrier pivot value})
    (after : M)
    (hright : right.1 = C.mul pivot after) :
    (C.localMul pivot left right).1 =
      C.mul left.1 after := by
  let chosen := C.localAfter pivot right
  have hchosen : right.1 = C.mul pivot chosen :=
    C.localAfter_spec pivot right
  have hleft :
      left.1 = C.mul (C.localBefore pivot left) pivot :=
    C.localBefore_spec pivot left
  change C.mul left.1 chosen = C.mul left.1 after
  calc
    C.mul left.1 chosen =
        C.mul (C.localBefore pivot left)
          (C.mul pivot chosen) := by
            rw [hleft, C.mul_assoc]
    _ = C.mul (C.localBefore pivot left) right.1 := by
          rw [← hchosen]
    _ = C.mul (C.localBefore pivot left)
          (C.mul pivot after) := by
          rw [hright]
    _ = C.mul left.1 after := by
          rw [hleft, C.mul_assoc]

theorem localIdempotent_mul_after
    (C : ControlMonoid M) (pivot : M)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hidempotent :
      (C.localDivisor pivot).Idempotent value) :
    C.mul value.1
        (C.localAfter pivot value) =
      value.1 := by
  have hvalue :=
    congrArg Subtype.val hidempotent
  change
    C.mul value.1
        (C.localAfter pivot value) =
      value.1 at hvalue
  exact hvalue

theorem localIdempotent_mul_rightQuotient
    (C : ControlMonoid M) (pivot : M)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (quotient : M)
    (hquotient :
      value.1 = C.mul pivot quotient) :
    C.mul value.1 quotient = value.1 := by
  have hlocal :=
    congrArg Subtype.val hidempotent
  change
    (C.localMul pivot value value).1 =
      value.1 at hlocal
  rw [C.localMul_val_eq_of_after
    pivot value value quotient hquotient] at hlocal
  exact hlocal

theorem localBefore_mul_localIdempotent
    (C : ControlMonoid M) (pivot : M)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hidempotent :
      (C.localDivisor pivot).Idempotent value) :
    C.mul (C.localBefore pivot value)
        value.1 =
      value.1 := by
  have hafter :=
    C.localIdempotent_mul_after
      pivot value hidempotent
  calc
    C.mul (C.localBefore pivot value)
        value.1 =
      C.mul (C.localBefore pivot value)
        (C.mul pivot
          (C.localAfter pivot value)) := by
            rw [← C.localAfter_spec pivot value]
    _ = C.mul
        (C.mul (C.localBefore pivot value)
          pivot)
        (C.localAfter pivot value) := by
          rw [C.mul_assoc]
    _ = C.mul value.1
        (C.localAfter pivot value) := by
          rw [← C.localBefore_spec pivot value]
    _ = value.1 := hafter

theorem leftQuotient_mul_localIdempotent
    (C : ControlMonoid M) (pivot : M)
    (value :
      {value : M //
        C.localDivisorCarrier pivot value})
    (hidempotent :
      (C.localDivisor pivot).Idempotent value)
    (quotient : M)
    (hquotient :
      value.1 = C.mul quotient pivot) :
    C.mul quotient value.1 = value.1 := by
  have hafter :=
    C.localIdempotent_mul_after
      pivot value hidempotent
  calc
    C.mul quotient value.1 =
      C.mul quotient
        (C.mul pivot
          (C.localAfter pivot value)) := by
            rw [← C.localAfter_spec pivot value]
    _ = C.mul
        (C.mul quotient pivot)
        (C.localAfter pivot value) := by
          rw [C.mul_assoc]
    _ = C.mul value.1
        (C.localAfter pivot value) := by
          rw [← hquotient]
    _ = value.1 := hafter

def localSandwich
    (C : ControlMonoid M) (pivot middle : M) :
    {value : M // C.localDivisorCarrier pivot value} :=
  ⟨C.mul (C.mul pivot middle) pivot, by
    constructor
    · exact ⟨C.mul middle pivot, by
        rw [C.mul_assoc]⟩
    · exact ⟨C.mul pivot middle, rfl⟩⟩

@[simp] theorem localSandwich_val
    (C : ControlMonoid M) (pivot middle : M) :
    (C.localSandwich pivot middle).1 =
      C.mul (C.mul pivot middle) pivot :=
  rfl

theorem eval_pivot_middle_pivot
    (C : ControlMonoid M) (pivot : M)
    (middle : Word M) :
    C.eval id ([pivot] ++ middle ++ [pivot]) =
      (C.localSandwich pivot (C.eval id middle)).1 := by
  simp only [C.eval_append, localSandwich_val,
    ControlMonoid.eval, List.map_id, List.map_cons,
    List.map_nil, ControlMonoid.product_cons,
    ControlMonoid.product_nil]
  rw [C.product_append ([pivot] ++ middle) [pivot],
    C.product_append [pivot] middle]
  simp only [ControlMonoid.product_cons,
    ControlMonoid.product_nil, C.mul_one]

theorem localMul_sandwich
    (C : ControlMonoid M) (pivot left right : M) :
    C.localMul pivot
        (C.localSandwich pivot left)
        (C.localSandwich pivot right) =
      C.localSandwich pivot
        (C.mul (C.mul left pivot) right) := by
  apply Subtype.ext
  rw [C.localMul_val_eq_of_after pivot
    (C.localSandwich pivot left)
    (C.localSandwich pivot right)
    (C.mul right pivot)]
  · simp only [localSandwich_val]
    simp only [C.mul_assoc]
  · simp only [localSandwich_val]
    rw [C.mul_assoc]

theorem localDivisor_mul_sandwich
    (C : ControlMonoid M) (pivot left right : M) :
    (C.localDivisor pivot).mul
        (C.localSandwich pivot left)
        (C.localSandwich pivot right) =
      C.localSandwich pivot
        (C.mul (C.mul left pivot) right) :=
  C.localMul_sandwich pivot left right

end ControlMonoid

end NSSE
