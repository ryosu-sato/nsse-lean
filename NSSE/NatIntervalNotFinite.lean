import NSSE.IntervalSideDelegation
import NSSE.FactorForestSubstitution
import NSSE.FiniteRegisteredStructuralTrace

/-!
# The concrete natural-interval type is not finitely enumerable

Several compiler interfaces currently accept `Enumeration NatInterval`.
That premise cannot be instantiated: the concrete interval type contains
the unit interval starting at every natural number.  Final finite compiler
states must therefore use a bounded interval type or a finite quotient of
interval geometry, not `NatInterval` itself.
-/

namespace NSSE

def NatInterval.unitAt (start : Nat) : NatInterval where
  start := start
  stop := start + 1
  nonempty := by omega

theorem Enumeration.not_natInterval
    (intervals : Enumeration NatInterval) : False := by
  let largestStart :=
    (intervals.values.map NatInterval.start).foldl max 0
  let fresh := NatInterval.unitAt (largestStart + 1)
  have hfresh : fresh ∈ intervals.values :=
    intervals.complete fresh
  have hstart :
      fresh.start ∈
        intervals.values.map NatInterval.start := by
    exact List.mem_map.mpr
      ⟨fresh, hfresh, rfl⟩
  have hle :=
    FactorTree.le_foldl_max_of_mem hstart 0
  change largestStart + 1 ≤ largestStart at hle
  omega

theorem not_nonempty_enumeration_natInterval :
    ¬ Nonempty (Enumeration NatInterval) := by
  rintro ⟨intervals⟩
  exact intervals.not_natInterval

def Enumeration.subtypeOfDecidable
    (elements : Enumeration α)
    (predicate : α → Prop)
    [DecidablePred predicate] :
    Enumeration {value : α // predicate value} where
  values :=
    elements.values.filterMap fun value =>
      if hvalue : predicate value then
        some ⟨value, hvalue⟩
      else
        none
  complete := by
    intro value
    simp only [List.mem_filterMap]
    refine ⟨value.1, elements.complete value.1, ?_⟩
    split
    · congr
    · rename_i hfalse
      exact False.elim (hfalse value.2)

abbrev BoundedNatInterval (limit : Nat) :=
  { endpoints : Fin (limit + 1) × Fin (limit + 1) //
      endpoints.1.1 < endpoints.2.1 }

def boundedNatIntervalEnumeration
    (limit : Nat) :
    Enumeration (BoundedNatInterval limit) :=
  ((finEnumeration (limit + 1)).product
    (finEnumeration (limit + 1))).subtypeOfDecidable
      (fun endpoints => endpoints.1.1 < endpoints.2.1)

def BoundedNatInterval.toNatInterval
    {limit : Nat} (interval : BoundedNatInterval limit) :
    NatInterval where
  start := interval.1.1.1
  stop := interval.1.2.1
  nonempty := interval.2

theorem BoundedNatInterval.stop_le
    {limit : Nat} (interval : BoundedNatInterval limit) :
    interval.toNatInterval.stop ≤ limit := by
  have hstop := interval.1.2.2
  change interval.1.2.1 ≤ limit
  omega

def BoundedNatInterval.ofNatInterval
    {limit : Nat} (interval : NatInterval)
    (hstop : interval.stop ≤ limit) :
    BoundedNatInterval limit :=
  ⟨(⟨interval.start, by
        have hnonempty := interval.nonempty
        omega⟩,
      ⟨interval.stop, by omega⟩),
    interval.nonempty⟩

@[simp] theorem BoundedNatInterval.toNatInterval_ofNatInterval
    {limit : Nat} (interval : NatInterval)
    (hstop : interval.stop ≤ limit) :
    (BoundedNatInterval.ofNatInterval interval hstop
      ).toNatInterval = interval := by
  cases interval
  rfl

theorem BoundedNatInterval.toNatInterval_injective
    {limit : Nat} :
    ∀ {left right : BoundedNatInterval limit},
      left.toNatInterval = right.toNatInterval →
        left = right := by
  intro left right heq
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg NatInterval.start heq
  · apply Fin.ext
    exact congrArg NatInterval.stop heq

end NSSE
