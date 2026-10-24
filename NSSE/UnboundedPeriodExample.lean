import NSSE.Cap

/-!
# The unbounded-period example from Theorem 3.1

This file isolates the concrete word calculation behind the example.  The
alphabet has letters `one` and `two`; the residue suffix is
`one^a two one^3`.
-/

namespace NSSE

inductive TwoLetter where
  | one
  | two
  deriving DecidableEq, Repr

namespace UnboundedPeriodExample

open TwoLetter

def ones (n : Nat) : Word TwoLetter :=
  List.replicate n one

def residueSuffix (a : Nat) : Word TwoLetter :=
  ones a ++ [two] ++ ones 3

def exampleWord (a : Nat) : Word TwoLetter :=
  [two] ++ residueSuffix a

/-- The right language `1*2` used by the single cap component. -/
def oneStarTwo : Language TwoLetter := fun w =>
  ∃ n, w = ones n ++ [two]

def singletonTwo : Language TwoLetter := fun w =>
  w = [two]

def exampleComponent : CapComponent TwoLetter where
  left := singletonTwo
  right := oneStarTwo

theorem residueSuffix_length (a : Nat) :
    (residueSuffix a).length = a + 4 := by
  simp [residueSuffix, ones]

/--
The suffix `1^a 2 111` has period `a+1` once the initial block has length
at least three.  This is the explicit witness used in Theorem 3.1.
-/
theorem residueSuffix_hasPeriod (a : Nat) (ha : 3 ≤ a) :
    Word.HasPeriod (residueSuffix a) (a + 1) := by
  unfold Word.HasPeriod Word.factor
  constructor
  · rw [residueSuffix_length]
    omega
  · have hsub : a + 4 - (a + 1) = 3 := by omega
    rw [residueSuffix_length, hsub]
    have hdrop :
        (residueSuffix a).drop (a + 1) = ones 3 := by
      rw [show residueSuffix a =
        (ones a ++ [two]) ++ ones 3 by simp [residueSuffix]]
      simp [ones, List.drop_append_eq_append_drop,
        show a - (a + 1) = 0 by omega,
        show a + 1 - a = 1 by omega]
    rw [hdrop]
    simp [residueSuffix, ones, List.take_append_eq_append_take,
      show min 3 a = 3 by omega, show 3 - a = 0 by omega]

/-- The period prefix is exactly the `1*2` word `1^a 2`. -/
theorem residueSuffix_periodPrefix_mem (a : Nat) :
    oneStarTwo ((residueSuffix a).take (a + 1)) := by
  refine ⟨a, ?_⟩
  rw [show residueSuffix a =
    (ones a ++ [two]) ++ ones 3 by simp [residueSuffix]]
  simp [ones, List.take_append_eq_append_take,
    show a + 1 - a = 1 by omega]

/--
No other proper prefix of the residue suffix belongs to `1*2`.  The unique
`two` occurs at zero-based position `a`, so an accepted prefix must stop
immediately after it.
-/
theorem periodPrefix_unique
    (a p : Nat) (hp : p < (residueSuffix a).length)
    (hmem : oneStarTwo ((residueSuffix a).take p)) :
    p = a + 1 := by
  rcases hmem with ⟨n, hword⟩
  have hplen : ((residueSuffix a).take p).length = p := by
    simp [Nat.min_eq_left (Nat.le_of_lt hp)]
  have hn : p = n + 1 := by
    have := congrArg List.length hword
    simpa [hplen, ones] using this
  by_cases hpa : p ≤ a
  · have htake :
        (residueSuffix a).take p = ones p := by
      simp [residueSuffix, ones, List.take_append_eq_append_take,
        Nat.sub_eq_zero_of_le hpa, Nat.min_eq_left hpa]
    have htwo :
        two ∈ ones n ++ [two] := by simp
    rw [← hword, htake] at htwo
    simp [ones] at htwo
  · have hap : a + 1 ≤ p := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hap
    by_cases hk : k = 0
    · omega
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hlast := congrArg List.getLast? hword
      have hklt : k < 3 := by
        rw [residueSuffix_length] at hp
        omega
      have hkCases : k = 1 ∨ k = 2 := by omega
      rcases hkCases with rfl | rfl
      · have htake :
            (residueSuffix a).take (a + 1 + 1) =
              ones a ++ [two, one] := by
          simp [residueSuffix, ones, List.take_append_eq_append_take,
            show a + 1 + 1 - a = 2 by omega,
            show min (a + 1 + 1) a = a by omega]
        rw [htake] at hlast
        simp [ones] at hlast
      · have htake :
            (residueSuffix a).take (a + 1 + 2) =
              ones a ++ [two, one, one] := by
          simp [residueSuffix, ones, List.take_append_eq_append_take,
            show a + 1 + 2 - a = 3 by omega,
            show min (a + 1 + 2) a = a by omega]
        rw [htake] at hlast
        simp [ones] at hlast

/--
The last three letters copy the first three letters at the unique anchor.
Together with the length equation, this is the concrete periodic witness.
-/
theorem exampleWord_witnessCopy (a : Nat) (ha : 3 ≤ a) :
    Word.WitnessCopy (exampleWord a) 1 (a + 1) 3 := by
  have hlen : 1 + (a + 1) + 3 = (exampleWord a).length := by
    simp [exampleWord, residueSuffix_length]
    omega
  apply (Word.witnessCopy_iff_anchoredPeriod
    (exampleWord a) 1 (a + 1) 3 hlen (by omega)).2
  simpa [Word.AnchoredPeriod, exampleWord] using
    residueSuffix_hasPeriod a ha

theorem exampleWord_length (a : Nat) :
    (exampleWord a).length = a + 5 := by
  simp [exampleWord, residueSuffix_length]

/-- The concrete words are covered through the periodic-witness branch. -/
theorem exampleWord_periodicWitness (a : Nat) (ha : 3 ≤ a) :
    PeriodicWitness exampleComponent (exampleWord a) := by
  refine ⟨1, a + 1, 3, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · rw [exampleWord_length]
    omega
  · simp [exampleComponent, singletonTwo, exampleWord]
  · simpa [exampleComponent, Word.factor, exampleWord] using
      residueSuffix_periodPrefix_mem a
  · exact exampleWord_witnessCopy a ha

theorem exampleWord_capCovered (a : Nat) (ha : 3 ≤ a) :
    capComponentCovers exampleComponent (exampleWord a) :=
  periodicWitness_capComponentCovers _ _
    (exampleWord_periodicWitness a ha)

/--
Every periodic witness on the distinguished residue word has period exactly
`a+1`.  This is the uniqueness assertion used by the unboundedness part of
Theorem 3.1.
-/
theorem exampleWord_witnessPeriod_unique
    (a j p e : Nat)
    (hp : 0 < p) (he : 0 < e)
    (hlen : j + p + e = (exampleWord a).length)
    (hleft : exampleComponent.left ((exampleWord a).take j))
    (hright : exampleComponent.right
      (Word.factor (exampleWord a) j p)) :
    p = a + 1 := by
  have hwordlen := exampleWord_length a
  have hjle : j ≤ (exampleWord a).length := by omega
  have hjlen : ((exampleWord a).take j).length = j := by
    simp [Nat.min_eq_left hjle]
  have hj : j = 1 := by
    have h := congrArg List.length hleft
    simpa [exampleComponent, singletonTwo, hjlen] using h
  subst j
  have hpProper : p < (residueSuffix a).length := by
    rw [residueSuffix_length]
    rw [hwordlen] at hlen
    omega
  apply periodPrefix_unique a p hpProper
  simpa [exampleComponent, Word.factor, exampleWord] using hright

/-- A version of `PeriodicWitness` exposing the period as a parameter. -/
def HasWitnessPeriod (a p : Nat) : Prop :=
  ∃ j e,
    0 < p ∧ 0 < e ∧
    j + p + e = (exampleWord a).length ∧
    exampleComponent.left ((exampleWord a).take j) ∧
    exampleComponent.right (Word.factor (exampleWord a) j p) ∧
    Word.WitnessCopy (exampleWord a) j p e

theorem hasWitnessPeriod_iff (a p : Nat) (ha : 3 ≤ a) :
    HasWitnessPeriod a p ↔ p = a + 1 := by
  constructor
  · rintro ⟨j, e, hp, he, hlen, hleft, hright, -⟩
    exact exampleWord_witnessPeriod_unique
      a j p e hp he hlen hleft hright
  · rintro rfl
    exact ⟨1, 3, by omega, by omega, by
      rw [exampleWord_length]
      omega, by
      simp [exampleComponent, singletonTwo, exampleWord], by
      simpa [exampleComponent, Word.factor, exampleWord] using
        residueSuffix_periodPrefix_mem a,
      exampleWord_witnessCopy a ha⟩

/--
There are admissible witness periods above every proposed finite bound.
Thus the periods required by this family cannot be uniformly bounded.
-/
theorem witnessPeriods_unbounded (B : Nat) :
    ∃ a j p e,
      3 ≤ a ∧ B < p ∧
      0 < p ∧ 0 < e ∧
      j + p + e = (exampleWord a).length ∧
      exampleComponent.left ((exampleWord a).take j) ∧
      exampleComponent.right (Word.factor (exampleWord a) j p) ∧
      Word.WitnessCopy (exampleWord a) j p e := by
  refine ⟨B + 3, 1, B + 4, 3, by omega, by omega,
    by omega, by omega, ?_, ?_, ?_, ?_⟩
  · rw [exampleWord_length]
    omega
  · simp [exampleComponent, singletonTwo, exampleWord]
  · simpa [exampleComponent, Word.factor, exampleWord] using
      residueSuffix_periodPrefix_mem (B + 3)
  · simpa using exampleWord_witnessCopy (B + 3) (by omega)

/-- The single component satisfies the required shuffle side condition. -/
theorem exampleComponent_shuffle :
    ShuffleCondition exampleComponent := by
  intro pi hleft hconcat
  rcases hconcat with ⟨x, y, hxy, hx, hy⟩
  have hpi : pi = [two] := hleft
  have hx' : x = [two] := hx
  rcases hy with ⟨n, hy⟩
  subst pi
  subst x
  subst y
  have hlen := congrArg List.length hxy
  simp [ones] at hlen

/-! ## The universal restricted expression -/

def distinguishedWords : Language TwoLetter := fun w =>
  ∃ a, 3 ≤ a ∧ w = exampleWord a

/-- The prefix-closed residue language `G*` from Theorem 3.1. -/
def gStar : Language TwoLetter :=
  Language.prefixClosure distinguishedWords

/-- Its complement is the extension-closed route language. -/
def complementRoute : Language TwoLetter := fun w =>
  ¬ gStar w

def exampleExpression : CapExpression TwoLetter where
  caps := [exampleComponent]
  routes := [complementRoute]

theorem gStar_capComponentCovers
    (w : Word TwoLetter) (hw : gStar w) :
    capComponentCovers exampleComponent w := by
  rcases hw with ⟨tail, a, ha, heq⟩
  rcases exampleWord_capCovered a ha with ⟨outer, hcovered⟩
  refine ⟨tail ++ outer, ?_⟩
  rw [← List.append_assoc, heq]
  exact hcovered

/--
The complement of a prefix-closed language is extension-closed.  This
justifies using `complementRoute` as the route generator `M` in `M·A*`.
-/
theorem complementRoute_append
    (x tail : Word TwoLetter) (hx : complementRoute x) :
    complementRoute (x ++ tail) := by
  intro hxt
  apply hx
  rcases hxt with ⟨outer, hdist⟩
  exact ⟨tail ++ outer, by
    simpa [List.append_assoc] using hdist⟩

theorem exampleExpression_restricted :
    exampleExpression.IsRestricted := by
  intro c hc
  simp [exampleExpression] at hc
  subst c
  exact exampleComponent_shuffle

/-- The expression constructed in Theorem 3.1 is universal. -/
theorem exampleExpression_universal :
    exampleExpression.Universal := by
  intro w
  by_cases hw : gStar w
  · apply Or.inl
    exact ⟨exampleComponent, by simp [exampleExpression],
      gStar_capComponentCovers w hw⟩
  · apply Or.inr
    refine ⟨complementRoute, by simp [exampleExpression],
      w, [], by simp, ?_, trivial⟩
    exact hw

/-- Every distinguished word lies in the residue `G*`. -/
theorem exampleWord_mem_gStar (a : Nat) (ha : 3 ≤ a) :
    gStar (exampleWord a) :=
  ⟨[], a, ha, by simp⟩

/--
No route covers a distinguished residue word.  Any route prefix outside
`G*` would contradict prefix closure after appending the remaining suffix.
-/
theorem exampleWord_routeFree (a : Nat) (ha : 3 ≤ a) :
    routeFree exampleExpression (exampleWord a) := by
  intro hroute
  rcases hroute with ⟨R, hR, x, y, hxy, hx, -⟩
  simp [exampleExpression] at hR
  subst R
  apply hx
  refine ⟨y, ?_⟩
  refine ⟨a, ha, ?_⟩
  exact hxy.symm

/--
Semantic form of Theorem 3.1: the constructed expression is restricted and
universal, but for every proposed bound there is a route-free covered word
whose (unique) periodic-witness period exceeds that bound.
-/
theorem universal_with_unbounded_witnessPeriods :
    exampleExpression.IsRestricted ∧
    exampleExpression.Universal ∧
    ∀ B, ∃ a,
      3 ≤ a ∧
      routeFree exampleExpression (exampleWord a) ∧
      B < a + 1 ∧
      HasWitnessPeriod a (a + 1) ∧
      ∀ p, HasWitnessPeriod a p → p = a + 1 := by
  refine ⟨exampleExpression_restricted,
    exampleExpression_universal, ?_⟩
  intro B
  refine ⟨B + 3, by omega,
    exampleWord_routeFree (B + 3) (by omega), by omega, ?_, ?_⟩
  · exact (hasWitnessPeriod_iff (B + 3) (B + 4) (by omega)).2 rfl
  · intro p hp
    exact (hasWitnessPeriod_iff (B + 3) p (by omega)).1 hp

end UnboundedPeriodExample

end NSSE
