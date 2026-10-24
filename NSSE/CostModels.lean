import NSSE.SevenExpTime

/-! # Models of computation, and the claim relative to one

The complexity claim has the same shape in any model: some program of the model
answers the language, and its running time on inputs of length `L` is at most
`tower 7 (p L)` for a polynomially bounded `p`. This file makes the model a
PARAMETER, so the claim can be stated uniformly and the difference between
models is a difference of instance rather than of wording.

Two instances are given:

* `counted` — programs are the counted functions of this development, the time
  of a program on an input is the step count it charges. This is the model
  adopted for the statement (maintainer's decision, 2026-09-18);
* `bitMachine` — programs are the two-stack bit machines of v1627, the time is
  the number of steps until halting. Nothing is free there: one step reads or
  moves one bit.

`sevenExpTime_counted` proves the claim in the first model. The same claim in
the second, `SevenExpTimeIn bitMachine (entailmentLanguage d hd)`, is the open
refinement; `MachineTimeBound` (v1625) proves that no polynomial per-step
overhead can change the tower height between them, and `BitMachine` (v1627)
realises the first stage.
-/

namespace NSSE.CostModels

open DirectRankStateTower BitMachine CodedTermEntailment SevenExpTimeTarget

universe u

/-- A model of computation for languages of bit strings. -/
structure Model : Type (u+1) where
  Program : Type u
  answer : Program → List Bool → Bool
  time : Program → List Bool → Nat

def DecidesIn (M : Model.{u}) (f : List Bool → Bool) (bound : Nat → Nat) : Prop :=
  ∃ P : M.Program, (∀ w, M.answer P w = f w) ∧ ∀ w, M.time P w ≤ bound w.length

/-- The claim, relative to a model: decided within `tower 7` of a polynomial. -/
def SevenExpTimeIn (M : Model.{u}) (f : List Bool → Bool) : Prop :=
  ∃ p : Nat → Nat, IsPoly p ∧ DecidesIn M f (fun L => tower 7 (p L))

/-! ## The counted model -/

/-- Programs are counted functions: a Boolean and the number of elementary
steps charged for producing it. -/
def counted : Model where
  Program := List Bool → Bool × Nat
  answer := fun P w => (P w).1
  time := fun P w => (P w).2

/-! ## The bit-machine model -/

open Classical in
/-- The number of steps until the machine halts, `0` if it never does. -/
noncomputable def haltTime (M : BitDecider) (w : List Bool) : Nat :=
  if h : ∃ T, step M.prog (iter M.prog T ⟨M.start,w,[],[]⟩) = none then Nat.find h else 0

open Classical in
noncomputable def bitMachine : Model where
  Program := BitDecider
  answer := fun M w => M.accept (iter M.prog (haltTime M w) ⟨M.start,w,[],[]⟩).state
  time := haltTime

/-! ## The result, in the adopted model -/

variable {d : Nat}

/-- **7-EXPTIME in the adopted (counted) model**, for the language of codes of
entailed queries over finite trees. -/
theorem sevenExpTime_counted (d : Nat) (hd : 0 < d) :
    SevenExpTimeIn counted (entailmentLanguage d hd) := by
  refine ⟨fun L => argument L d+1,argument_isPoly d,
    ⟨fun w => (((decideFinite d w hd).1).getD false,(decideFinite d w hd).2),fun w => rfl,?_⟩⟩
  intro w
  exact finite_bound d w hd

/-- The same for arbitrary trees (equivalently, regular trees). -/
theorem sevenExpTime_counted_arbitrary (d : Nat) (hd : 0 < d) :
    SevenExpTimeIn counted (arbitraryLanguage d hd) := by
  refine ⟨fun L => argument L d+1,argument_isPoly d,
    ⟨fun w => (((decideAll d w hd).1).getD false,(decideAll d w hd).2),fun w => rfl,?_⟩⟩
  intro w
  exact all_bound d w hd

/-- What the theorem above says about the ORIGINAL problem: the program of the
model answers, on the code of a query, exactly the original entailment. -/
theorem counted_program_spec (d : Nat) (hd : 0 < d) {n : Nat} (Q : SubtypeTerms.Query n d) :
    entailmentLanguage d hd (RawQueryCodec.encQuery (CodedQueryConversion.rawOfQuery Q)) = true ↔
      SubtypeTerms.Entails (FiniteSubtypeTrees.constructor d) Q :=
  language_spec Q hd

/-! ## The open refinement

`SevenExpTimeIn bitMachine (entailmentLanguage d hd)` is the machine-level
claim. It is not proved here, and this file does not assume it. The two models
are related by `MachineTimeBound.PolynomiallyFaithful`: under any polynomial
per-step overhead the tower height is the same, so the refinement can only
change the additive constant in the argument, not the class.
-/

end NSSE.CostModels
