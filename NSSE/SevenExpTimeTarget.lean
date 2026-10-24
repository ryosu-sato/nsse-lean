import NSSE.BitMachine
import NSSE.CodedTermEntailment

/-! # The 7-EXPTIME claim, as a formal statement

Everything on this line has been phrased so far as bounds on a counted step
measure. This file writes down, in Lean, what the complexity claim itself says,
on the bit machine of v1627 — so that "7-EXPTIME" is a proposition in the
development rather than prose, and so that what is still missing is a named
goal rather than a paragraph.

* `Decides M f time` — the machine `M`, started on `w` with empty stacks, has
  halted after `time |w|` steps and its halting state answers `f w`.
* `SevenExpTime f` — some bit-machine decides `f` within `tower 7 (p |w|)`
  steps for some polynomially bounded `p`.
* `entailmentLanguage d` — the language of bit strings that encode an ENTAILED
  query, via the decision of v1624; `language_spec` says exactly that.

`SevenExpTime (entailmentLanguage d)` is the open target. What is already
proved towards it is the COUNTED bound of v1624 (`finite_bound`), the
absorption calculus of v1625 (any polynomial per-step overhead keeps the tower
height), and one stage realised on this very machine in v1627.
-/

namespace NSSE.SevenExpTimeTarget

open DirectRankStateTower BitMachine RawQueryCodec CodedQueryConversion CodedTermEntailment
open SubtypeTerms

/-! ## Deciding a language on the bit machine -/

structure BitDecider where
  State : Type
  prog : State → Instr State
  start : State
  accept : State → Bool

def Decides (M : BitDecider) (f : List Bool → Bool) (time : Nat → Nat) : Prop :=
  ∀ w : List Bool,
    step M.prog (iter M.prog (time w.length) ⟨M.start,w,[],[]⟩) = none ∧
      M.accept (iter M.prog (time w.length) ⟨M.start,w,[],[]⟩).state = f w

/-- Polynomially bounded, in the only sense a time bound needs. -/
def IsPoly (p : Nat → Nat) : Prop := ∃ k c : Nat, ∀ L, p L ≤ c*(L+1)^k

def SevenExpTime (f : List Bool → Bool) : Prop :=
  ∃ (M : BitDecider) (p : Nat → Nat), IsPoly p ∧ Decides M f (fun L => tower 7 (p L))

/-! ## The definition is not vacuous -/

private inductive Triv | go | yes | no
  deriving DecidableEq

private def trivProg : Triv → Instr Triv
  | .go => .halt
  | .yes => .halt
  | .no => .halt

/-- The always-true language is decided in zero steps. -/
theorem sevenExpTime_const : SevenExpTime (fun _ => true) := by
  refine ⟨⟨Triv,trivProg,.go,fun _ => true⟩,fun _ => 0,⟨0,0,fun _ => by simp⟩,fun w => ?_⟩
  rw [iter_halt trivProg _ rfl]
  exact ⟨rfl,rfl⟩

private inductive Bit | start | yes | no
  deriving DecidableEq

private def bitProg : Bit → Instr Bit
  | .start => .read .yes .no .no
  | .yes => .halt
  | .no => .halt

private def bitAccept : Bit → Bool
  | .yes => true
  | _ => false

private theorem bit_decides (T : Nat) (hT : 1 ≤ T) (w : List Bool) :
    step bitProg (iter bitProg T ⟨.start,w,[],[]⟩) = none ∧
      bitAccept (iter bitProg T ⟨.start,w,[],[]⟩).state = w.head?.getD false := by
  obtain ⟨m,rfl⟩ : ∃ m, T = m+1 := ⟨T-1,by omega⟩
  cases w with
  | nil =>
    rw [iter_step bitProg (c' := ⟨.no,[],[],[]⟩) rfl, iter_halt bitProg _ rfl]
    exact ⟨rfl,rfl⟩
  | cons b w =>
    cases b with
    | false =>
      rw [iter_step bitProg (c' := ⟨.no,w,[],[]⟩) rfl, iter_halt bitProg _ rfl]
      exact ⟨rfl,rfl⟩
    | true =>
      rw [iter_step bitProg (c' := ⟨.yes,w,[],[]⟩) rfl, iter_halt bitProg _ rfl]
      exact ⟨rfl,rfl⟩

private theorem bit_decidesD (T : Nat → Nat) (hT : ∀ L, 1 ≤ T L) :
    Decides ⟨Bit,bitProg,.start,bitAccept⟩ (fun w => w.head?.getD false) T :=
  fun w => bit_decides (T w.length) (hT _) w

/-- "The first input bit is `1`" is decided in one step, hence inside every
tower bound. -/
theorem sevenExpTime_firstBit : SevenExpTime (fun w => w.head?.getD false) :=
  ⟨⟨Bit,bitProg,.start,bitAccept⟩,fun _ => 1,⟨0,1,fun _ => by simp⟩,
    bit_decidesD _ (fun _ => CodedTermEntailment.self_le_tower 7 1)⟩

/-! ## The language of the problem -/

variable {n d : Nat}

/-- Bit strings that encode an entailed query; strings that are not codes are
rejected. -/
def entailmentLanguage (d : Nat) (hd : 0 < d) (w : List Bool) : Bool :=
  ((decideFinite d w hd).1).getD false

theorem language_spec (Q : Query n d) (hd : 0 < d) :
    entailmentLanguage d hd (encQuery (rawOfQuery Q)) = true ↔
      Entails (FiniteSubtypeTrees.constructor d) Q := by
  unfold entailmentLanguage
  constructor
  · intro h
    refine (finite_correct Q hd).mp ?_
    cases hc : (decideFinite d (encQuery (rawOfQuery Q)) hd).1 with
    | none => rw [hc] at h; simp at h
    | some b => rw [hc] at h; simp at h; rw [h]
  · intro h
    rw [(finite_correct Q hd).mpr h]
    rfl

/-- The arbitrary-tree (equivalently regular-tree) language, for completeness. -/
def arbitraryLanguage (d : Nat) (hd : 0 < d) (w : List Bool) : Bool :=
  ((decideAll d w hd).1).getD false

theorem arbitrary_language_spec (Q : Query n d) (hd : 0 < d) :
    arbitraryLanguage d hd (encQuery (rawOfQuery Q)) = true ↔
      Entails (AbsorbingSubtypeTrees.constructor d) Q := by
  unfold arbitraryLanguage
  constructor
  · intro h
    refine (arbitrary_correct Q hd).mp ?_
    cases hc : (decideAll d (encQuery (rawOfQuery Q)) hd).1 with
    | none => rw [hc] at h; simp at h
    | some b => rw [hc] at h; simp at h; rw [h]
  · intro h
    rw [(arbitrary_correct Q hd).mpr h]
    rfl

/-! ## The target, and the evidence

`SevenExpTime (entailmentLanguage d hd)` is exactly the complexity claim for
non-structural subtype entailment over one covariant constructor of positive
arity, over finite trees; `arbitraryLanguage` is the same for arbitrary and
regular trees. Neither is proved.

The counted evidence is `CodedTermEntailment.finite_bound`: the counted step
number of the very function these languages are defined from is at most
`tower 7 (argument |w| d + 1)`, and `argument` is a polynomial, as
`argument_isPoly` records. What is missing is a machine realisation of that
counted program — v1627 realises one stage of it.
-/

/-- The same shape of statement in the COUNTED cost model: the counted step
number of the decision, decoding included, is at most `tower 7` of a polynomial
in the input length. This is what IS proved; `SevenExpTime` above is the
machine statement, which is not. The two are separated on purpose: a counted
step is a step of the Lean implementation, and the passage to machine time is
the premise isolated in `MachineTimeBound`. -/
def SevenExpTimeCounted (cost : List Bool → Nat) : Prop :=
  ∃ p : Nat → Nat, IsPoly p ∧ ∀ w : List Bool, cost w ≤ tower 7 (p w.length)

theorem argument_isPoly (d : Nat) : IsPoly (fun L => argument L d+1) := by
  refine ⟨8,16*(d+1)^4+40*(d+1)^3+53*(d+1)^2+34*(d+1)+d+74427,fun L => ?_⟩
  have h2 : (L+1)^2 ≤ (L+1)^8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : ((L+1)^2)^4 = (L+1)^8 := by rw [← pow_mul]
  have h3 : ((L+1)^2)^3 ≤ (L+1)^8 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h22 : ((L+1)^2)^2 ≤ (L+1)^8 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : (1:Nat) ≤ (L+1)^8 := Nat.one_le_pow _ _ (by omega)
  have e1 : 16*((d+1)*(L+1)^2)^4 = 16*(d+1)^4*((L+1)^2)^4 := by ring
  have e2 : 40*((d+1)*(L+1)^2)^3 = 40*(d+1)^3*((L+1)^2)^3 := by ring
  have e3 : 53*((d+1)*(L+1)^2)^2 = 53*(d+1)^2*((L+1)^2)^2 := by ring
  have e4 : 34*((d+1)*(L+1)^2) = 34*(d+1)*(L+1)^2 := by ring
  show argument L d+1 ≤ _
  unfold argument
  rw [e1, e2, e3, e4, h4, add_mul, add_mul, add_mul, add_mul, add_mul]
  have b2 := Nat.mul_le_mul_left (40*(d+1)^3) h3
  have b3 := Nat.mul_le_mul_left (53*(d+1)^2) h22
  have b4 := Nat.mul_le_mul_left (34*(d+1)) h2
  have b5 := Nat.mul_le_mul_left d h1
  have b6 := Nat.mul_le_mul_left 74427 h1
  omega

/-- What is proved, stated once: deciding whether a bit string encodes an
entailed query costs at most seven exponentials of a polynomial in its length,
counted steps, decoding included. -/
theorem entailment_counted (d : Nat) (hd : 0 < d) :
    SevenExpTimeCounted (fun w => (decideFinite d w hd).2) :=
  ⟨fun L => argument L d+1,argument_isPoly d,fun w => finite_bound d w hd⟩

theorem arbitrary_counted (d : Nat) (hd : 0 < d) :
    SevenExpTimeCounted (fun w => (decideAll d w hd).2) :=
  ⟨fun L => argument L d+1,argument_isPoly d,fun w => all_bound d w hd⟩

end NSSE.SevenExpTimeTarget
