import NSSE.BitMachine
import NSSE.SevenExpTimeTarget

/-! # The machine model captures the regular languages, in linear time

A sanity check on the model of v1627, and a supply of non-vacuous instances for
the claim shape of v1628: every DFA over the bit alphabet is simulated by a bit
machine that reads each input bit once and halts one step later, so every
regular language is decided within `|w|+1` steps and hence lies inside
`SevenExpTime`.

This is what the model is worth on its own; it does not touch the decision
procedure of the development, whose realisation remains the open part of
`SevenExpTimeTarget.SevenExpTime (entailmentLanguage d hd)`.
-/

namespace NSSE.BitMachineRegular

open DirectRankStateTower BitMachine SevenExpTimeTarget

variable {Q : Type}

/-- Control states: one per DFA state, plus the two answers. -/
inductive St (Q : Type)
  | run (q : Q)
  | out (b : Bool)

/-- The DFA is the control: one step per input bit, then one step to the
answer state. -/
def dfaProg (A : DFA Bool Q) (acc : Q → Bool) : St Q → Instr (St Q)
  | .run q => .read (.run (A.step q true)) (.run (A.step q false)) (.out (acc q))
  | .out _ => .halt

theorem dfa_run (A : DFA Bool Q) (acc : Q → Bool) (w : List Bool) (q : Q) :
    iter (dfaProg A acc) (w.length+1) ⟨.run q,w,[],[]⟩
      = ⟨.out (acc (A.runFrom q w)),[],[],[]⟩ := by
  induction w generalizing q with
  | nil =>
    simp only [List.length_nil, Nat.zero_add]
    rw [iter_one (dfaProg A acc) (c' := ⟨.out (acc q),[],[],[]⟩) rfl]
    rfl
  | cons x w ih =>
    have he : (x :: w).length+1 = (w.length+1)+1 := by simp
    rw [he, Nat.add_comm (w.length+1) 1]
    cases x with
    | false =>
      rw [iter_step' (dfaProg A acc) (c' := ⟨.run (A.step q false),w,[],[]⟩) rfl]
      rw [ih]
      rfl
    | true =>
      rw [iter_step' (dfaProg A acc) (c' := ⟨.run (A.step q true),w,[],[]⟩) rfl]
      rw [ih]
      rfl

theorem dfa_halted (A : DFA Bool Q) (acc : Q → Bool) (w : List Bool) :
    step (dfaProg A acc) (iter (dfaProg A acc) (w.length+1) ⟨.run A.start,w,[],[]⟩) = none := by
  rw [dfa_run]
  rfl

/-- The decider built from a DFA. -/
def dfaDecider (A : DFA Bool Q) (acc : Q → Bool) : BitDecider where
  State := St Q
  prog := dfaProg A acc
  start := .run A.start
  accept := fun s => match s with | .run _ => false | .out b => b

theorem dfa_decides (A : DFA Bool Q) (acc : Q → Bool) (T : Nat → Nat)
    (hT : ∀ w : List Bool, w.length+1 ≤ T w.length) :
    Decides (dfaDecider A acc) (fun w => acc (A.run w)) T := by
  intro w
  obtain ⟨m,hm⟩ : ∃ m, T w.length = (w.length+1)+m := ⟨T w.length-(w.length+1),by
    have := hT w; omega⟩
  have hrun : iter (dfaDecider A acc).prog (w.length+1) ⟨(dfaDecider A acc).start,w,[],[]⟩
      = ⟨.out (acc (A.run w)),[],[],[]⟩ := dfa_run A acc w A.start
  constructor
  · rw [hm, iter_add, hrun, iter_halt (dfaDecider A acc).prog _ rfl]
    rfl
  · rw [hm, iter_add, hrun, iter_halt (dfaDecider A acc).prog _ rfl]
    rfl

/-- Every language decided by a DFA on bits is in the class, by a machine that
reads its input once. -/
theorem sevenExpTime_of_dfa (A : DFA Bool Q) (acc : Q → Bool) :
    SevenExpTime (fun w => acc (A.run w)) :=
  ⟨dfaDecider A acc,fun L => L+1,⟨1,1,fun L => by simp⟩,
    dfa_decides A acc _ (fun w => CodedTermEntailment.self_le_tower 7 (w.length+1))⟩

end NSSE.BitMachineRegular
