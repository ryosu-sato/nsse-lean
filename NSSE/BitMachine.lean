import NSSE.RawBitNumeral
import NSSE.RawTermCodec

/-! # A bit-level machine, and the first counted stage realised on it

`MachineTimeBound.PolynomiallyFaithful` is the one premise between the counted
step measure and machine time. Discharging it needs an actual machine model and
actual programs. This file supplies the model and the first program.

The model is deliberately primitive, so that no step hides work: a
deterministic two-stack machine over BITS with finite control. One step reads
one input bit, or pushes or pops one bit, and nothing else — in particular no
arithmetic on large numbers is available for free, which is exactly the
objection against unit-cost models.

`numeral` is the machine program for the self-delimiting numeral decoder of
v1622 (`RawBitNumeral.encNat`). `numeral_run` proves it consumes exactly the
numeral, leaves the rest of the input untouched, produces the bits of the
identifier on the second stack, and halts within `5*L+2` steps, `L` the number
of bits of the identifier — linear in the piece of input consumed, hence within
a constant factor of the counted cost of `decNat`.
-/

namespace NSSE.BitMachine

open RawBitNumeral RawTermCodec

/-! ## The model -/

structure Config (Q : Type) where
  state : Q
  input : List Bool
  a : List Bool
  b : List Bool

inductive Instr (Q : Type)
  | read (onTrue onFalse onEmpty : Q)
  | pushA (bit : Bool) (next : Q)
  | pushB (bit : Bool) (next : Q)
  | popA (onSome onEmpty : Q)
  | popB (onSome onEmpty : Q)
  | popValA (onTrue onFalse onEmpty : Q)
  | popValB (onTrue onFalse onEmpty : Q)
  | nop (next : Q)
  | halt

variable {Q : Type}

def step (P : Q → Instr Q) (c : Config Q) : Option (Config Q) :=
  match P c.state with
  | .halt => none
  | .read t f e =>
    match c.input with
    | [] => some ⟨e,[],c.a,c.b⟩
    | true :: w => some ⟨t,w,c.a,c.b⟩
    | false :: w => some ⟨f,w,c.a,c.b⟩
  | .pushA bit next => some ⟨next,c.input,bit :: c.a,c.b⟩
  | .pushB bit next => some ⟨next,c.input,c.a,bit :: c.b⟩
  | .popA s e =>
    match c.a with
    | [] => some ⟨e,c.input,[],c.b⟩
    | _ :: r => some ⟨s,c.input,r,c.b⟩
  | .popB s e =>
    match c.b with
    | [] => some ⟨e,c.input,c.a,[]⟩
    | _ :: r => some ⟨s,c.input,c.a,r⟩
  | .popValA t f e =>
    match c.a with
    | [] => some ⟨e,c.input,[],c.b⟩
    | true :: r => some ⟨t,c.input,r,c.b⟩
    | false :: r => some ⟨f,c.input,r,c.b⟩
  | .popValB t f e =>
    match c.b with
    | [] => some ⟨e,c.input,c.a,[]⟩
    | true :: r => some ⟨t,c.input,c.a,r⟩
    | false :: r => some ⟨f,c.input,c.a,r⟩
  | .nop next => some ⟨next,c.input,c.a,c.b⟩

/-- Run for at most `n` steps; a halted configuration is a fixed point, so this
is an upper bound on the machine time and composes without side conditions. -/
def iter (P : Q → Instr Q) : Nat → Config Q → Config Q
  | 0, c => c
  | n+1, c =>
    match step P c with
    | none => c
    | some c' => iter P n c'

theorem iter_halt (P : Q → Instr Q) (c : Config Q) (h : step P c = none) (n : Nat) :
    iter P n c = c := by
  cases n with
  | zero => rfl
  | succ n => simp only [iter, h]

theorem iter_step (P : Q → Instr Q) {c c' : Config Q} (h : step P c = some c') (n : Nat) :
    iter P (n+1) c = iter P n c' := by
  simp only [iter, h]

theorem iter_step' (P : Q → Instr Q) {c c' : Config Q} (h : step P c = some c') (n : Nat) :
    iter P (1+n) c = iter P n c' := by
  rw [Nat.add_comm]
  exact iter_step P h n

theorem iter_one (P : Q → Instr Q) {c c' : Config Q} (h : step P c = some c') :
    iter P 1 c = c' := by
  show (match step P c with | none => c | some c'' => iter P 0 c'') = c'
  rw [h]
  rfl

theorem iter_add (P : Q → Instr Q) (m n : Nat) (c : Config Q) :
    iter P (m+n) c = iter P n (iter P m c) := by
  induction m generalizing c with
  | zero => simp [iter]
  | succ m ih =>
    cases h : step P c with
    | none =>
      rw [iter_halt P c h, iter_halt P c h, iter_halt P c h]
    | some c' =>
      have he : m+1+n = (m+n)+1 := by omega
      rw [he, iter_step P h, iter_step P h, ih]

/-! ## The numeral decoder as a program -/

inductive St
  | count
  | mark
  | next
  | digit
  | keep0
  | keep1
  | done
  deriving DecidableEq

def numeral : St → Instr St
  | .count => .read .mark .next .done
  | .mark => .pushA true .count
  | .next => .popA .digit .done
  | .digit => .read .keep1 .keep0 .done
  | .keep0 => .pushB false .next
  | .keep1 => .pushB true .next
  | .done => .halt

theorem replicate_cons (L : Nat) (x : Bool) (a : List Bool) :
    List.replicate L x ++ x :: a = List.replicate (L+1) x ++ a := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [List.replicate_succ, List.cons_append, ih]

/-! ### Phase one: the unary length prefix -/

theorem phase_count (L : Nat) (w a b : List Bool) :
    iter numeral (2*L+1) ⟨.count,List.replicate L true ++ false :: w,a,b⟩
      = ⟨.next,w,List.replicate L true ++ a,b⟩ := by
  induction L generalizing a with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rw [iter_step numeral (c' := ⟨.next,w,a,b⟩) rfl]
    rfl
  | succ L ih =>
    have he : 2*(L+1)+1 = (2*L+1)+1+1 := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step numeral
      (c' := ⟨.mark,List.replicate L true ++ false :: w,a,b⟩) rfl]
    rw [iter_step numeral
      (c' := ⟨.count,List.replicate L true ++ false :: w,true :: a,b⟩) rfl]
    rw [ih, replicate_cons, List.replicate_succ, List.cons_append]

/-! ### Phase two: the bits, one marker each -/

theorem phase_digits (bits : List Bool) (w a b : List Bool) :
    iter numeral (3*bits.length) ⟨.next,bits ++ w,List.replicate bits.length true ++ a,b⟩
      = ⟨.next,w,a,bits.reverse ++ b⟩ := by
  induction bits generalizing b with
  | nil => simp [iter]
  | cons x bits ih =>
    have he : 3*(x :: bits).length = (3*bits.length)+1+1+1 := by
      simp only [List.length_cons]; ring
    rw [he]
    simp only [List.length_cons, List.replicate_succ, List.cons_append]
    rw [iter_step numeral
      (c' := ⟨.digit,x :: (bits ++ w),List.replicate bits.length true ++ a,b⟩) rfl]
    cases x with
    | false =>
      rw [iter_step numeral
        (c' := ⟨.keep0,bits ++ w,List.replicate bits.length true ++ a,b⟩) rfl]
      rw [iter_step numeral
        (c' := ⟨.next,bits ++ w,List.replicate bits.length true ++ a,false :: b⟩) rfl]
      rw [ih]
      simp
    | true =>
      rw [iter_step numeral
        (c' := ⟨.keep1,bits ++ w,List.replicate bits.length true ++ a,b⟩) rfl]
      rw [iter_step numeral
        (c' := ⟨.next,bits ++ w,List.replicate bits.length true ++ a,true :: b⟩) rfl]
      rw [ih]
      simp

/-! ### The numeral decoder, realised -/

theorem numeral_run (i : Nat) (w : List Bool) :
    iter numeral (5*(toBits i).length+2) ⟨.count,encNat i ++ w,[],[]⟩
      = ⟨.done,w,[],(toBits i).reverse⟩ := by
  have he : 5*(toBits i).length+2 = (2*(toBits i).length+1)+(3*(toBits i).length+1) := by ring
  simp only [encNat, List.append_assoc, List.cons_append]
  rw [he, iter_add, phase_count, iter_add, phase_digits]
  rw [iter_step numeral (c' := ⟨.done,w,[],(toBits i).reverse ++ []⟩) rfl]
  simp only [List.append_nil]
  rfl

theorem numeral_halted (i : Nat) (w : List Bool) :
    step numeral (iter numeral (5*(toBits i).length+2) ⟨.count,encNat i ++ w,[],[]⟩) = none := by
  rw [numeral_run]
  rfl

/-- The machine time of the realised stage is linear in the piece of input it
consumes. -/
theorem numeral_time (i : Nat) : 5*(toBits i).length+2 ≤ 3*(encNat i).length := by
  rw [encNat_length]
  omega


/-! ## The numeral decoder as a reusable COMPONENT

The standalone program above assumes it starts with empty stacks. A component
that is to be used inside a larger program may not: it must pop only its own
markers. The fix is one sentinel bit: the caller pushes `false` on stack A and
enters at `count`; the component pushes `true` markers, consumes them, and the
final pop — the one that sees the sentinel — leaves for `exit` with the stack
exactly as the caller left it.

`numeralCode` is the code, parameterised by the embedding of its states into a
bigger state type and by the exit and failure continuations;
`numeral_component` is its correctness and exact step count, for ANY program
agreeing with `numeralCode` on the embedded states.
-/

inductive NSt
  | count
  | mark
  | next
  | digit
  | keep0
  | keep1
  deriving DecidableEq

def numeralCode {Q : Type} (emb : NSt → Q) (exit fail : Q) : NSt → Instr Q
  | .count => .read (emb .mark) (emb .next) fail
  | .mark => .pushA true (emb .count)
  | .next => .popValA (emb .digit) exit fail
  | .digit => .read (emb .keep1) (emb .keep0) fail
  | .keep0 => .pushB false (emb .next)
  | .keep1 => .pushB true (emb .next)

section Component

variable {Q : Type} (P : Q → Instr Q) (emb : NSt → Q) (exit fail : Q)
  (hP : ∀ s, P (emb s) = numeralCode emb exit fail s)

include hP

theorem comp_count (L : Nat) (w S b : List Bool) :
    iter P (2*L+1) ⟨emb .count,List.replicate L true ++ false :: w,S,b⟩
      = ⟨emb .next,w,List.replicate L true ++ S,b⟩ := by
  induction L generalizing S with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rw [iter_step P (c' := ⟨emb .next,w,S,b⟩) (by simp [step, hP, numeralCode])]
    rfl
  | succ L ih =>
    have he : 2*(L+1)+1 = (2*L+1)+1+1 := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step P (c' := ⟨emb .mark,List.replicate L true ++ false :: w,S,b⟩)
      (by simp [step, hP, numeralCode])]
    rw [iter_step P (c' := ⟨emb .count,List.replicate L true ++ false :: w,true :: S,b⟩)
      (by simp [step, hP, numeralCode])]
    rw [ih, replicate_cons, List.replicate_succ, List.cons_append]

theorem comp_digits (bits : List Bool) (w S b : List Bool) :
    iter P (3*bits.length) ⟨emb .next,bits ++ w,List.replicate bits.length true ++ S,b⟩
      = ⟨emb .next,w,S,bits.reverse ++ b⟩ := by
  induction bits generalizing b with
  | nil => simp [iter]
  | cons x bits ih =>
    have he : 3*(x :: bits).length = (3*bits.length)+1+1+1 := by
      simp only [List.length_cons]; ring
    rw [he]
    simp only [List.length_cons, List.replicate_succ, List.cons_append]
    rw [iter_step P (c' := ⟨emb .digit,x :: (bits ++ w),List.replicate bits.length true ++ S,b⟩)
      (by simp [step, hP, numeralCode])]
    cases x with
    | false =>
      rw [iter_step P (c' := ⟨emb .keep0,bits ++ w,List.replicate bits.length true ++ S,b⟩)
        (by simp [step, hP, numeralCode])]
      rw [iter_step P
        (c' := ⟨emb .next,bits ++ w,List.replicate bits.length true ++ S,false :: b⟩)
        (by simp [step, hP, numeralCode])]
      rw [ih]
      simp
    | true =>
      rw [iter_step P (c' := ⟨emb .keep1,bits ++ w,List.replicate bits.length true ++ S,b⟩)
        (by simp [step, hP, numeralCode])]
      rw [iter_step P
        (c' := ⟨emb .next,bits ++ w,List.replicate bits.length true ++ S,true :: b⟩)
        (by simp [step, hP, numeralCode])]
      rw [ih]
      simp

/-- The component: entered at `count` with a sentinel `false` on stack A, it
consumes exactly one encoded identifier, restores the stack, leaves the rest of
the input untouched, pushes the identifier's bits on stack B, and reaches
`exit` in `5L+2` steps. -/
theorem numeral_component (i : Nat) (w A b : List Bool) :
    iter P (5*(toBits i).length+2) ⟨emb .count,encNat i ++ w,false :: A,b⟩
      = ⟨exit,w,A,(toBits i).reverse ++ b⟩ := by
  have he : 5*(toBits i).length+2 = (2*(toBits i).length+1)+(3*(toBits i).length+1) := by ring
  simp only [encNat, List.append_assoc, List.cons_append]
  rw [he, iter_add, comp_count P emb exit fail hP, iter_add,
    comp_digits P emb exit fail hP]
  rw [iter_step P (c' := ⟨exit,w,A,(toBits i).reverse ++ b⟩) (by simp [step, hP, numeralCode])]
  rfl

end Component


/-! ## The term parser as a component

Pending slots are kept on stack A: one `true` marker per term still to be
parsed after the current one, and a `false` sentinel marking the caller's
boundary. A term that finishes pops one element: a marker means a sibling is
pending and parsing continues; the sentinel means the whole term is parsed and
the component leaves for `exit`. Node arity is fixed, so a node pushes `d-1`
markers and starts on its first child; the last child's completion IS the
node's completion. Identifiers are read by the numeral component above, behind
its own sentinel.
-/

inductive TSt
  | tok
  | t1
  | f1
  | numSentinel
  | push (k : Nat)
  | complete
  | num (s : NSt)
  deriving DecidableEq

def termCode (d : Nat) {Q : Type} (emb : TSt → Q) (exit fail : Q) : TSt → Instr Q
  | .tok => .read (emb .t1) (emb .f1) fail
  | .f1 => .read (emb .complete) (emb .complete) fail
  | .t1 => .read (emb .numSentinel) (emb (.push (d-1))) fail
  | .numSentinel => .pushA false (emb (.num .count))
  | .push 0 => .nop (emb .tok)
  | .push (k+1) => .pushA true (emb (.push k))
  | .complete => .popValA (emb .tok) exit fail
  | .num s => numeralCode (fun s' => emb (.num s')) (emb .complete) fail s

/-- Machine steps of the term component on a well-formed term. -/
def termTime (d : Nat) : Raw → Nat
  | .bot => 3
  | .top => 3
  | .var i => 5*(toBits i).length+6
  | .node cs => 2+d+(cs.map (termTime d)).sum

section TermComponent

variable {Q : Type} (P : Q → Instr Q) (d : Nat) (emb : TSt → Q) (exit fail : Q)
  (hd : 0 < d) (hP : ∀ s, P (emb s) = termCode d emb exit fail s)

include hP

/-- The state reached when a finished term pops one pending slot. -/
def afterState : List Bool → Q
  | [] => fail
  | true :: _ => emb .tok
  | false :: _ => exit

theorem push_chain (k : Nat) (inp A b : List Bool) :
    iter P (k+1) ⟨emb (.push k),inp,A,b⟩ = ⟨emb .tok,inp,List.replicate k true ++ A,b⟩ := by
  induction k generalizing A with
  | zero =>
    rw [iter_step P (c' := ⟨emb .tok,inp,A,b⟩) (by simp [step, hP, termCode])]
    rfl
  | succ k ih =>
    rw [show k+1+1 = (k+1)+1 from rfl]
    rw [iter_step P (c' := ⟨emb (.push k),inp,true :: A,b⟩) (by simp [step, hP, termCode])]
    rw [ih]
    rw [replicate_cons, List.replicate_succ, List.cons_append]

theorem numeral_inside (i : Nat) (w A b : List Bool) :
    iter P (5*(toBits i).length+2) ⟨emb (.num .count),encNat i ++ w,false :: A,b⟩
      = ⟨emb .complete,w,A,(toBits i).reverse ++ b⟩ :=
  numeral_component P (fun s => emb (.num s)) (emb .complete) fail
    (fun s => by rw [hP (.num s)]; rfl) i w A b

include hd in
theorem term_component :
    (∀ t : Raw, WellFormed d t → ∀ rest A b : List Bool, ∃ b',
        iter P (termTime d t) ⟨emb .tok,enc t ++ rest,A,b⟩
          = ⟨afterState emb exit fail A,rest,A.tail,b'⟩) ∧
    (∀ ts : List Raw, ts ≠ [] → (∀ c ∈ ts, WellFormed d c) → ∀ rest A b : List Bool, ∃ b',
        iter P ((ts.map (termTime d)).sum)
            ⟨emb .tok,ts.flatMap enc ++ rest,List.replicate (ts.length-1) true ++ A,b⟩
          = ⟨afterState emb exit fail A,rest,A.tail,b'⟩) := by
  refine rec2
    (P := fun t => WellFormed d t → ∀ rest A b : List Bool, ∃ b',
      iter P (termTime d t) ⟨emb .tok,enc t ++ rest,A,b⟩
        = ⟨afterState emb exit fail A,rest,A.tail,b'⟩)
    (Q := fun ts => ts ≠ [] → (∀ c ∈ ts, WellFormed d c) → ∀ rest A b : List Bool, ∃ b',
      iter P ((ts.map (termTime d)).sum)
          ⟨emb .tok,ts.flatMap enc ++ rest,List.replicate (ts.length-1) true ++ A,b⟩
        = ⟨afterState emb exit fail A,rest,A.tail,b'⟩)
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- var
    intro i _ rest A b
    refine ⟨(toBits i).reverse ++ b,?_⟩
    have he : termTime d (Raw.var i) = 1+(1+(1+((5*(toBits i).length+2)+1))) := by
      simp only [termTime]; omega
    rw [he]
    simp only [enc, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .t1,true :: (encNat i ++ rest),A,b⟩)
      (by simp [step, hP, termCode])]
    rw [iter_step' P (c' := ⟨emb .numSentinel,encNat i ++ rest,A,b⟩)
      (by simp [step, hP, termCode])]
    rw [iter_step' P (c' := ⟨emb (.num .count),encNat i ++ rest,false :: A,b⟩)
      (by simp [step, hP, termCode])]
    rw [iter_add, numeral_inside P d emb exit fail hP]
    cases A with
    | nil =>
      rw [iter_one P (c' := ⟨fail,rest,[],(toBits i).reverse ++ b⟩)
        (by simp [step, hP, termCode])]
      rfl
    | cons x A =>
      cases x with
      | false =>
        rw [iter_one P (c' := ⟨exit,rest,A,(toBits i).reverse ++ b⟩)
          (by simp [step, hP, termCode])]
        rfl
      | true =>
        rw [iter_one P (c' := ⟨emb .tok,rest,A,(toBits i).reverse ++ b⟩)
          (by simp [step, hP, termCode])]
        rfl
  · -- bot
    intro _ rest A b
    refine ⟨b,?_⟩
    have he : termTime d Raw.bot = 1+(1+1) := by simp only [termTime]
    rw [he]
    simp only [enc, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .f1,false :: rest,A,b⟩) (by simp [step, hP, termCode])]
    rw [iter_step' P (c' := ⟨emb .complete,rest,A,b⟩) (by simp [step, hP, termCode])]
    cases A with
    | nil =>
      rw [iter_one P (c' := ⟨fail,rest,[],b⟩) (by simp [step, hP, termCode])]
      rfl
    | cons x A =>
      cases x with
      | false =>
        rw [iter_one P (c' := ⟨exit,rest,A,b⟩) (by simp [step, hP, termCode])]
        rfl
      | true =>
        rw [iter_one P (c' := ⟨emb .tok,rest,A,b⟩) (by simp [step, hP, termCode])]
        rfl
  · -- top
    intro _ rest A b
    refine ⟨b,?_⟩
    have he : termTime d Raw.top = 1+(1+1) := by simp only [termTime]
    rw [he]
    simp only [enc, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .f1,true :: rest,A,b⟩) (by simp [step, hP, termCode])]
    rw [iter_step' P (c' := ⟨emb .complete,rest,A,b⟩) (by simp [step, hP, termCode])]
    cases A with
    | nil =>
      rw [iter_one P (c' := ⟨fail,rest,[],b⟩) (by simp [step, hP, termCode])]
      rfl
    | cons x A =>
      cases x with
      | false =>
        rw [iter_one P (c' := ⟨exit,rest,A,b⟩) (by simp [step, hP, termCode])]
        rfl
      | true =>
        rw [iter_one P (c' := ⟨emb .tok,rest,A,b⟩) (by simp [step, hP, termCode])]
        rfl
  · -- node
    intro cs ih hwf rest A b
    simp only [WellFormed] at hwf
    obtain ⟨hlen,hch⟩ := hwf
    have hne : cs ≠ [] := by
      intro h
      rw [h] at hlen
      simp only [List.length_nil] at hlen
      omega
    have he : termTime d (Raw.node cs) = 1+(1+(((d-1)+1)+(cs.map (termTime d)).sum)) := by
      simp only [termTime]
      omega
    rw [he]
    simp only [enc, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .t1,false :: (cs.flatMap enc ++ rest),A,b⟩)
      (by simp [step, hP, termCode])]
    rw [iter_step' P (c' := ⟨emb (.push (d-1)),cs.flatMap enc ++ rest,A,b⟩)
      (by simp [step, hP, termCode])]
    rw [iter_add, push_chain P d emb exit fail hP]
    have hrep : List.replicate (d-1) true ++ A = List.replicate (cs.length-1) true ++ A := by
      rw [hlen]
    rw [hrep]
    exact ih hne hch rest A b
  · -- nil
    intro h
    exact absurd rfl h
  · -- cons
    intro t ts iht ihts _ hwf rest A b
    have hwt : WellFormed d t := hwf t (by simp)
    have hwts : ∀ c ∈ ts, WellFormed d c := fun c hc => hwf c (by simp [hc])
    cases ts with
    | nil =>
      simp only [List.length_cons, List.length_nil, Nat.sub_self, List.replicate_zero,
        List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      exact iht hwt rest A b
    | cons u us =>
      have hne : (u :: us) ≠ [] := by simp
      have hstack : List.replicate ((t :: u :: us).length-1) true ++ A
          = true :: (List.replicate ((u :: us).length-1) true ++ A) := by
        simp only [List.length_cons, Nat.add_sub_cancel, List.replicate_succ, List.cons_append]
      rw [hstack, List.flatMap_cons, List.map_cons, List.sum_cons, List.append_assoc]
      obtain ⟨b1,hb1⟩ := iht hwt ((u :: us).flatMap enc ++ rest)
        (true :: (List.replicate ((u :: us).length-1) true ++ A)) b
      rw [iter_add, hb1]
      simp only [afterState, List.tail]
      exact ihts hne hwts rest A b1

end TermComponent


/-! ## The term parser as a standalone machine

The component, instantiated with its own state type and a `false` sentinel on
stack A, is a machine that parses one encoded term and halts. -/

inductive TAll
  | s (t : TSt)
  | done
  | fail
  deriving DecidableEq

def termProg (d : Nat) : TAll → Instr TAll
  | .s t => termCode d (fun t' => TAll.s t') .done .fail t
  | .done => .halt
  | .fail => .halt

theorem termProg_run (d : Nat) (hd : 0 < d) (t : Raw) (h : WellFormed d t) (rest b : List Bool) :
    ∃ b', iter (termProg d) (termTime d t) ⟨.s .tok,enc t ++ rest,[false],b⟩
      = ⟨.done,rest,[],b'⟩ := by
  obtain ⟨b',hb⟩ := (term_component (termProg d) d (fun t' => TAll.s t') .done .fail hd
    (fun s => rfl)).1 t h rest [false] b
  exact ⟨b',by simpa only [afterState, List.tail] using hb⟩

/-- Parsing a term is linear in the length of its code, for a fixed arity. -/
theorem termTime_le (d : Nat) : ∀ t : Raw, termTime d t ≤ (d+6)*(enc t).length := by
  refine (rec2 (P := fun t => termTime d t ≤ (d+6)*(enc t).length)
    (Q := fun cs => (cs.map (termTime d)).sum ≤ (d+6)*(cs.flatMap enc).length) ?_ ?_ ?_ ?_ ?_ ?_).1
  · intro i
    have h : 5*(toBits i).length+6 ≤ (d+6)*(2*(toBits i).length+1+2) := by
      have h6 : 6*(2*(toBits i).length+3) ≤ (d+6)*(2*(toBits i).length+1+2) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    simpa only [termTime, enc, List.length_cons, encNat_length] using h
  · have h : 3 ≤ (d+6)*2 := by omega
    simpa only [termTime, enc] using h
  · have h : 3 ≤ (d+6)*2 := by omega
    simpa only [termTime, enc] using h
  · intro cs h
    have hd6 : (d+6)*((cs.flatMap enc).length+1+1)
        = (d+6)*(cs.flatMap enc).length+(d+6)+(d+6) := by ring
    simp only [termTime, enc, List.length_cons]
    omega
  · simp
  · intro t ts ht hts
    have hmul : (d+6)*((enc t).length+(ts.flatMap enc).length)
        = (d+6)*(enc t).length+(d+6)*(ts.flatMap enc).length := by ring
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
    omega


/-! ## Stack shuttling, as reusable components

Any table-driven simulation on this machine has to move bits between the two
stacks: the table is data, not control, so it must be scanned. These are the
two primitives, with exact step counts, stated for any program embedding them.
-/

inductive MSt
  | loop
  | pt
  | pf
  deriving DecidableEq

/-- Pop all of stack A onto stack B (reversing it), then leave for `exit`. -/
def moveABCode {Q : Type} (emb : MSt → Q) (exit : Q) : MSt → Instr Q
  | .loop => .popValA (emb .pt) (emb .pf) exit
  | .pt => .pushB true (emb .loop)
  | .pf => .pushB false (emb .loop)

/-- Pop all of stack B onto stack A (reversing it), then leave for `exit`. -/
def moveBACode {Q : Type} (emb : MSt → Q) (exit : Q) : MSt → Instr Q
  | .loop => .popValB (emb .pt) (emb .pf) exit
  | .pt => .pushA true (emb .loop)
  | .pf => .pushA false (emb .loop)

theorem moveAB_component {Q : Type} (P : Q → Instr Q) (emb : MSt → Q) (exit : Q)
    (hP : ∀ s, P (emb s) = moveABCode emb exit s) (A : List Bool) (inp B : List Bool) :
    iter P (2*A.length+1) ⟨emb .loop,inp,A,B⟩ = ⟨exit,inp,[],A.reverse ++ B⟩ := by
  induction A generalizing B with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append]
    rw [iter_one P (c' := ⟨exit,inp,[],B⟩) (by simp [step, hP, moveABCode])]
  | cons x A ih =>
    have he : 2*(x :: A).length+1 = (2*A.length+1)+1+1 := by
      simp only [List.length_cons]; ring
    rw [he]
    cases x with
    | false =>
      rw [iter_step P (c' := ⟨emb .pf,inp,A,B⟩) (by simp [step, hP, moveABCode])]
      rw [iter_step P (c' := ⟨emb .loop,inp,A,false :: B⟩) (by simp [step, hP, moveABCode])]
      rw [ih]
      simp
    | true =>
      rw [iter_step P (c' := ⟨emb .pt,inp,A,B⟩) (by simp [step, hP, moveABCode])]
      rw [iter_step P (c' := ⟨emb .loop,inp,A,true :: B⟩) (by simp [step, hP, moveABCode])]
      rw [ih]
      simp

theorem moveBA_component {Q : Type} (P : Q → Instr Q) (emb : MSt → Q) (exit : Q)
    (hP : ∀ s, P (emb s) = moveBACode emb exit s) (B : List Bool) (inp A : List Bool) :
    iter P (2*B.length+1) ⟨emb .loop,inp,A,B⟩ = ⟨exit,inp,B.reverse ++ A,[]⟩ := by
  induction B generalizing A with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append]
    rw [iter_one P (c' := ⟨exit,inp,A,[]⟩) (by simp [step, hP, moveBACode])]
  | cons x B ih =>
    have he : 2*(x :: B).length+1 = (2*B.length+1)+1+1 := by
      simp only [List.length_cons]; ring
    rw [he]
    cases x with
    | false =>
      rw [iter_step P (c' := ⟨emb .pf,inp,A,B⟩) (by simp [step, hP, moveBACode])]
      rw [iter_step P (c' := ⟨emb .loop,inp,false :: A,B⟩) (by simp [step, hP, moveBACode])]
      rw [ih]
      simp
    | true =>
      rw [iter_step P (c' := ⟨emb .pt,inp,A,B⟩) (by simp [step, hP, moveBACode])]
      rw [iter_step P (c' := ⟨emb .loop,inp,true :: A,B⟩) (by simp [step, hP, moveBACode])]
      rw [ih]
      simp

/-- Shuttling there and back restores the stack, in `4|A|+2` steps. -/
theorem move_round_trip {Q : Type} (P : Q → Instr Q) (embAB embBA : MSt → Q) (exit : Q)
    (hAB : ∀ s, P (embAB s) = moveABCode embAB (embBA .loop) s)
    (hBA : ∀ s, P (embBA s) = moveBACode embBA exit s) (A inp : List Bool) :
    iter P ((2*A.length+1)+(2*A.length+1)) ⟨embAB .loop,inp,A,[]⟩ = ⟨exit,inp,A,[]⟩ := by
  rw [iter_add, moveAB_component P embAB (embBA .loop) hAB A inp []]
  simp only [List.append_nil]
  have h := moveBA_component P embBA exit hBA A.reverse inp []
  simp only [List.length_reverse] at h
  rw [h]
  simp

/-- A standalone shuttling machine, for execution. -/
inductive ShSt
  | ab (s : MSt)
  | ba (s : MSt)
  | done
  deriving DecidableEq

def shuttleProg : ShSt → Instr ShSt
  | .ab s => moveABCode (fun t => ShSt.ab t) (.ba .loop) s
  | .ba s => moveBACode (fun t => ShSt.ba t) .done s
  | .done => .halt

theorem shuttle_run (A inp : List Bool) :
    iter shuttleProg ((2*A.length+1)+(2*A.length+1)) ⟨.ab .loop,inp,A,[]⟩
      = ⟨.done,inp,A,[]⟩ :=
  move_round_trip shuttleProg (fun t => ShSt.ab t) (fun t => ShSt.ba t) .done
    (fun _ => rfl) (fun _ => rfl) A inp

/-! ## What this establishes

Two stages of the pipeline are now realised on a machine whose every step reads
or moves ONE BIT: the numeral decoder (standalone and as a reusable component)
and the TERM parser, each in time linear in the input it consumes, matching
their counted costs up to a constant factor. The method behind
`MachineTimeBound.PolynomiallyFaithful` is therefore not vacuous: this is what
discharging it looks like, one stage at a time. The remaining stages — the
query parser, the conversion to a typed query, and above all the decision
itself — are not realised here, and until they are, the machine-level claim
`SevenExpTimeTarget.SevenExpTime` is not established.
-/

end NSSE.BitMachine
