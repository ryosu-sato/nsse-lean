import NSSE.RawBitNumeral

/-! # A three-stack bit machine, and table lookup on it

v1638 recorded why the next stage of the machine realisation — running automata
that are BUILT FROM THE INPUT, whose tables are therefore data — is awkward with
two stacks: the index and the table compete for the same stack. This file adds
the model with three stacks, still one bit per step, and proves the primitive
that the two-stack model made painful: skipping to the `k`-th entry of a table.

Three stacks are no stronger than two in principle; they are polynomially
equivalent, and each step here still reads or moves a single bit, so no work is
hidden. The existing two-stack development (v1627–v1637) is left untouched.
-/

namespace NSSE.BitMachine3

structure Config (Q : Type) where
  state : Q
  input : List Bool
  a : List Bool
  b : List Bool
  c : List Bool

inductive Instr (Q : Type)
  | read (onTrue onFalse onEmpty : Q)
  | pushA (bit : Bool) (next : Q)
  | pushB (bit : Bool) (next : Q)
  | pushC (bit : Bool) (next : Q)
  | popA (onTrue onFalse onEmpty : Q)
  | popB (onTrue onFalse onEmpty : Q)
  | popC (onTrue onFalse onEmpty : Q)
  | nop (next : Q)
  | halt

variable {Q : Type}

def step (P : Q → Instr Q) (c : Config Q) : Option (Config Q) :=
  match P c.state with
  | .halt => none
  | .read t f e =>
    match c.input with
    | [] => some ⟨e,[],c.a,c.b,c.c⟩
    | true :: w => some ⟨t,w,c.a,c.b,c.c⟩
    | false :: w => some ⟨f,w,c.a,c.b,c.c⟩
  | .pushA bit next => some ⟨next,c.input,bit :: c.a,c.b,c.c⟩
  | .pushB bit next => some ⟨next,c.input,c.a,bit :: c.b,c.c⟩
  | .pushC bit next => some ⟨next,c.input,c.a,c.b,bit :: c.c⟩
  | .popA t f e =>
    match c.a with
    | [] => some ⟨e,c.input,[],c.b,c.c⟩
    | true :: r => some ⟨t,c.input,r,c.b,c.c⟩
    | false :: r => some ⟨f,c.input,r,c.b,c.c⟩
  | .popB t f e =>
    match c.b with
    | [] => some ⟨e,c.input,c.a,[],c.c⟩
    | true :: r => some ⟨t,c.input,c.a,r,c.c⟩
    | false :: r => some ⟨f,c.input,c.a,r,c.c⟩
  | .popC t f e =>
    match c.c with
    | [] => some ⟨e,c.input,c.a,c.b,[]⟩
    | true :: r => some ⟨t,c.input,c.a,c.b,r⟩
    | false :: r => some ⟨f,c.input,c.a,c.b,r⟩
  | .nop next => some ⟨next,c.input,c.a,c.b,c.c⟩

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
    | none => rw [iter_halt P c h, iter_halt P c h, iter_halt P c h]
    | some c' =>
      have he : m+1+n = (m+n)+1 := by omega
      rw [he, iter_step P h, iter_step P h, ih]

theorem replicate_cons (L : Nat) (x : Bool) (a : List Bool) :
    List.replicate L x ++ x :: a = x :: (List.replicate L x ++ a) := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [List.replicate_succ, List.cons_append, ih]

/-! ## Tables of unary numbers -/

/-- A table: each entry is a unary numeral closed by a separator. -/
def unaryBlocks : List Nat → List Bool
  | [] => []
  | n :: ns => List.replicate n true ++ false :: unaryBlocks ns

theorem unaryBlocks_append (xs ys : List Nat) :
    unaryBlocks (xs ++ ys) = unaryBlocks xs ++ unaryBlocks ys := by
  induction xs with
  | nil => simp [unaryBlocks]
  | cons n xs ih => simp only [List.cons_append, unaryBlocks, ih, List.append_assoc, List.cons_append]

/-! ## The lookup primitive

The index is a unary counter on stack A, closed by a separator; the table is on
stack B; the entries scanned past are moved to stack C, so nothing is lost and
the machine can put the table back afterwards. -/

inductive KSt
  | loop
  | scan
  | pt
  | pf
  deriving DecidableEq

def skipCode {Q : Type} (emb : KSt → Q) (exit fail : Q) : KSt → Instr Q
  | .loop => .popA (emb .scan) exit exit
  | .scan => .popB (emb .pt) (emb .pf) fail
  | .pt => .pushC true (emb .scan)
  | .pf => .pushC false (emb .loop)

section Skip

variable (P : Q → Instr Q) (emb : KSt → Q) (exit fail : Q)
  (hP : ∀ s, P (emb s) = skipCode emb exit fail s)

include hP

theorem scan_block (n : Nat) (inp A rest C : List Bool) :
    iter P (2*n+2) ⟨emb .scan,inp,A,List.replicate n true ++ false :: rest,C⟩
      = ⟨emb .loop,inp,A,rest,false :: (List.replicate n true ++ C)⟩ := by
  induction n generalizing C with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    rw [iter_step P (c' := ⟨emb .pf,inp,A,rest,C⟩) (by simp [step, hP, skipCode])]
    rw [iter_one P (c' := ⟨emb .loop,inp,A,rest,false :: C⟩) (by simp [step, hP, skipCode])]
  | succ n ih =>
    have he : 2*(n+1)+2 = 1+(1+(2*n+2)) := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .pt,inp,A,List.replicate n true ++ false :: rest,C⟩)
      (by simp [step, hP, skipCode])]
    rw [iter_step' P (c' := ⟨emb .scan,inp,A,List.replicate n true ++ false :: rest,true :: C⟩)
      (by simp [step, hP, skipCode])]
    rw [ih, replicate_cons, List.cons_append]

/-- Skipping the first `pre.length` entries of a table: the index is consumed,
the skipped entries are on stack C, and the wanted entry is on top of B. -/
theorem skip_component (pre : List Nat) (inp A post C : List Bool) :
    iter P (3*pre.length+2*pre.sum+1)
        ⟨emb .loop,inp,List.replicate pre.length true ++ false :: A,unaryBlocks pre ++ post,C⟩
      = ⟨exit,inp,A,post,(unaryBlocks pre).reverse ++ C⟩ := by
  induction pre generalizing C with
  | nil =>
    simp only [List.length_nil, List.sum_nil, Nat.mul_zero, Nat.zero_add, List.replicate_zero,
      List.nil_append, unaryBlocks, List.reverse_nil]
    rw [iter_one P (c' := ⟨exit,inp,A,post,C⟩) (by simp [step, hP, skipCode])]
  | cons n pre ih =>
    have he : 3*(n :: pre).length+2*(n :: pre).sum+1 = 1+((2*n+2)+(3*pre.length+2*pre.sum+1)) := by
      simp only [List.length_cons, List.sum_cons]; ring
    rw [he]
    simp only [List.length_cons, List.replicate_succ, List.cons_append, unaryBlocks,
      List.append_assoc]
    rw [iter_step' P
      (c' := ⟨emb .scan,inp,List.replicate pre.length true ++ false :: A,
        List.replicate n true ++ (false :: (unaryBlocks pre ++ post)),C⟩)
      (by simp [step, hP, skipCode])]
    rw [iter_add, scan_block P emb exit fail hP n inp (List.replicate pre.length true ++ false :: A)
      (unaryBlocks pre ++ post) C]
    rw [ih]
    simp only [unaryBlocks, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]

end Skip


/-! ## Moving a stack, and scaling a unary counter

Two more primitives a table-driven simulation needs: putting the scanned part
of a table back, and building the index `k*q + r` from a unary `q`. Both are
components, usable inside any program.
-/

inductive MSt
  | loop
  | pt
  | pf
  deriving DecidableEq

/-- Pop all of stack C onto stack B, reversing it. -/
def moveCBCode {Q : Type} (emb : MSt → Q) (exit : Q) : MSt → Instr Q
  | .loop => .popC (emb .pt) (emb .pf) exit
  | .pt => .pushB true (emb .loop)
  | .pf => .pushB false (emb .loop)

section Move

variable (P : Q → Instr Q) (emb : MSt → Q) (exit : Q)
  (hP : ∀ s, P (emb s) = moveCBCode emb exit s)

include hP

theorem moveCB_component (C : List Bool) (inp A B : List Bool) :
    iter P (2*C.length+1) ⟨emb .loop,inp,A,B,C⟩ = ⟨exit,inp,A,C.reverse ++ B,[]⟩ := by
  induction C generalizing B with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append]
    rw [iter_one P (c' := ⟨exit,inp,A,B,[]⟩) (by simp [step, hP, moveCBCode])]
  | cons x C ih =>
    have he : 2*(x :: C).length+1 = (2*C.length+1)+1+1 := by
      simp only [List.length_cons]; ring
    rw [he]
    cases x with
    | false =>
      rw [iter_step P (c' := ⟨emb .pf,inp,A,B,C⟩) (by simp [step, hP, moveCBCode])]
      rw [iter_step P (c' := ⟨emb .loop,inp,A,false :: B,C⟩) (by simp [step, hP, moveCBCode])]
      rw [ih]
      simp
    | true =>
      rw [iter_step P (c' := ⟨emb .pt,inp,A,B,C⟩) (by simp [step, hP, moveCBCode])]
      rw [iter_step P (c' := ⟨emb .loop,inp,A,true :: B,C⟩) (by simp [step, hP, moveCBCode])]
      rw [ih]
      simp

end Move

/-! ### Scaling a unary counter

`scaleCode k` reads a unary counter on stack A, closed by a separator, and
writes `k` markers on stack B for each one: the index arithmetic a table lookup
needs, done in unary. -/

inductive SSt
  | loop
  | push (j : Nat)
  deriving DecidableEq

def scaleCode (k : Nat) {Q : Type} (emb : SSt → Q) (exit : Q) : SSt → Instr Q
  | .loop => .popA (emb (.push k)) exit exit
  | .push 0 => .nop (emb .loop)
  | .push (j+1) => .pushB true (emb (.push j))

section Scale

variable (P : Q → Instr Q) (k : Nat) (emb : SSt → Q) (exit : Q)
  (hP : ∀ s, P (emb s) = scaleCode k emb exit s)

include hP

theorem scale_push (j : Nat) (inp A B C : List Bool) :
    iter P (j+1) ⟨emb (.push j),inp,A,B,C⟩
      = ⟨emb .loop,inp,A,List.replicate j true ++ B,C⟩ := by
  induction j generalizing B with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rw [iter_one P (c' := ⟨emb .loop,inp,A,B,C⟩) (by simp [step, hP, scaleCode])]
  | succ j ih =>
    rw [show j+1+1 = (j+1)+1 from rfl]
    rw [iter_step P (c' := ⟨emb (.push j),inp,A,true :: B,C⟩) (by simp [step, hP, scaleCode])]
    rw [ih]
    simp only [List.replicate_succ, List.cons_append]
    rw [replicate_cons]

theorem scale_component (m : Nat) (inp A B C : List Bool) :
    iter P (m*(k+2)+1) ⟨emb .loop,inp,List.replicate m true ++ false :: A,B,C⟩
      = ⟨exit,inp,A,List.replicate (m*k) true ++ B,C⟩ := by
  induction m generalizing B with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.zero_mul, Nat.zero_add]
    rw [iter_one P (c' := ⟨exit,inp,A,B,C⟩) (by simp [step, hP, scaleCode])]
  | succ m ih =>
    have he : (m+1)*(k+2)+1 = 1+((k+1)+(m*(k+2)+1)) := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb (.push k),inp,List.replicate m true ++ false :: A,B,C⟩)
      (by simp [step, hP, scaleCode])]
    rw [iter_add, scale_push P k emb exit hP k inp (List.replicate m true ++ false :: A) B C]
    rw [ih]
    have hrep : List.replicate (m*k) true ++ (List.replicate k true ++ B)
        = List.replicate ((m+1)*k) true ++ B := by
      rw [← List.append_assoc, ← List.replicate_add]
      congr 2
      ring
    rw [hrep]

end Scale


/-! ### Moving stack A onto stack C, and scaling from C into A

The simulation loop keeps the current state on stack C between steps, so it
needs the two mirror images of the primitives above. -/

inductive NSt
  | loop
  | pt
  | pf
  deriving DecidableEq

def moveACCode {Q : Type} (emb : NSt → Q) (exit : Q) : NSt → Instr Q
  | .loop => .popA (emb .pt) (emb .pf) exit
  | .pt => .pushC true (emb .loop)
  | .pf => .pushC false (emb .loop)

section MoveAC

variable (P : Q → Instr Q) (emb : NSt → Q) (exit : Q)
  (hP : ∀ s, P (emb s) = moveACCode emb exit s)

include hP

theorem moveAC_component (A : List Bool) (inp B C : List Bool) :
    iter P (2*A.length+1) ⟨emb .loop,inp,A,B,C⟩ = ⟨exit,inp,[],B,A.reverse ++ C⟩ := by
  induction A generalizing C with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append]
    rw [iter_one P (c' := ⟨exit,inp,[],B,C⟩) (by simp [step, hP, moveACCode])]
  | cons x A ih =>
    have he : 2*(x :: A).length+1 = (2*A.length+1)+1+1 := by
      simp only [List.length_cons]; ring
    rw [he]
    cases x with
    | false =>
      rw [iter_step P (c' := ⟨emb .pf,inp,A,B,C⟩) (by simp [step, hP, moveACCode])]
      rw [iter_step P (c' := ⟨emb .loop,inp,A,B,false :: C⟩) (by simp [step, hP, moveACCode])]
      rw [ih]
      simp
    | true =>
      rw [iter_step P (c' := ⟨emb .pt,inp,A,B,C⟩) (by simp [step, hP, moveACCode])]
      rw [iter_step P (c' := ⟨emb .loop,inp,A,B,true :: C⟩) (by simp [step, hP, moveACCode])]
      rw [ih]
      simp

end MoveAC

inductive TSt
  | loop
  | push (j : Nat)
  deriving DecidableEq

/-- Read a unary counter on stack C, closed by a separator, and write `k`
markers on stack A for each one. -/
def scaleCACode (k : Nat) {Q : Type} (emb : TSt → Q) (exit : Q) : TSt → Instr Q
  | .loop => .popC (emb (.push k)) exit exit
  | .push 0 => .nop (emb .loop)
  | .push (j+1) => .pushA true (emb (.push j))

section ScaleCA

variable (P : Q → Instr Q) (k : Nat) (emb : TSt → Q) (exit : Q)
  (hP : ∀ s, P (emb s) = scaleCACode k emb exit s)

include hP

theorem scaleCA_push (j : Nat) (inp A B C : List Bool) :
    iter P (j+1) ⟨emb (.push j),inp,A,B,C⟩
      = ⟨emb .loop,inp,List.replicate j true ++ A,B,C⟩ := by
  induction j generalizing A with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rw [iter_one P (c' := ⟨emb .loop,inp,A,B,C⟩) (by simp [step, hP, scaleCACode])]
  | succ j ih =>
    rw [show j+1+1 = (j+1)+1 from rfl]
    rw [iter_step P (c' := ⟨emb (.push j),inp,true :: A,B,C⟩) (by simp [step, hP, scaleCACode])]
    rw [ih]
    simp only [List.replicate_succ, List.cons_append]
    rw [replicate_cons]

theorem scaleCA_component (m : Nat) (inp A B C : List Bool) :
    iter P (m*(k+2)+1) ⟨emb .loop,inp,A,B,List.replicate m true ++ false :: C⟩
      = ⟨exit,inp,List.replicate (m*k) true ++ A,B,C⟩ := by
  induction m generalizing A with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.zero_mul, Nat.zero_add]
    rw [iter_one P (c' := ⟨exit,inp,A,B,C⟩) (by simp [step, hP, scaleCACode])]
  | succ m ih =>
    have he : (m+1)*(k+2)+1 = 1+((k+1)+(m*(k+2)+1)) := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb (.push k),inp,A,B,List.replicate m true ++ false :: C⟩)
      (by simp [step, hP, scaleCACode])]
    rw [iter_add, scaleCA_push P k emb exit hP k inp A B (List.replicate m true ++ false :: C)]
    rw [ih]
    have hrep : List.replicate (m*k) true ++ (List.replicate k true ++ A)
        = List.replicate ((m+1)*k) true ++ A := by
      rw [← List.append_assoc, ← List.replicate_add]
      congr 2
      ring
    rw [hrep]

end ScaleCA

/-! ### Copying one table entry into the state register

The entry is read off stack B and written twice: to stack A, which becomes the
new state, and to stack C, which keeps the scanned table for restoration. -/

inductive DSt
  | loop
  | pa
  | pc
  | sep
  deriving DecidableEq

def copyCode {Q : Type} (emb : DSt → Q) (exit fail : Q) : DSt → Instr Q
  | .loop => .popB (emb .pa) (emb .sep) fail
  | .pa => .pushA true (emb .pc)
  | .pc => .pushC true (emb .loop)
  | .sep => .pushC false exit

section Copy

variable (P : Q → Instr Q) (emb : DSt → Q) (exit fail : Q)
  (hP : ∀ s, P (emb s) = copyCode emb exit fail s)

include hP

theorem copy_component (n : Nat) (inp A rest C : List Bool) :
    iter P (3*n+2) ⟨emb .loop,inp,A,List.replicate n true ++ false :: rest,C⟩
      = ⟨exit,inp,List.replicate n true ++ A,rest,false :: (List.replicate n true ++ C)⟩ := by
  induction n generalizing A C with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    rw [iter_step P (c' := ⟨emb .sep,inp,A,rest,C⟩) (by simp [step, hP, copyCode])]
    rw [iter_one P (c' := ⟨exit,inp,A,rest,false :: C⟩) (by simp [step, hP, copyCode])]
  | succ n ih =>
    have he : 3*(n+1)+2 = 1+(1+(1+(3*n+2))) := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .pa,inp,A,List.replicate n true ++ false :: rest,C⟩)
      (by simp [step, hP, copyCode])]
    rw [iter_step' P (c' := ⟨emb .pc,inp,true :: A,List.replicate n true ++ false :: rest,C⟩)
      (by simp [step, hP, copyCode])]
    rw [iter_step' P
      (c' := ⟨emb .loop,inp,true :: A,List.replicate n true ++ false :: rest,true :: C⟩)
      (by simp [step, hP, copyCode])]
    rw [ih]
    simp only [List.replicate_succ, List.cons_append]
    rw [replicate_cons, replicate_cons]

end Copy

/-! ## A standalone lookup machine, for execution -/

inductive LSt
  | s (k : KSt)
  | done
  | fail
  deriving DecidableEq

def lookupProg : LSt → Instr LSt
  | .s k => skipCode (fun t => LSt.s t) .done .fail k
  | .done => .halt
  | .fail => .halt

theorem lookup_run (pre : List Nat) (inp A post C : List Bool) :
    iter lookupProg (3*pre.length+2*pre.sum+1)
        ⟨.s .loop,inp,List.replicate pre.length true ++ false :: A,unaryBlocks pre ++ post,C⟩
      = ⟨.done,inp,A,post,(unaryBlocks pre).reverse ++ C⟩ :=
  skip_component lookupProg (fun t => LSt.s t) .done .fail (fun _ => rfl) pre inp A post C


/-! ## The simulation loop

A deterministic automaton over bits, with states `0 … n-1`, is stored as a
table of unary entries: for each state `q`, the entries `3q`, `3q+1`, `3q+2`
are the transition on `0`, the transition on `1`, and the acceptance flag. The
loop below runs it: the state lives on stack C as a unary counter closed by a
separator, the table lives on stack B, and stack A is scratch.

Each round builds the index `3q+b` on A, looks the entry up, copies it into the
state register, puts the table back exactly, and returns the state to C. When
the input runs out the same lookup is done at `3q+2` and the answer is whether
that entry is nonzero.
-/

inductive SimSt
  | sepA
  | sc (x : TSt)
  | bit
  | one
  | sk (x : KSt)
  | cp (x : DSt)
  | rb (x : MSt)
  | sepC
  | ac (x : NSt)
  | accA
  | accB
  | fk (x : KSt)
  | test
  | yes
  | no
  | fail
  deriving DecidableEq

def simProg : SimSt → Instr SimSt
  | .sepA => .pushA false (.sc .loop)
  | .sc x => scaleCACode 3 (fun t => SimSt.sc t) .bit x
  | .bit => .read .one (.sk .loop) .accA
  | .one => .pushA true (.sk .loop)
  | .sk x => skipCode (fun t => SimSt.sk t) (.cp .loop) .fail x
  | .cp x => copyCode (fun t => SimSt.cp t) (.rb .loop) .fail x
  | .rb x => moveCBCode (fun t => SimSt.rb t) .sepC x
  | .sepC => .pushC false (.ac .loop)
  | .ac x => moveACCode (fun t => SimSt.ac t) .sepA x
  | .accA => .pushA true .accB
  | .accB => .pushA true (.fk .loop)
  | .fk x => skipCode (fun t => SimSt.fk t) .test .fail x
  | .test => .popB .yes .no .fail
  | .yes => .halt
  | .no => .halt
  | .fail => .halt

/-- The cost of one round: the pieces, summed. -/
def stepTime (pre : List Nat) (e q : Nat) (b : Bool) : Nat :=
  1+(q*5+1)+1+(if b then 1 else 0)+(3*pre.length+2*pre.sum+1)+(3*e+2)
    +(2*(1+e+(unaryBlocks pre).length)+1)+1+(2*e+1)

theorem sim_step (pre : List Nat) (e : Nat) (rest : List Nat) (q : Nat) (b : Bool)
    (w : List Bool) (hlen : pre.length = 3*q+(if b then 1 else 0)) :
    iter simProg (stepTime pre e q b)
        ⟨.sepA,b :: w,[],unaryBlocks (pre ++ e :: rest),List.replicate q true ++ [false]⟩
      = ⟨.sepA,w,[],unaryBlocks (pre ++ e :: rest),List.replicate e true ++ [false]⟩ := by
  have htab : unaryBlocks (pre ++ e :: rest)
      = unaryBlocks pre ++ (List.replicate e true ++ false :: unaryBlocks rest) := by
    rw [unaryBlocks_append]
    rfl
  unfold stepTime
  rw [show 1+(q*5+1)+1+(if b then 1 else 0)+(3*pre.length+2*pre.sum+1)+(3*e+2)
      +(2*(1+e+(unaryBlocks pre).length)+1)+1+(2*e+1)
      = 1+((q*5+1)+(1+((if b then 1 else 0)+((3*pre.length+2*pre.sum+1)+((3*e+2)
        +((2*(1+e+(unaryBlocks pre).length)+1)+(1+(2*e+1)))))))) from by ring]
  -- push the index separator
  rw [iter_step' simProg (c' := ⟨.sc .loop,b :: w,[false],unaryBlocks (pre ++ e :: rest),
    List.replicate q true ++ [false]⟩) rfl]
  -- build 3q on stack A
  rw [iter_add, scaleCA_component simProg 3 (fun t => SimSt.sc t) .bit (fun _ => rfl) q
    (b :: w) [false] (unaryBlocks (pre ++ e :: rest)) []]
  -- read the input bit
  cases b with
  | false =>
    rw [show (if (false : Bool) then 1 else 0) = 0 from rfl, Nat.zero_add]
    rw [iter_step' simProg (c' := ⟨.sk .loop,w,List.replicate (q*3) true ++ [false],
      unaryBlocks (pre ++ e :: rest),[]⟩) rfl]
    have hq : pre.length = q*3 := by
      have hif : (if (false : Bool) then 1 else 0) = 0 := rfl
      omega
    rw [← hq, htab, iter_add,
      skip_component simProg (fun t => SimSt.sk t) (.cp .loop) .fail (fun _ => rfl) pre w []
        (List.replicate e true ++ false :: unaryBlocks rest) []]
    simp only [List.append_nil]
    rw [iter_add, copy_component simProg (fun t => SimSt.cp t) (.rb .loop) .fail (fun _ => rfl)
      e w [] (unaryBlocks rest) ((unaryBlocks pre).reverse)]
    simp only [List.append_nil]
    rw [show 2*(1+e+(unaryBlocks pre).length)+1
      = 2*(false :: (List.replicate e true ++ (unaryBlocks pre).reverse)).length+1 from by
        simp; omega]
    rw [iter_add, moveCB_component simProg (fun t => SimSt.rb t) .sepC (fun _ => rfl)
      (false :: (List.replicate e true ++ (unaryBlocks pre).reverse)) w
      (List.replicate e true) (unaryBlocks rest)]
    rw [show 1+(2*e+1) = 1+(2*(List.replicate e true).length+1) from by simp]
    rw [iter_step' simProg (c' := ⟨.ac .loop,w,List.replicate e true,
      ((false :: (List.replicate e true ++ (unaryBlocks pre).reverse)).reverse
        ++ unaryBlocks rest),[false]⟩) rfl]
    rw [moveAC_component simProg (fun t => SimSt.ac t) .sepA (fun _ => rfl)
      (List.replicate e true) w
      ((false :: (List.replicate e true ++ (unaryBlocks pre).reverse)).reverse
        ++ unaryBlocks rest) [false]]
    simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.reverse_reverse, List.append_assoc, List.singleton_append, htab]
  | true =>
    rw [show (if (true : Bool) then 1 else 0) = 1 from rfl]
    rw [iter_step' simProg (c' := ⟨.one,w,List.replicate (q*3) true ++ [false],
      unaryBlocks (pre ++ e :: rest),[]⟩) rfl]
    rw [iter_step' simProg (c' := ⟨.sk .loop,w,true :: (List.replicate (q*3) true ++ [false]),
      unaryBlocks (pre ++ e :: rest),[]⟩) rfl]
    have hq : pre.length = q*3+1 := by
      have hif : (if (true : Bool) then 1 else 0) = 1 := rfl
      omega
    have hstack : true :: (List.replicate (q*3) true ++ [false])
        = List.replicate pre.length true ++ false :: [] := by
      rw [hq, List.replicate_succ, List.cons_append]
    rw [hstack, htab, iter_add,
      skip_component simProg (fun t => SimSt.sk t) (.cp .loop) .fail (fun _ => rfl) pre w []
        (List.replicate e true ++ false :: unaryBlocks rest) []]
    simp only [List.append_nil]
    rw [iter_add, copy_component simProg (fun t => SimSt.cp t) (.rb .loop) .fail (fun _ => rfl)
      e w [] (unaryBlocks rest) ((unaryBlocks pre).reverse)]
    simp only [List.append_nil]
    rw [show 2*(1+e+(unaryBlocks pre).length)+1
      = 2*(false :: (List.replicate e true ++ (unaryBlocks pre).reverse)).length+1 from by
        simp; omega]
    rw [iter_add, moveCB_component simProg (fun t => SimSt.rb t) .sepC (fun _ => rfl)
      (false :: (List.replicate e true ++ (unaryBlocks pre).reverse)) w
      (List.replicate e true) (unaryBlocks rest)]
    rw [show 1+(2*e+1) = 1+(2*(List.replicate e true).length+1) from by simp]
    rw [iter_step' simProg (c' := ⟨.ac .loop,w,List.replicate e true,
      ((false :: (List.replicate e true ++ (unaryBlocks pre).reverse)).reverse
        ++ unaryBlocks rest),[false]⟩) rfl]
    rw [moveAC_component simProg (fun t => SimSt.ac t) .sepA (fun _ => rfl)
      (List.replicate e true) w
      ((false :: (List.replicate e true ++ (unaryBlocks pre).reverse)).reverse
        ++ unaryBlocks rest) [false]]
    simp only [List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.reverse_reverse, List.append_assoc, List.singleton_append, htab]


/-! ### The whole run, and the acceptance test -/

/-- The automaton the table encodes: three entries per state, the transitions
on `0` and `1` and the acceptance flag. -/
def stepT (table : List Nat) (q : Nat) (b : Bool) : Nat :=
  table.getD (3*q+(if b then 1 else 0)) 0

def runT (table : List Nat) (q : Nat) : List Bool → Nat
  | [] => q
  | b :: w => runT table (stepT table q b) w

def acceptT (table : List Nat) (q : Nat) : Bool := table.getD (3*q+2) 0 ≠ 0

/-- Entries are state indices, and every state has its three entries. -/
def ValidTable (table : List Nat) : Prop :=
  ∀ i, i < table.length → 3*(table.getD i 0)+2 < table.length

theorem split_table (table : List Nat) (i : Nat) (h : i < table.length) :
    table = table.take i ++ table.getD i 0 :: table.drop (i+1)
      ∧ (table.take i).length = i := by
  constructor
  · conv_lhs => rw [← List.take_append_drop i table]
    congr 1
    rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem table 0 h]
  · simp [Nat.min_eq_left h.le]

def runTime (table : List Nat) (q : Nat) : List Bool → Nat
  | [] => 0
  | b :: w =>
    stepTime (table.take (3*q+(if b then 1 else 0))) (stepT table q b) q b
      + runTime table (stepT table q b) w

theorem sim_run (table : List Nat) (hv : ValidTable table) :
    ∀ (w : List Bool) (q : Nat), 3*q+2 < table.length →
      iter simProg (runTime table q w)
          ⟨.sepA,w,[],unaryBlocks table,List.replicate q true ++ [false]⟩
        = ⟨.sepA,[],[],unaryBlocks table,List.replicate (runT table q w) true ++ [false]⟩ := by
  intro w
  induction w with
  | nil => intro q _; simp [runTime, runT, iter]
  | cons b w ih =>
    intro q hq
    have hi : 3*q+(if b then 1 else 0) < table.length := by
      cases b <;> simp <;> omega
    obtain ⟨hsplit,hlen⟩ := split_table table (3*q+(if b then 1 else 0)) hi
    have hstep : stepT table q b = table.getD (3*q+(if b then 1 else 0)) 0 := rfl
    have hnext : 3*(stepT table q b)+2 < table.length := by
      rw [hstep]; exact hv _ hi
    simp only [runTime, runT]
    rw [iter_add]
    rw [show unaryBlocks table
        = unaryBlocks (table.take (3*q+(if b then 1 else 0))
            ++ stepT table q b :: table.drop (3*q+(if b then 1 else 0)+1)) from by
      rw [hstep, ← hsplit]]
    rw [sim_step (table.take (3*q+(if b then 1 else 0))) (stepT table q b)
      (table.drop (3*q+(if b then 1 else 0)+1)) q b w (by rw [hlen])]
    rw [show unaryBlocks (table.take (3*q+(if b then 1 else 0))
            ++ stepT table q b :: table.drop (3*q+(if b then 1 else 0)+1))
        = unaryBlocks table from by rw [hstep, ← hsplit]]
    exact ih (stepT table q b) hnext

/-- The acceptance test: the same lookup at index `3q+2`. -/
def acceptTime (pre : List Nat) (q : Nat) : Nat :=
  1+(q*5+1)+1+1+1+(3*pre.length+2*pre.sum+1)+1

theorem sim_accept (pre : List Nat) (a : Nat) (rest : List Nat) (q : Nat)
    (hlen : pre.length = 3*q+2) :
    (iter simProg (acceptTime pre q)
        ⟨.sepA,[],[],unaryBlocks (pre ++ a :: rest),List.replicate q true ++ [false]⟩).state
      = if a = 0 then SimSt.no else SimSt.yes := by
  have htab : unaryBlocks (pre ++ a :: rest)
      = unaryBlocks pre ++ (List.replicate a true ++ false :: unaryBlocks rest) := by
    rw [unaryBlocks_append]; rfl
  unfold acceptTime
  rw [show 1+(q*5+1)+1+1+1+(3*pre.length+2*pre.sum+1)+1
      = 1+((q*5+1)+(1+(1+(1+((3*pre.length+2*pre.sum+1)+1))))) from by ring]
  rw [iter_step' simProg (c' := ⟨.sc .loop,[],[false],unaryBlocks (pre ++ a :: rest),
    List.replicate q true ++ [false]⟩) rfl]
  rw [iter_add, scaleCA_component simProg 3 (fun t => SimSt.sc t) .bit (fun _ => rfl) q
    [] [false] (unaryBlocks (pre ++ a :: rest)) []]
  rw [iter_step' simProg (c' := ⟨.accA,[],List.replicate (q*3) true ++ [false],
    unaryBlocks (pre ++ a :: rest),[]⟩) rfl]
  rw [iter_step' simProg (c' := ⟨.accB,[],true :: (List.replicate (q*3) true ++ [false]),
    unaryBlocks (pre ++ a :: rest),[]⟩) rfl]
  rw [iter_step' simProg (c' := ⟨.fk .loop,[],
    true :: (true :: (List.replicate (q*3) true ++ [false])),
    unaryBlocks (pre ++ a :: rest),[]⟩) rfl]
  have hstack : true :: (true :: (List.replicate (q*3) true ++ [false]))
      = List.replicate pre.length true ++ false :: [] := by
    rw [hlen, show 3*q+2 = (q*3+1)+1 from by ring, List.replicate_succ, List.cons_append,
      List.replicate_succ, List.cons_append]
  rw [hstack, htab, iter_add,
    skip_component simProg (fun t => SimSt.fk t) .test .fail (fun _ => rfl) pre [] []
      (List.replicate a true ++ false :: unaryBlocks rest) []]
  cases a with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, if_pos]
    rw [iter_one simProg (c' := ⟨.no,[],[],unaryBlocks rest,(unaryBlocks pre).reverse ++ []⟩) rfl]
  | succ n =>
    simp only [List.replicate_succ, List.cons_append]
    rw [iter_one simProg (c' := ⟨.yes,[],[],List.replicate n true ++ false :: unaryBlocks rest,
      (unaryBlocks pre).reverse ++ []⟩) rfl]
    simp


/-! ## Loading a table from the input tape

The simulator above runs a table that is already on a stack. For the machine to
run an automaton GIVEN TO IT, the table has to be read off the input. The code
is the number of entries in unary, a separator, then the entries:

    encTable table = replicate |table| true ++ false :: unaryBlocks table

which is unambiguous (the count says how many separators to expect).
-/

def encTable (table : List Nat) : List Bool :=
  List.replicate table.length true ++ false :: unaryBlocks table

inductive LdSt
  | cnt
  | mark
  | ent
  | bits
  | pt
  | pf
  | mv (m : MSt)
  deriving DecidableEq

def loadCode {Q : Type} (emb : LdSt → Q) (exit fail : Q) : LdSt → Instr Q
  | .cnt => .read (emb .mark) (emb .ent) fail
  | .mark => .pushA true (emb .cnt)
  | .ent => .popA (emb .bits) (emb (.mv .loop)) (emb (.mv .loop))
  | .bits => .read (emb .pt) (emb .pf) fail
  | .pt => .pushC true (emb .bits)
  | .pf => .pushC false (emb .ent)
  | .mv m => moveCBCode (fun t => emb (.mv t)) exit m

section Load

variable (P : Q → Instr Q) (emb : LdSt → Q) (exit fail : Q)
  (hP : ∀ s, P (emb s) = loadCode emb exit fail s)

include hP

theorem load_count (k : Nat) (w A B C : List Bool) :
    iter P (2*k+1) ⟨emb .cnt,List.replicate k true ++ false :: w,A,B,C⟩
      = ⟨emb .ent,w,List.replicate k true ++ A,B,C⟩ := by
  induction k generalizing A with
  | zero =>
    simp only [List.replicate_zero, List.nil_append]
    rw [iter_one P (c' := ⟨emb .ent,w,A,B,C⟩) (by simp [step, hP, loadCode])]
  | succ k ih =>
    have he : 2*(k+1)+1 = (2*k+1)+1+1 := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step P (c' := ⟨emb .mark,List.replicate k true ++ false :: w,A,B,C⟩)
      (by simp [step, hP, loadCode])]
    rw [iter_step P (c' := ⟨emb .cnt,List.replicate k true ++ false :: w,true :: A,B,C⟩)
      (by simp [step, hP, loadCode])]
    rw [ih, replicate_cons, List.cons_append]

theorem load_entry (n : Nat) (w A B C : List Bool) :
    iter P (2*n+2) ⟨emb .bits,List.replicate n true ++ false :: w,A,B,C⟩
      = ⟨emb .ent,w,A,B,false :: (List.replicate n true ++ C)⟩ := by
  induction n generalizing C with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    rw [iter_step P (c' := ⟨emb .pf,w,A,B,C⟩) (by simp [step, hP, loadCode])]
    rw [iter_one P (c' := ⟨emb .ent,w,A,B,false :: C⟩) (by simp [step, hP, loadCode])]
  | succ n ih =>
    have he : 2*(n+1)+2 = 1+(1+(2*n+2)) := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .pt,List.replicate n true ++ false :: w,A,B,C⟩)
      (by simp [step, hP, loadCode])]
    rw [iter_step' P (c' := ⟨emb .bits,List.replicate n true ++ false :: w,A,B,true :: C⟩)
      (by simp [step, hP, loadCode])]
    rw [ih, replicate_cons, List.cons_append]

def entriesTime (table : List Nat) : Nat := (table.map (fun n => 2*n+3)).sum

theorem load_entries (table : List Nat) (w A B C : List Bool) :
    iter P (entriesTime table)
        ⟨emb .ent,unaryBlocks table ++ w,List.replicate table.length true ++ A,B,C⟩
      = ⟨emb .ent,w,A,B,(unaryBlocks table).reverse ++ C⟩ := by
  induction table generalizing C with
  | nil => simp [entriesTime, unaryBlocks, iter]
  | cons n table ih =>
    have he : entriesTime (n :: table) = 1+((2*n+2)+entriesTime table) := by
      simp only [entriesTime, List.map_cons, List.sum_cons]; ring
    rw [he]
    simp only [List.length_cons, List.replicate_succ, List.cons_append, unaryBlocks,
      List.append_assoc]
    rw [iter_step' P (c' := ⟨emb .bits,List.replicate n true ++ (false :: (unaryBlocks table ++ w)),
      List.replicate table.length true ++ A,B,C⟩) (by simp [step, hP, loadCode])]
    rw [iter_add, load_entry P emb exit fail hP n (unaryBlocks table ++ w)
      (List.replicate table.length true ++ A) B C]
    rw [ih]
    simp only [unaryBlocks, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]

def loadTime (table : List Nat) : Nat :=
  (2*table.length+1)+entriesTime table+1+(2*(unaryBlocks table).length+1)

theorem load_component (table : List Nat) (w : List Bool) :
    iter P (loadTime table) ⟨emb .cnt,encTable table ++ w,[],[],[]⟩
      = ⟨exit,w,[],unaryBlocks table,[]⟩ := by
  unfold loadTime
  rw [show (2*table.length+1)+entriesTime table+1+(2*(unaryBlocks table).length+1)
      = (2*table.length+1)+(entriesTime table+(1+(2*(unaryBlocks table).length+1))) from by ring]
  simp only [encTable, List.append_assoc, List.cons_append]
  rw [iter_add, load_count P emb exit fail hP table.length (unaryBlocks table ++ w) [] [] []]
  rw [iter_add, load_entries P emb exit fail hP table (w) [] [] []]
  rw [iter_step' P (c' := ⟨emb (.mv .loop),w,[],[],(unaryBlocks table).reverse ++ []⟩)
    (by simp [step, hP, loadCode])]
  simp only [List.append_nil]
  rw [show 2*(unaryBlocks table).length+1 = 2*((unaryBlocks table).reverse).length+1 from by simp]
  rw [moveCB_component P (fun t => emb (.mv t)) exit (fun s => by rw [hP (.mv s)]; rfl)
    ((unaryBlocks table).reverse) w [] []]
  simp

end Load


/-! ## Transporting a program along an embedding

A finished program becomes a component of a bigger one by renaming its states.
Since every instruction only mentions successor states, renaming commutes with
the step function, so runs transport verbatim. -/

def Instr.map {Q Q' : Type} (f : Q → Q') : Instr Q → Instr Q'
  | .read t fa e => .read (f t) (f fa) (f e)
  | .pushA b n => .pushA b (f n)
  | .pushB b n => .pushB b (f n)
  | .pushC b n => .pushC b (f n)
  | .popA t fa e => .popA (f t) (f fa) (f e)
  | .popB t fa e => .popB (f t) (f fa) (f e)
  | .popC t fa e => .popC (f t) (f fa) (f e)
  | .nop n => .nop (f n)
  | .halt => .halt

def mapConfig {Q Q' : Type} (f : Q → Q') (c : Config Q) : Config Q' :=
  ⟨f c.state,c.input,c.a,c.b,c.c⟩

theorem step_map {Q Q' : Type} (P : Q → Instr Q) (P' : Q' → Instr Q') (f : Q → Q')
    (h : ∀ q, P' (f q) = Instr.map f (P q)) (c : Config Q) :
    step P' (mapConfig f c) = (step P c).map (mapConfig f) := by
  simp only [step, mapConfig, h]
  cases P c.state with
  | read t fa e => cases c.input with
    | nil => rfl
    | cons x w => cases x <;> rfl
  | pushA b n => rfl
  | pushB b n => rfl
  | pushC b n => rfl
  | popA t fa e => cases c.a with
    | nil => rfl
    | cons x r => cases x <;> rfl
  | popB t fa e => cases c.b with
    | nil => rfl
    | cons x r => cases x <;> rfl
  | popC t fa e => cases c.c with
    | nil => rfl
    | cons x r => cases x <;> rfl
  | nop n => rfl
  | halt => rfl

theorem iter_map {Q Q' : Type} (P : Q → Instr Q) (P' : Q' → Instr Q') (f : Q → Q')
    (h : ∀ q, P' (f q) = Instr.map f (P q)) (n : Nat) (c : Config Q) :
    iter P' n (mapConfig f c) = mapConfig f (iter P n c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    have hs := step_map P P' f h c
    cases hc : step P c with
    | none =>
      rw [hc] at hs
      rw [iter_halt P' _ hs, iter_halt P c hc]
    | some c' =>
      rw [hc] at hs
      rw [iter_step P' hs, iter_step P hc, ih]

/-! ## A universal automaton machine

Read an automaton and a word from the input, run the automaton on the word, and
answer. This is the shape the cap decision needs: the automaton is part of the
input, not of the control. -/

inductive UnivSt
  | ld (x : LdSt)
  | sep
  | sim (x : SimSt)
  deriving DecidableEq

def univProg : UnivSt → Instr UnivSt
  | .ld x => loadCode (fun t => UnivSt.ld t) .sep (.sim .fail) x
  | .sep => .pushC false (.sim .sepA)
  | .sim x => Instr.map (fun t => UnivSt.sim t) (simProg x)

theorem runT_valid (table : List Nat) (hv : ValidTable table) :
    ∀ (w : List Bool) (q : Nat), 3*q+2 < table.length → 3*(runT table q w)+2 < table.length := by
  intro w
  induction w with
  | nil => intro q h; exact h
  | cons b w ih =>
    intro q h
    refine ih (stepT table q b) ?_
    have hi : 3*q+(if b then 1 else 0) < table.length := by cases b <;> simp <;> omega
    exact hv _ hi

def univTime (table : List Nat) (w : List Bool) : Nat :=
  loadTime table+1+runTime table 0 w
    +acceptTime (table.take (3*(runT table 0 w)+2)) (runT table 0 w)

/-- The machine reads the automaton and the word from its input and answers
acceptance. -/
theorem univ_run (table : List Nat) (hv : ValidTable table) (h0 : 3*0+2 < table.length)
    (w : List Bool) :
    (iter univProg (univTime table w) ⟨.ld .cnt,encTable table ++ w,[],[],[]⟩).state
      = if acceptT table (runT table 0 w) then UnivSt.sim .yes else UnivSt.sim .no := by
  have hq := runT_valid table hv w 0 h0
  obtain ⟨hsplit,hlen⟩ := split_table table (3*(runT table 0 w)+2) hq
  unfold univTime
  rw [show loadTime table+1+runTime table 0 w
      +acceptTime (table.take (3*(runT table 0 w)+2)) (runT table 0 w)
      = loadTime table+(1+(runTime table 0 w
        +acceptTime (table.take (3*(runT table 0 w)+2)) (runT table 0 w))) from by ring]
  rw [iter_add, load_component univProg (fun t => UnivSt.ld t) .sep (.sim .fail)
    (fun _ => rfl) table w]
  rw [iter_step' univProg (c' := ⟨.sim .sepA,w,[],unaryBlocks table,[false]⟩) rfl]
  rw [iter_add]
  have hmap : ∀ q, univProg ((fun t => UnivSt.sim t) q) = Instr.map (fun t => UnivSt.sim t) (simProg q) :=
    fun _ => rfl
  have hrun : iter univProg (runTime table 0 w)
      ⟨.sim .sepA,w,[],unaryBlocks table,[false]⟩
      = mapConfig (fun t => UnivSt.sim t)
        ⟨.sepA,[],[],unaryBlocks table,List.replicate (runT table 0 w) true ++ [false]⟩ := by
    have h := iter_map simProg univProg (fun t => UnivSt.sim t) hmap (runTime table 0 w)
      ⟨.sepA,w,[],unaryBlocks table,[false]⟩
    have h0' : (⟨.sepA,w,[],unaryBlocks table,[false]⟩ : Config SimSt)
        = ⟨.sepA,w,[],unaryBlocks table,List.replicate 0 true ++ [false]⟩ := rfl
    rw [h0'] at h
    rw [show (⟨.sim .sepA,w,[],unaryBlocks table,[false]⟩ : Config UnivSt)
        = mapConfig (fun t => UnivSt.sim t)
          ⟨.sepA,w,[],unaryBlocks table,List.replicate 0 true ++ [false]⟩ from rfl]
    rw [h, sim_run table hv w 0 h0]
  rw [hrun]
  have hacc := sim_accept (table.take (3*(runT table 0 w)+2))
    (table.getD (3*(runT table 0 w)+2) 0) (table.drop (3*(runT table 0 w)+2+1))
    (runT table 0 w) hlen
  have hmapacc := iter_map simProg univProg (fun t => UnivSt.sim t) hmap
    (acceptTime (table.take (3*(runT table 0 w)+2)) (runT table 0 w))
    ⟨.sepA,[],[],unaryBlocks table,List.replicate (runT table 0 w) true ++ [false]⟩
  rw [hmapacc]
  simp only [mapConfig]
  rw [show unaryBlocks table
      = unaryBlocks (table.take (3*(runT table 0 w)+2)
        ++ table.getD (3*(runT table 0 w)+2) 0 :: table.drop (3*(runT table 0 w)+2+1)) from by
    rw [← hsplit]]
  rw [hacc]
  have hdef : acceptT table (runT table 0 w)
      = decide (table.getD (3*(runT table 0 w)+2) 0 ≠ 0) := rfl
  by_cases h : table.getD (3*(runT table 0 w)+2) 0 = 0
  · rw [if_pos h, hdef, decide_eq_false (not_not_intro h)]
    rfl
  · rw [if_neg h, hdef, decide_eq_true h]
    rfl


/-! ## Rewriting a table: complementing the acceptance flags

The decision's front end builds automata from others: complement, product,
reachability. The simplest of those on this machine is complementation, which
rewrites every third entry. It is the first piece of table CONSTRUCTION, as
opposed to table reading.

A table with flags is a list of triples — the two transitions and an acceptance
bit — flattened into the entry list the simulator expects. -/

def flagTable (ts : List (Nat × Nat × Bool)) : List Nat :=
  ts.flatMap (fun t => [t.1,t.2.1,if t.2.2 then 1 else 0])

def complementFlags (ts : List (Nat × Nat × Bool)) : List (Nat × Nat × Bool) :=
  ts.map (fun t => (t.1,t.2.1,!t.2.2))

inductive CmSt
  | c0
  | p0
  | s0
  | c1
  | p1
  | s1
  | c2
  | t2
  | z2
  | w0
  | w1
  | fin (m : MSt)
  deriving DecidableEq

def complCode {Q : Type} (emb : CmSt → Q) (exit fail : Q) : CmSt → Instr Q
  | .c0 => .popB (emb .p0) (emb .s0) (emb (.fin .loop))
  | .p0 => .pushC true (emb .c0)
  | .s0 => .pushC false (emb .c1)
  | .c1 => .popB (emb .p1) (emb .s1) fail
  | .p1 => .pushC true (emb .c1)
  | .s1 => .pushC false (emb .c2)
  | .c2 => .popB (emb .t2) (emb .z2) fail
  | .t2 => .popB fail (emb .w0) fail
  | .z2 => .pushC true (emb .w1)
  | .w0 => .pushC false (emb .c0)
  | .w1 => .pushC false (emb .c0)
  | .fin m => moveCBCode (fun t => emb (.fin t)) exit m

section Compl

variable (P : Q → Instr Q) (emb : CmSt → Q) (exit fail : Q)
  (hP : ∀ s, P (emb s) = complCode emb exit fail s)

include hP

theorem compl_copy0 (n : Nat) (inp A rest C : List Bool) :
    iter P (2*n+2) ⟨emb .c0,inp,A,List.replicate n true ++ false :: rest,C⟩
      = ⟨emb .c1,inp,A,rest,false :: (List.replicate n true ++ C)⟩ := by
  induction n generalizing C with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    rw [iter_step P (c' := ⟨emb .s0,inp,A,rest,C⟩) (by simp [step, hP, complCode])]
    rw [iter_one P (c' := ⟨emb .c1,inp,A,rest,false :: C⟩) (by simp [step, hP, complCode])]
  | succ n ih =>
    have he : 2*(n+1)+2 = 1+(1+(2*n+2)) := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .p0,inp,A,List.replicate n true ++ false :: rest,C⟩)
      (by simp [step, hP, complCode])]
    rw [iter_step' P (c' := ⟨emb .c0,inp,A,List.replicate n true ++ false :: rest,true :: C⟩)
      (by simp [step, hP, complCode])]
    rw [ih, replicate_cons, List.cons_append]

theorem compl_copy1 (n : Nat) (inp A rest C : List Bool) :
    iter P (2*n+2) ⟨emb .c1,inp,A,List.replicate n true ++ false :: rest,C⟩
      = ⟨emb .c2,inp,A,rest,false :: (List.replicate n true ++ C)⟩ := by
  induction n generalizing C with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    rw [iter_step P (c' := ⟨emb .s1,inp,A,rest,C⟩) (by simp [step, hP, complCode])]
    rw [iter_one P (c' := ⟨emb .c2,inp,A,rest,false :: C⟩) (by simp [step, hP, complCode])]
  | succ n ih =>
    have he : 2*(n+1)+2 = 1+(1+(2*n+2)) := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .p1,inp,A,List.replicate n true ++ false :: rest,C⟩)
      (by simp [step, hP, complCode])]
    rw [iter_step' P (c' := ⟨emb .c1,inp,A,List.replicate n true ++ false :: rest,true :: C⟩)
      (by simp [step, hP, complCode])]
    rw [ih, replicate_cons, List.cons_append]

theorem compl_flag (b : Bool) (inp A rest C : List Bool) :
    iter P 3
        ⟨emb .c2,inp,A,unaryBlocks [if b then 1 else 0] ++ rest,C⟩
      = ⟨emb .c0,inp,A,rest,
          false :: (List.replicate (if b then 0 else 1) true ++ C)⟩ := by
  cases b with
  | false =>
    show iter P (1+(1+1)) _ = _
    simp only [if_false, unaryBlocks, List.replicate_zero, List.nil_append, List.cons_append,
      List.append_assoc]
    rw [iter_step' P (c' := ⟨emb .z2,inp,A,unaryBlocks [] ++ rest,C⟩)
      (by simp [step, hP, complCode, unaryBlocks])]
    rw [iter_step' P (c' := ⟨emb .w1,inp,A,unaryBlocks [] ++ rest,true :: C⟩)
      (by simp [step, hP, complCode])]
    rw [iter_one P (c' := ⟨emb .c0,inp,A,unaryBlocks [] ++ rest,false :: (true :: C)⟩)
      (by simp [step, hP, complCode])]
    simp [unaryBlocks]
  | true =>
    show iter P (1+(1+1)) _ = _
    simp only [if_true, unaryBlocks, List.replicate_one, List.cons_append, List.nil_append,
      List.append_assoc]
    rw [iter_step' P (c' := ⟨emb .t2,inp,A,false :: (unaryBlocks [] ++ rest),C⟩)
      (by simp [step, hP, complCode, unaryBlocks])]
    rw [iter_step' P (c' := ⟨emb .w0,inp,A,unaryBlocks [] ++ rest,C⟩)
      (by simp [step, hP, complCode])]
    rw [iter_one P (c' := ⟨emb .c0,inp,A,unaryBlocks [] ++ rest,false :: C⟩)
      (by simp [step, hP, complCode])]
    simp [unaryBlocks]

def passTime (ts : List (Nat × Nat × Bool)) : Nat :=
  (ts.map (fun t => (2*t.1+2)+((2*t.2.1+2)+3))).sum

theorem compl_pass (ts : List (Nat × Nat × Bool)) (inp A rest C : List Bool) :
    iter P (passTime ts) ⟨emb .c0,inp,A,unaryBlocks (flagTable ts) ++ rest,C⟩
      = ⟨emb .c0,inp,A,rest,(unaryBlocks (flagTable (complementFlags ts))).reverse ++ C⟩ := by
  induction ts generalizing C with
  | nil => simp [passTime, flagTable, complementFlags, unaryBlocks, iter]
  | cons t ts ih =>
    obtain ⟨n0,n1,b⟩ := t
    have hflat : flagTable ((n0,n1,b) :: ts)
        = n0 :: n1 :: (if b then 1 else 0) :: flagTable ts := by
      simp [flagTable]
    have htime : passTime ((n0,n1,b) :: ts)
        = (2*n0+2)+((2*n1+2)+(3+passTime ts)) := by
      simp only [passTime, List.map_cons, List.sum_cons]
      ring
    rw [hflat, htime]
    simp only [unaryBlocks, List.append_assoc, List.cons_append]
    rw [iter_add, compl_copy0 P emb exit fail hP n0 inp A
      (List.replicate n1 true ++ (false :: (List.replicate (if b then 1 else 0) true
        ++ (false :: (unaryBlocks (flagTable ts) ++ rest))))) C]
    rw [iter_add, compl_copy1 P emb exit fail hP n1 inp A
      (List.replicate (if b then 1 else 0) true ++ (false :: (unaryBlocks (flagTable ts) ++ rest)))
      (false :: (List.replicate n0 true ++ C))]
    rw [iter_add]
    rw [show (List.replicate (if b then 1 else 0) true
          ++ (false :: (unaryBlocks (flagTable ts) ++ rest)))
        = unaryBlocks [if b then 1 else 0] ++ (unaryBlocks (flagTable ts) ++ rest) from by
      simp [unaryBlocks]]
    rw [compl_flag P emb exit fail hP b inp A (unaryBlocks (flagTable ts) ++ rest)
      (false :: (List.replicate n1 true ++ (false :: (List.replicate n0 true ++ C))))]
    rw [ih]
    have hcompl : flagTable (complementFlags ((n0,n1,b) :: ts))
        = n0 :: n1 :: (if b then 0 else 1) :: flagTable (complementFlags ts) := by
      cases b <;> simp [flagTable, complementFlags]
    rw [hcompl]
    simp only [unaryBlocks, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]

def complTime (ts : List (Nat × Nat × Bool)) : Nat :=
  passTime ts+1+(2*(unaryBlocks (flagTable (complementFlags ts))).length+1)

theorem compl_component (ts : List (Nat × Nat × Bool)) (inp A : List Bool) :
    iter P (complTime ts) ⟨emb .c0,inp,A,unaryBlocks (flagTable ts),[]⟩
      = ⟨exit,inp,A,unaryBlocks (flagTable (complementFlags ts)),[]⟩ := by
  unfold complTime
  rw [show passTime ts+1+(2*(unaryBlocks (flagTable (complementFlags ts))).length+1)
      = passTime ts+(1+(2*(unaryBlocks (flagTable (complementFlags ts))).length+1)) from by ring]
  rw [show (unaryBlocks (flagTable ts) : List Bool) = unaryBlocks (flagTable ts) ++ [] from by simp]
  rw [iter_add, compl_pass P emb exit fail hP ts inp A [] []]
  simp only [List.append_nil]
  rw [iter_step' P (c' := ⟨emb (.fin .loop),inp,A,[],
    (unaryBlocks (flagTable (complementFlags ts))).reverse⟩) (by simp [step, hP, complCode])]
  rw [show 2*(unaryBlocks (flagTable (complementFlags ts))).length+1
      = 2*((unaryBlocks (flagTable (complementFlags ts))).reverse).length+1 from by simp]
  rw [moveCB_component P (fun t => emb (.fin t)) exit (fun s => by rw [hP (.fin s)]; rfl)
    ((unaryBlocks (flagTable (complementFlags ts))).reverse) inp A []]
  simp

end Compl


/-! ## Unary multiplication

Building a product automaton needs the index `p*n+q`, so the machine has to
multiply two numbers that are both DATA. Addition in unary is concatenation,
which the moves already do; multiplication is the repeated addition below.

The multiplier is a unary counter on stack A closed by a separator, the
multiplicand a unary counter on stack C closed by a separator, and the product
accumulates on stack B. The multiplicand is restored after each round by
stacking its markers on A and putting them back, which is why three stacks are
enough.
-/

inductive MulSt
  | loop
  | mark
  | inner
  | toB
  | toA
  | closeC
  | back
  | sep
  deriving DecidableEq

def mulCode {Q : Type} (emb : MulSt → Q) (exit fail : Q) : MulSt → Instr Q
  | .loop => .popA (emb .mark) exit exit
  | .mark => .pushA false (emb .inner)
  | .inner => .popC (emb .toB) (emb .closeC) fail
  | .toB => .pushB true (emb .toA)
  | .toA => .pushA true (emb .inner)
  | .closeC => .pushC false (emb .back)
  | .back => .popA (emb .sep) (emb .loop) (emb .loop)
  | .sep => .pushC true (emb .back)

section Mul

variable (P : Q → Instr Q) (emb : MulSt → Q) (exit fail : Q)
  (hP : ∀ s, P (emb s) = mulCode emb exit fail s)

include hP

/-- One pass over the multiplicand: its markers go to the accumulator and are
stacked on A, and the separator is written back on C. -/
theorem mul_inner (n : Nat) (inp A B C : List Bool) :
    iter P (3*n+2) ⟨emb .inner,inp,A,B,List.replicate n true ++ false :: C⟩
      = ⟨emb .back,inp,List.replicate n true ++ A,List.replicate n true ++ B,false :: C⟩ := by
  induction n generalizing A B with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    rw [iter_step P (c' := ⟨emb .closeC,inp,A,B,C⟩) (by simp [step, hP, mulCode])]
    rw [iter_one P (c' := ⟨emb .back,inp,A,B,false :: C⟩) (by simp [step, hP, mulCode])]
  | succ n ih =>
    have he : 3*(n+1)+2 = 1+(1+(1+(3*n+2))) := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .toB,inp,A,B,List.replicate n true ++ false :: C⟩)
      (by simp [step, hP, mulCode])]
    rw [iter_step' P (c' := ⟨emb .toA,inp,A,true :: B,List.replicate n true ++ false :: C⟩)
      (by simp [step, hP, mulCode])]
    rw [iter_step' P (c' := ⟨emb .inner,inp,true :: A,true :: B,
      List.replicate n true ++ false :: C⟩) (by simp [step, hP, mulCode])]
    rw [ih]
    simp only [List.replicate_succ, List.cons_append]
    rw [replicate_cons, replicate_cons]

/-- The multiplicand is put back on C, so the next round sees it again. -/
theorem mul_back (n : Nat) (inp A B C : List Bool) :
    iter P (2*n+1) ⟨emb .back,inp,List.replicate n true ++ false :: A,B,C⟩
      = ⟨emb .loop,inp,A,B,List.replicate n true ++ C⟩ := by
  induction n generalizing C with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    rw [iter_one P (c' := ⟨emb .loop,inp,A,B,C⟩) (by simp [step, hP, mulCode])]
  | succ n ih =>
    have he : 2*(n+1)+1 = 1+(1+(2*n+1)) := by ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .sep,inp,List.replicate n true ++ false :: A,B,C⟩)
      (by simp [step, hP, mulCode])]
    rw [iter_step' P (c' := ⟨emb .back,inp,List.replicate n true ++ false :: A,B,true :: C⟩)
      (by simp [step, hP, mulCode])]
    rw [ih, replicate_cons, List.cons_append]

def mulTime (m n : Nat) : Nat := m*(1+(1+((3*n+2)+(2*n+1))))+1

/-- `m` copies of `n` land on the accumulator; the multiplier is consumed and
the multiplicand restored. -/
theorem mul_component (m n : Nat) (inp A B C : List Bool) :
    iter P (mulTime m n)
        ⟨emb .loop,inp,List.replicate m true ++ false :: A,B,
          List.replicate n true ++ false :: C⟩
      = ⟨exit,inp,A,List.replicate (m*n) true ++ B,List.replicate n true ++ false :: C⟩ := by
  induction m generalizing B with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.zero_mul, Nat.zero_add, mulTime]
    rw [iter_one P (c' := ⟨exit,inp,A,B,List.replicate n true ++ false :: C⟩)
      (by simp [step, hP, mulCode])]
  | succ m ih =>
    have he : mulTime (m+1) n = 1+(1+((3*n+2)+((2*n+1)+mulTime m n))) := by
      simp only [mulTime]; ring
    rw [he, List.replicate_succ, List.cons_append]
    rw [iter_step' P (c' := ⟨emb .mark,inp,List.replicate m true ++ false :: A,B,
      List.replicate n true ++ false :: C⟩) (by simp [step, hP, mulCode])]
    rw [iter_step' P (c' := ⟨emb .inner,inp,false :: (List.replicate m true ++ false :: A),B,
      List.replicate n true ++ false :: C⟩) (by simp [step, hP, mulCode])]
    rw [iter_add, mul_inner P emb exit fail hP n inp
      (false :: (List.replicate m true ++ false :: A)) B C]
    rw [iter_add, mul_back P emb exit fail hP n inp (List.replicate m true ++ false :: A)
      (List.replicate n true ++ B) (false :: C)]
    rw [ih]
    have hrep : List.replicate (m*n) true ++ (List.replicate n true ++ B)
        = List.replicate ((m+1)*n) true ++ B := by
      rw [← List.append_assoc, ← List.replicate_add]
      congr 2
      ring
    rw [hrep]

end Mul


/-! ## Duplicating a table

A construction that reads one table many times — the product, for instance —
needs a second copy. With three stacks that is two sweeps: reverse the table
onto the free stack, then pour it back while writing a second copy.
-/

inductive DupSt
  | up
  | ut
  | uf
  | down
  | d1
  | d2
  | e1
  | e2
  deriving DecidableEq

def dupCode {Q : Type} (emb : DupSt → Q) (exit : Q) : DupSt → Instr Q
  | .up => .popB (emb .ut) (emb .uf) (emb .down)
  | .ut => .pushA true (emb .up)
  | .uf => .pushA false (emb .up)
  | .down => .popA (emb .d1) (emb .e1) exit
  | .d1 => .pushB true (emb .d2)
  | .d2 => .pushC true (emb .down)
  | .e1 => .pushB false (emb .e2)
  | .e2 => .pushC false (emb .down)

section Dup

variable (P : Q → Instr Q) (emb : DupSt → Q) (exit : Q)
  (hP : ∀ s, P (emb s) = dupCode emb exit s)

include hP

theorem dup_up (T : List Bool) (inp A C : List Bool) :
    iter P (2*T.length+1) ⟨emb .up,inp,A,T,C⟩ = ⟨emb .down,inp,T.reverse ++ A,[],C⟩ := by
  induction T generalizing A with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append]
    rw [iter_one P (c' := ⟨emb .down,inp,A,[],C⟩) (by simp [step, hP, dupCode])]
  | cons x T ih =>
    have he : 2*(x :: T).length+1 = (2*T.length+1)+1+1 := by
      simp only [List.length_cons]; ring
    rw [he]
    cases x with
    | false =>
      rw [iter_step P (c' := ⟨emb .uf,inp,A,T,C⟩) (by simp [step, hP, dupCode])]
      rw [iter_step P (c' := ⟨emb .up,inp,false :: A,T,C⟩) (by simp [step, hP, dupCode])]
      rw [ih]
      simp
    | true =>
      rw [iter_step P (c' := ⟨emb .ut,inp,A,T,C⟩) (by simp [step, hP, dupCode])]
      rw [iter_step P (c' := ⟨emb .up,inp,true :: A,T,C⟩) (by simp [step, hP, dupCode])]
      rw [ih]
      simp

theorem dup_down (T : List Bool) (inp B C : List Bool) :
    iter P (3*T.length+1) ⟨emb .down,inp,T,B,C⟩
      = ⟨exit,inp,[],T.reverse ++ B,T.reverse ++ C⟩ := by
  induction T generalizing B C with
  | nil =>
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append]
    rw [iter_one P (c' := ⟨exit,inp,[],B,C⟩) (by simp [step, hP, dupCode])]
  | cons x T ih =>
    have he : 3*(x :: T).length+1 = (3*T.length+1)+1+1+1 := by
      simp only [List.length_cons]; ring
    rw [he]
    cases x with
    | false =>
      rw [iter_step P (c' := ⟨emb .e1,inp,T,B,C⟩) (by simp [step, hP, dupCode])]
      rw [iter_step P (c' := ⟨emb .e2,inp,T,false :: B,C⟩) (by simp [step, hP, dupCode])]
      rw [iter_step P (c' := ⟨emb .down,inp,T,false :: B,false :: C⟩)
        (by simp [step, hP, dupCode])]
      rw [ih]
      simp
    | true =>
      rw [iter_step P (c' := ⟨emb .d1,inp,T,B,C⟩) (by simp [step, hP, dupCode])]
      rw [iter_step P (c' := ⟨emb .d2,inp,T,true :: B,C⟩) (by simp [step, hP, dupCode])]
      rw [iter_step P (c' := ⟨emb .down,inp,T,true :: B,true :: C⟩)
        (by simp [step, hP, dupCode])]
      rw [ih]
      simp

def dupTime (T : List Bool) : Nat := (2*T.length+1)+(3*T.length+1)

/-- Two copies of the table, one on each of the two stacks it did not occupy. -/
theorem dup_component (T : List Bool) (inp : List Bool) :
    iter P (dupTime T) ⟨emb .up,inp,[],T,[]⟩ = ⟨exit,inp,[],T,T⟩ := by
  unfold dupTime
  rw [iter_add, dup_up P emb exit hP T inp [] []]
  simp only [List.append_nil]
  rw [show 3*T.length+1 = 3*(T.reverse).length+1 from by simp]
  rw [dup_down P emb exit hP T.reverse inp [] []]
  simp

end Dup

/-! ## What this gives

A transition table of a DFA built from the input can be stored on stack B as a
list of unary entries; `skip_component` moves the machine to the entry it wants
in `3k+2m+1` steps, where `k` entries of total size `m` were skipped, with the
skipped part preserved on stack C so the table can be restored. That is the
primitive a table-driven simulation needs, and it was the obstacle recorded in
v1638. The stages above it — the simulator, the cap front end, the decision —
are still not realised, so `SevenExpTimeTarget.SevenExpTime` remains open.
-/

end NSSE.BitMachine3
