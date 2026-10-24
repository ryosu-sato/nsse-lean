import NSSE.RawBitNumeral

/-! # The bit machine with `k` stacks

v1648 recorded why the next stage — the product construction and an emptiness
test — does not fit on three stacks: it needs five live regions. This file is
the model with an indexed family of stacks, which is the recommended way out.
Nothing else changes: one step reads one input bit, or pushes or pops one bit
on ONE stack, so the model is still as fine-grained as the two- and three-stack
ones, and it is polynomially equivalent to them and to a Turing machine.

Only the core is set up here — the step and iteration lemmas and the transport
of a program along a renaming of its states. Components are re-derived on top of
it as they are needed; the earlier files stay as they are.
-/

namespace NSSE.BitMachineK

variable {Q : Type} {k : Nat}

structure Config (Q : Type) (k : Nat) where
  state : Q
  input : List Bool
  stk : Fin k → List Bool

inductive Instr (Q : Type) (k : Nat)
  | read (onTrue onFalse onEmpty : Q)
  | push (i : Fin k) (bit : Bool) (next : Q)
  | pop (i : Fin k) (onTrue onFalse onEmpty : Q)
  | nop (next : Q)
  | halt

def step (P : Q → Instr Q k) (c : Config Q k) : Option (Config Q k) :=
  match P c.state with
  | .halt => none
  | .read t f e =>
    match c.input with
    | [] => some ⟨e,[],c.stk⟩
    | true :: w => some ⟨t,w,c.stk⟩
    | false :: w => some ⟨f,w,c.stk⟩
  | .push i bit next =>
    some ⟨next,c.input,Function.update c.stk i (bit :: c.stk i)⟩
  | .pop i t f e =>
    match c.stk i with
    | [] => some ⟨e,c.input,c.stk⟩
    | true :: r => some ⟨t,c.input,Function.update c.stk i r⟩
    | false :: r => some ⟨f,c.input,Function.update c.stk i r⟩
  | .nop next => some ⟨next,c.input,c.stk⟩

def iter (P : Q → Instr Q k) : Nat → Config Q k → Config Q k
  | 0, c => c
  | n+1, c =>
    match step P c with
    | none => c
    | some c' => iter P n c'

theorem iter_halt (P : Q → Instr Q k) (c : Config Q k) (h : step P c = none) (n : Nat) :
    iter P n c = c := by
  cases n with
  | zero => rfl
  | succ n => simp only [iter, h]

theorem iter_step (P : Q → Instr Q k) {c c' : Config Q k} (h : step P c = some c') (n : Nat) :
    iter P (n+1) c = iter P n c' := by
  simp only [iter, h]

theorem iter_step' (P : Q → Instr Q k) {c c' : Config Q k} (h : step P c = some c') (n : Nat) :
    iter P (1+n) c = iter P n c' := by
  rw [Nat.add_comm]
  exact iter_step P h n

theorem iter_one (P : Q → Instr Q k) {c c' : Config Q k} (h : step P c = some c') :
    iter P 1 c = c' := by
  show (match step P c with | none => c | some c'' => iter P 0 c'') = c'
  rw [h]
  rfl

theorem iter_add (P : Q → Instr Q k) (m n : Nat) (c : Config Q k) :
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

/-! ## Transport along a renaming of the states -/

def Instr.map {Q Q' : Type} (f : Q → Q') : Instr Q k → Instr Q' k
  | .read t fa e => .read (f t) (f fa) (f e)
  | .push i b n => .push i b (f n)
  | .pop i t fa e => .pop i (f t) (f fa) (f e)
  | .nop n => .nop (f n)
  | .halt => .halt

def mapConfig {Q Q' : Type} (f : Q → Q') (c : Config Q k) : Config Q' k :=
  ⟨f c.state,c.input,c.stk⟩

theorem step_map {Q Q' : Type} (P : Q → Instr Q k) (P' : Q' → Instr Q' k) (f : Q → Q')
    (h : ∀ q, P' (f q) = Instr.map f (P q)) (c : Config Q k) :
    step P' (mapConfig f c) = (step P c).map (mapConfig f) := by
  simp only [step, mapConfig, h]
  cases P c.state <;> simp only [Instr.map]
  case read t fa e => cases c.input with
    | nil => rfl
    | cons x w => cases x <;> rfl
  case pop i t fa e => cases c.stk i with
    | nil => rfl
    | cons x r => cases x <;> rfl
  all_goals rfl

theorem iter_map {Q Q' : Type} (P : Q → Instr Q k) (P' : Q' → Instr Q' k) (f : Q → Q')
    (h : ∀ q, P' (f q) = Instr.map f (P q)) (n : Nat) (c : Config Q k) :
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

/-! ## Moving one stack onto another

The first component in the new model, and the one that shows the gain: a single
lemma covers every pair of stacks, where the three-stack file needed one per
direction. -/

inductive MSt
  | loop
  | pt
  | pf
  deriving DecidableEq

def moveCode (i j : Fin k) (emb : MSt → Q) (exit : Q) : MSt → Instr Q k
  | .loop => .pop i (emb .pt) (emb .pf) exit
  | .pt => .push j true (emb .loop)
  | .pf => .push j false (emb .loop)

theorem move_component (P : Q → Instr Q k) (i j : Fin k) (hij : i ≠ j)
    (emb : MSt → Q) (exit : Q) (hP : ∀ s, P (emb s) = moveCode i j emb exit s)
    (S : List Bool) (inp : List Bool) (st : Fin k → List Bool) (hi : st i = S) :
    iter P (2*S.length+1) ⟨emb .loop,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st i []) j (S.reverse ++ st j)⟩ := by
  induction S generalizing st with
  | nil =>
    have hstep : step P ⟨emb .loop,inp,st⟩ = some ⟨exit,inp,st⟩ := by
      simp [step, hP, moveCode, hi]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append]
    rw [iter_one P hstep]
    have : Function.update (Function.update st i []) j (st j) = st := by
      funext x
      by_cases hx : x = j
      · subst hx; simp [Function.update_apply, hij.symm]
      · by_cases hy : x = i
        · subst hy; simp [Function.update_apply, hx, hi]
        · simp [Function.update_apply, hx, hy]
    rw [this]
  | cons x S ih =>
    have he : 2*(x :: S).length+1 = (2*S.length+1)+1+1 := by
      simp only [List.length_cons]; ring
    rw [he]
    cases x with
    | false =>
      have h1 : step P ⟨emb .loop,inp,st⟩
          = some ⟨emb .pf,inp,Function.update st i S⟩ := by
        simp [step, hP, moveCode, hi]
      rw [iter_step P h1]
      have h2 : step P ⟨emb .pf,inp,Function.update st i S⟩
          = some ⟨emb .loop,inp,Function.update (Function.update st i S) j
            (false :: (Function.update st i S) j)⟩ := by
        simp [step, hP, moveCode]
      rw [iter_step P h2]
      have hji : (Function.update st i S) j = st j := by
        simp [Function.update_apply, hij.symm]
      rw [hji]
      rw [ih (Function.update (Function.update st i S) j (false :: st j))
        (by simp [Function.update_apply, hij])]
      congr 1
      funext y
      by_cases hy : y = j
      · subst hy; simp [Function.update_apply, hij.symm]
      · by_cases hz : y = i
        · subst hz; simp [Function.update_apply, hy]
        · simp [Function.update_apply, hy, hz]
    | true =>
      have h1 : step P ⟨emb .loop,inp,st⟩
          = some ⟨emb .pt,inp,Function.update st i S⟩ := by
        simp [step, hP, moveCode, hi]
      rw [iter_step P h1]
      have h2 : step P ⟨emb .pt,inp,Function.update st i S⟩
          = some ⟨emb .loop,inp,Function.update (Function.update st i S) j
            (true :: (Function.update st i S) j)⟩ := by
        simp [step, hP, moveCode]
      rw [iter_step P h2]
      have hji : (Function.update st i S) j = st j := by
        simp [Function.update_apply, hij.symm]
      rw [hji]
      rw [ih (Function.update (Function.update st i S) j (true :: st j))
        (by simp [Function.update_apply, hij])]
      congr 1
      funext y
      by_cases hy : y = j
      · subst hy; simp [Function.update_apply, hij.symm]
      · by_cases hz : y = i
        · subst hz; simp [Function.update_apply, hy]
        · simp [Function.update_apply, hy, hz]


/-! ## Scaling a unary counter

Reading a counter off one stack and writing a constant multiple of it on
another: the index arithmetic a table lookup needs, now generic in the two
stacks. -/

inductive SSt
  | loop
  | push (j : Nat)
  deriving DecidableEq

def scaleCode (m : Nat) (src dst : Fin k) (emb : SSt → Q) (exit : Q) : SSt → Instr Q k
  | .loop => .pop src (emb (.push m)) exit exit
  | .push 0 => .nop (emb .loop)
  | .push (j+1) => .push dst true (emb (.push j))

section Scale

variable (P : Q → Instr Q k) (m : Nat) (src dst : Fin k) (hne : src ≠ dst)
  (emb : SSt → Q) (exit : Q) (hP : ∀ s, P (emb s) = scaleCode m src dst emb exit s)

include hP

theorem scale_push (j : Nat) (inp : List Bool) (st : Fin k → List Bool) :
    iter P (j+1) ⟨emb (.push j),inp,st⟩
      = ⟨emb .loop,inp,Function.update st dst (List.replicate j true ++ st dst)⟩ := by
  induction j generalizing st with
  | zero =>
    have h1 : step P ⟨emb (.push 0),inp,st⟩ = some ⟨emb .loop,inp,st⟩ := by
      simp [step, hP, scaleCode]
    rw [iter_one P h1]
    simp
  | succ j ih =>
    have h1 : step P ⟨emb (.push (j+1)),inp,st⟩
        = some ⟨emb (.push j),inp,Function.update st dst (true :: st dst)⟩ := by
      simp [step, hP, scaleCode]
    rw [show j+1+1 = (j+1)+1 from rfl, iter_step P h1, ih]
    congr 1
    funext y
    by_cases hy : y = dst
    · subst hy
      simp [Function.update_idem, List.replicate_succ, replicate_cons]
    · simp only [Function.update_noteq hy]

include hne

theorem scale_component (n : Nat) (inp : List Bool) (st : Fin k → List Bool)
    (rest : List Bool) (hsrc : st src = List.replicate n true ++ false :: rest) :
    iter P (n*(m+2)+1) ⟨emb .loop,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st src rest) dst
          (List.replicate (n*m) true ++ st dst)⟩ := by
  induction n generalizing st with
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at hsrc
    have h1 : step P ⟨emb .loop,inp,st⟩ = some ⟨exit,inp,Function.update st src rest⟩ := by
      simp [step, hP, scaleCode, hsrc]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [iter_one P h1]
    congr 1
    funext y
    by_cases hy : y = dst
    · subst hy
      simp only [Function.update_same, List.replicate_zero, Nat.zero_mul, List.nil_append,
        Function.update_noteq (Ne.symm hne)]
    · by_cases hz : y = src
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same]
      · simp only [Function.update_noteq hy, Function.update_noteq hz]
  | succ n ih =>
    have he : (n+1)*(m+2)+1 = 1+((m+1)+(n*(m+2)+1)) := by ring
    have hsrc' : st src = true :: (List.replicate n true ++ false :: rest) := by
      rw [hsrc, List.replicate_succ, List.cons_append]
    have h1 : step P ⟨emb .loop,inp,st⟩
        = some ⟨emb (.push m),inp,Function.update st src
          (List.replicate n true ++ false :: rest)⟩ := by
      simp [step, hP, scaleCode, hsrc']
    rw [he, iter_step' P h1, iter_add,
      scale_push P m src dst emb exit hP m inp
        (Function.update st src (List.replicate n true ++ false :: rest))]
    have hdst : (Function.update st src (List.replicate n true ++ false :: rest)) dst = st dst := by
      simp only [Function.update_noteq (Ne.symm hne)]
    rw [hdst]
    rw [ih (Function.update (Function.update st src (List.replicate n true ++ false :: rest)) dst
      (List.replicate m true ++ st dst)) (by
        simp only [Function.update_noteq hne, Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = dst
    · subst hy
      simp only [Function.update_same, Function.update_noteq (Ne.symm hne)]
      rw [← List.append_assoc, ← List.replicate_add]
      congr 2
      ring
    · by_cases hz : y = src
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same]
      · simp only [Function.update_noteq hy, Function.update_noteq hz]

end Scale


/-! ## Table lookup

Tables are lists of unary entries, each closed by a separator, exactly as in the
three-stack file. The index is a unary counter on one stack, the table on
another, and the entries passed over are kept on a third so the table can be
rebuilt. Generic in all three indices. -/

def blocks : List Nat → List Bool
  | [] => []
  | n :: ns => List.replicate n true ++ false :: blocks ns

theorem blocks_append (xs ys : List Nat) : blocks (xs ++ ys) = blocks xs ++ blocks ys := by
  induction xs with
  | nil => simp [blocks]
  | cons n xs ih => simp only [List.cons_append, blocks, ih, List.append_assoc, List.cons_append]

inductive KSt
  | loop
  | scan
  | pt
  | pf
  deriving DecidableEq

def skipCode (idx tab tmp : Fin k) (emb : KSt → Q) (exit fail : Q) : KSt → Instr Q k
  | .loop => .pop idx (emb .scan) exit exit
  | .scan => .pop tab (emb .pt) (emb .pf) fail
  | .pt => .push tmp true (emb .scan)
  | .pf => .push tmp false (emb .loop)

section Skip

variable (P : Q → Instr Q k) (idx tab tmp : Fin k)
  (hit : idx ≠ tab) (him : idx ≠ tmp) (htm : tab ≠ tmp)
  (emb : KSt → Q) (exit fail : Q)
  (hP : ∀ s, P (emb s) = skipCode idx tab tmp emb exit fail s)

include hP htm

theorem scan_block (n : Nat) (inp : List Bool) (st : Fin k → List Bool) (rest : List Bool)
    (htab : st tab = List.replicate n true ++ false :: rest) :
    iter P (2*n+2) ⟨emb .scan,inp,st⟩
      = ⟨emb .loop,inp,Function.update (Function.update st tab rest) tmp
          (false :: (List.replicate n true ++ st tmp))⟩ := by
  induction n generalizing st with
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at htab
    have h1 : step P ⟨emb .scan,inp,st⟩ = some ⟨emb .pf,inp,Function.update st tab rest⟩ := by
      simp [step, hP, skipCode, htab]
    have h2 : step P ⟨emb .pf,inp,Function.update st tab rest⟩
        = some ⟨emb .loop,inp,Function.update (Function.update st tab rest) tmp
          (false :: (Function.update st tab rest) tmp)⟩ := by
      simp [step, hP, skipCode]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [iter_step P h1, iter_one P h2]
    simp only [Function.update_noteq (Ne.symm htm), List.replicate_zero, List.nil_append]
  | succ n ih =>
    have htab' : st tab = true :: (List.replicate n true ++ false :: rest) := by
      rw [htab, List.replicate_succ, List.cons_append]
    have h1 : step P ⟨emb .scan,inp,st⟩
        = some ⟨emb .pt,inp,Function.update st tab (List.replicate n true ++ false :: rest)⟩ := by
      simp [step, hP, skipCode, htab']
    have h2 : step P ⟨emb .pt,inp,
        Function.update st tab (List.replicate n true ++ false :: rest)⟩
        = some ⟨emb .scan,inp,Function.update
          (Function.update st tab (List.replicate n true ++ false :: rest)) tmp
          (true :: (Function.update st tab (List.replicate n true ++ false :: rest)) tmp)⟩ := by
      simp [step, hP, skipCode]
    have he : 2*(n+1)+2 = 1+(1+(2*n+2)) := by ring
    rw [he, iter_step' P h1, iter_step' P h2]
    simp only [Function.update_noteq (Ne.symm htm)]
    rw [ih (Function.update (Function.update st tab (List.replicate n true ++ false :: rest)) tmp
      (true :: st tmp)) (by simp [Function.update_noteq htm, Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = tmp
    · subst hy
      simp only [Function.update_same, Function.update_noteq htm, Function.update_idem,
        List.replicate_succ, List.cons_append]
      rw [replicate_cons]
    · by_cases hz : y = tab
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same, Function.update_idem]
      · simp only [Function.update_noteq hy, Function.update_noteq hz]

include hit him

theorem skip_component (pre : List Nat) (inp : List Bool) (st : Fin k → List Bool)
    (A post : List Bool)
    (hidx : st idx = List.replicate pre.length true ++ false :: A)
    (htab : st tab = blocks pre ++ post) :
    iter P (3*pre.length+2*pre.sum+1) ⟨emb .loop,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st idx A) tab post) tmp
          ((blocks pre).reverse ++ st tmp)⟩ := by
  induction pre generalizing st with
  | nil =>
    simp only [List.length_nil, List.sum_nil, Nat.mul_zero, Nat.zero_add, List.replicate_zero,
      List.nil_append, blocks, List.reverse_nil] at *
    have h1 : step P ⟨emb .loop,inp,st⟩ = some ⟨exit,inp,Function.update st idx A⟩ := by
      simp [step, hP, skipCode, hidx]
    rw [iter_one P h1]
    congr 1
    funext y
    by_cases hy : y = tmp
    · subst hy
      simp only [Function.update_same, Function.update_noteq (Ne.symm him),
        Function.update_noteq (Ne.symm htm), List.nil_append]
    · by_cases hz : y = tab
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same,
          Function.update_noteq (Ne.symm hit), htab]
      · simp only [Function.update_noteq hy, Function.update_noteq hz]
  | cons n pre ih =>
    have hidx' : st idx = true :: (List.replicate pre.length true ++ false :: A) := by
      rw [hidx]
      simp only [List.length_cons, List.replicate_succ, List.cons_append]
    have htab' : st tab = List.replicate n true ++ false :: (blocks pre ++ post) := by
      rw [htab]
      simp only [blocks, List.append_assoc, List.cons_append]
    have he : 3*(n :: pre).length+2*(n :: pre).sum+1
        = 1+((2*n+2)+(3*pre.length+2*pre.sum+1)) := by
      simp only [List.length_cons, List.sum_cons]; ring
    have h1 : step P ⟨emb .loop,inp,st⟩
        = some ⟨emb .scan,inp,Function.update st idx
          (List.replicate pre.length true ++ false :: A)⟩ := by
      simp [step, hP, skipCode, hidx']
    rw [he, iter_step' P h1, iter_add]
    rw [scan_block P idx tab tmp htm emb exit fail hP n inp
      (Function.update st idx (List.replicate pre.length true ++ false :: A))
      (blocks pre ++ post) (by simp [Function.update_noteq (Ne.symm hit), htab'])]
    simp only [Function.update_noteq (Ne.symm him)]
    rw [ih (Function.update (Function.update
        (Function.update st idx (List.replicate pre.length true ++ false :: A))
        tab (blocks pre ++ post)) tmp (false :: (List.replicate n true ++ st tmp)))
      (by simp [Function.update_noteq him, Function.update_noteq hit, Function.update_same])
      (by simp [Function.update_noteq htm, Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = tmp
    · subst hy
      simp only [Function.update_same, Function.update_noteq htm, Function.update_noteq him,
        Function.update_idem, blocks, List.reverse_append, List.reverse_cons,
        List.reverse_replicate, List.append_assoc, List.cons_append, List.nil_append,
        List.singleton_append]
    · by_cases hz : y = tab
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same, Function.update_idem]
      · by_cases hw : y = idx
        · subst hw
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
            Function.update_idem]
        · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw]

end Skip


/-! ## Copying one entry, and pouring a stack onto two others

Two more components the constructions need: reading a single table entry and
writing it twice (the new state register and the preserved copy of the table),
and emptying a stack onto two others at once, which with a preceding move is how
a table is duplicated. -/

inductive DSt
  | loop
  | pa
  | pb
  | sep
  deriving DecidableEq

def copyCode (src d1 d2 : Fin k) (emb : DSt → Q) (exit fail : Q) : DSt → Instr Q k
  | .loop => .pop src (emb .pa) (emb .sep) fail
  | .pa => .push d1 true (emb .pb)
  | .pb => .push d2 true (emb .loop)
  | .sep => .push d2 false exit

section Copy

variable (P : Q → Instr Q k) (src d1 d2 : Fin k)
  (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2)
  (emb : DSt → Q) (exit fail : Q)
  (hP : ∀ s, P (emb s) = copyCode src d1 d2 emb exit fail s)

include hP h1 h2 h12

theorem copy_component (n : Nat) (inp : List Bool) (st : Fin k → List Bool) (rest : List Bool)
    (hsrc : st src = List.replicate n true ++ false :: rest) :
    iter P (3*n+2) ⟨emb .loop,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st src rest) d1
          (List.replicate n true ++ st d1)) d2 (false :: (List.replicate n true ++ st d2))⟩ := by
  induction n generalizing st with
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at hsrc
    have s1 : step P ⟨emb .loop,inp,st⟩ = some ⟨emb .sep,inp,Function.update st src rest⟩ := by
      simp [step, hP, copyCode, hsrc]
    have s2 : step P ⟨emb .sep,inp,Function.update st src rest⟩
        = some ⟨exit,inp,Function.update (Function.update st src rest) d2
          (false :: (Function.update st src rest) d2)⟩ := by
      simp [step, hP, copyCode]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [iter_step P s1, iter_one P s2]
    congr 1
    funext y
    by_cases hy : y = d2
    · subst hy
      simp only [Function.update_same, Function.update_noteq (Ne.symm h2), List.replicate_zero,
        List.nil_append]
    · by_cases hz : y = d1
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same,
          Function.update_noteq (Ne.symm h1), List.replicate_zero, List.nil_append]
      · simp only [Function.update_noteq hy, Function.update_noteq hz]
  | succ n ih =>
    have hsrc' : st src = true :: (List.replicate n true ++ false :: rest) := by
      rw [hsrc, List.replicate_succ, List.cons_append]
    have s1 : step P ⟨emb .loop,inp,st⟩
        = some ⟨emb .pa,inp,Function.update st src (List.replicate n true ++ false :: rest)⟩ := by
      simp [step, hP, copyCode, hsrc']
    have s2 : ∀ u : Fin k → List Bool, step P ⟨emb .pa,inp,u⟩
        = some ⟨emb .pb,inp,Function.update u d1 (true :: u d1)⟩ := by
      intro u; simp [step, hP, copyCode]
    have s3 : ∀ u : Fin k → List Bool, step P ⟨emb .pb,inp,u⟩
        = some ⟨emb .loop,inp,Function.update u d2 (true :: u d2)⟩ := by
      intro u; simp [step, hP, copyCode]
    have he : 3*(n+1)+2 = 1+(1+(1+(3*n+2))) := by ring
    rw [he, iter_step' P s1, iter_step' P (s2 _), iter_step' P (s3 _)]
    have e1 : (Function.update st src (List.replicate n true ++ false :: rest)) d1 = st d1 := by
      simp only [Function.update_noteq (Ne.symm h1)]
    have e2 : (Function.update (Function.update st src (List.replicate n true ++ false :: rest)) d1
        (true :: st d1)) d2 = st d2 := by
      simp only [Function.update_noteq (Ne.symm h12), Function.update_noteq (Ne.symm h2)]
    rw [e1, e2]
    rw [ih (Function.update (Function.update
        (Function.update st src (List.replicate n true ++ false :: rest)) d1 (true :: st d1))
        d2 (true :: st d2))
      (by simp [Function.update_noteq h2, Function.update_noteq h1, Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = d2
    · subst hy
      simp only [Function.update_same, Function.update_noteq h12, Function.update_noteq (Ne.symm h2),
        Function.update_idem, List.replicate_succ, List.cons_append]
      rw [replicate_cons]
    · by_cases hz : y = d1
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same, Function.update_idem,
          Function.update_noteq (Ne.symm h1), List.replicate_succ, List.cons_append]
        rw [replicate_cons]
      · by_cases hw : y = src
        · subst hw
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
            Function.update_idem]
        · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw]

end Copy

inductive PSt
  | loop
  | t1
  | t2
  | f1
  | f2
  deriving DecidableEq

def pourCode (src d1 d2 : Fin k) (emb : PSt → Q) (exit : Q) : PSt → Instr Q k
  | .loop => .pop src (emb .t1) (emb .f1) exit
  | .t1 => .push d1 true (emb .t2)
  | .t2 => .push d2 true (emb .loop)
  | .f1 => .push d1 false (emb .f2)
  | .f2 => .push d2 false (emb .loop)

section Pour

variable (P : Q → Instr Q k) (src d1 d2 : Fin k)
  (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2)
  (emb : PSt → Q) (exit : Q)
  (hP : ∀ s, P (emb s) = pourCode src d1 d2 emb exit s)

include hP h1 h2 h12

theorem pour_component (S : List Bool) (inp : List Bool) (st : Fin k → List Bool)
    (hsrc : st src = S) :
    iter P (3*S.length+1) ⟨emb .loop,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st src []) d1
          (S.reverse ++ st d1)) d2 (S.reverse ++ st d2)⟩ := by
  induction S generalizing st with
  | nil =>
    have s1 : step P ⟨emb .loop,inp,st⟩ = some ⟨exit,inp,st⟩ := by
      simp [step, hP, pourCode, hsrc]
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.nil_append]
    rw [iter_one P s1]
    congr 1
    funext y
    by_cases hy : y = d2
    · subst hy
      simp only [Function.update_same, Function.update_noteq (Ne.symm h2)]
    · by_cases hz : y = d1
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same,
          Function.update_noteq (Ne.symm h1)]
      · by_cases hw : y = src
        · subst hw
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same, hsrc]
        · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw]
  | cons x S ih =>
    have he : 3*(x :: S).length+1 = 1+(1+(1+(3*S.length+1))) := by
      simp only [List.length_cons]; ring
    have hsrc' : st src = x :: S := hsrc
    rw [he]
    cases x with
    | false =>
      have s1 : step P ⟨emb .loop,inp,st⟩
          = some ⟨emb .f1,inp,Function.update st src S⟩ := by
        simp [step, hP, pourCode, hsrc']
      have s2 : ∀ u : Fin k → List Bool, step P ⟨emb .f1,inp,u⟩
          = some ⟨emb .f2,inp,Function.update u d1 (false :: u d1)⟩ := by
        intro u; simp [step, hP, pourCode]
      have s3 : ∀ u : Fin k → List Bool, step P ⟨emb .f2,inp,u⟩
          = some ⟨emb .loop,inp,Function.update u d2 (false :: u d2)⟩ := by
        intro u; simp [step, hP, pourCode]
      rw [iter_step' P s1, iter_step' P (s2 _), iter_step' P (s3 _)]
      have e1 : (Function.update st src S) d1 = st d1 := by
        simp only [Function.update_noteq (Ne.symm h1)]
      have e2 : (Function.update (Function.update st src S) d1 (false :: st d1)) d2 = st d2 := by
        simp only [Function.update_noteq (Ne.symm h12), Function.update_noteq (Ne.symm h2)]
      rw [e1, e2]
      rw [ih (Function.update (Function.update (Function.update st src S) d1 (false :: st d1))
        d2 (false :: st d2)) (by simp [Function.update_noteq h2, Function.update_noteq h1,
          Function.update_same])]
      congr 1
      funext y
      by_cases hy : y = d2
      · subst hy
        simp only [Function.update_same, Function.update_noteq h12,
          Function.update_noteq (Ne.symm h2), Function.update_idem, List.reverse_cons,
          List.append_assoc, List.singleton_append]
      · by_cases hz : y = d1
        · subst hz
          simp only [Function.update_noteq hy, Function.update_same, Function.update_idem,
            Function.update_noteq (Ne.symm h1), List.reverse_cons, List.append_assoc,
            List.singleton_append]
        · by_cases hw : y = src
          · subst hw
            simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
              Function.update_idem]
          · simp only [Function.update_noteq hy, Function.update_noteq hz,
              Function.update_noteq hw]
    | true =>
      have s1 : step P ⟨emb .loop,inp,st⟩
          = some ⟨emb .t1,inp,Function.update st src S⟩ := by
        simp [step, hP, pourCode, hsrc']
      have s2 : ∀ u : Fin k → List Bool, step P ⟨emb .t1,inp,u⟩
          = some ⟨emb .t2,inp,Function.update u d1 (true :: u d1)⟩ := by
        intro u; simp [step, hP, pourCode]
      have s3 : ∀ u : Fin k → List Bool, step P ⟨emb .t2,inp,u⟩
          = some ⟨emb .loop,inp,Function.update u d2 (true :: u d2)⟩ := by
        intro u; simp [step, hP, pourCode]
      rw [iter_step' P s1, iter_step' P (s2 _), iter_step' P (s3 _)]
      have e1 : (Function.update st src S) d1 = st d1 := by
        simp only [Function.update_noteq (Ne.symm h1)]
      have e2 : (Function.update (Function.update st src S) d1 (true :: st d1)) d2 = st d2 := by
        simp only [Function.update_noteq (Ne.symm h12), Function.update_noteq (Ne.symm h2)]
      rw [e1, e2]
      rw [ih (Function.update (Function.update (Function.update st src S) d1 (true :: st d1))
        d2 (true :: st d2)) (by simp [Function.update_noteq h2, Function.update_noteq h1,
          Function.update_same])]
      congr 1
      funext y
      by_cases hy : y = d2
      · subst hy
        simp only [Function.update_same, Function.update_noteq h12,
          Function.update_noteq (Ne.symm h2), Function.update_idem, List.reverse_cons,
          List.append_assoc, List.singleton_append]
      · by_cases hz : y = d1
        · subst hz
          simp only [Function.update_noteq hy, Function.update_same, Function.update_idem,
            Function.update_noteq (Ne.symm h1), List.reverse_cons, List.append_assoc,
            List.singleton_append]
        · by_cases hw : y = src
          · subst hw
            simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
              Function.update_idem]
          · simp only [Function.update_noteq hy, Function.update_noteq hz,
              Function.update_noteq hw]

end Pour


/-! ## Writing one entry

The dual of the lookup: a unary counter on one stack becomes a table entry —
markers and a closing separator — on another. A table is built by writing its
entries in turn and reversing the result once, exactly as the rewriting pass of
v1645 did. -/

inductive WSt
  | loop
  | pt
  | psep
  deriving DecidableEq

def writeCode (src dst : Fin k) (emb : WSt → Q) (exit : Q) : WSt → Instr Q k
  | .loop => .pop src (emb .pt) (emb .psep) exit
  | .pt => .push dst true (emb .loop)
  | .psep => .push dst false exit

section Write

variable (P : Q → Instr Q k) (src dst : Fin k) (hne : src ≠ dst)
  (emb : WSt → Q) (exit : Q) (hP : ∀ s, P (emb s) = writeCode src dst emb exit s)

include hP hne

theorem write_component (n : Nat) (inp : List Bool) (st : Fin k → List Bool) (rest : List Bool)
    (hsrc : st src = List.replicate n true ++ false :: rest) :
    iter P (2*n+2) ⟨emb .loop,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st src rest) dst
          (false :: (List.replicate n true ++ st dst))⟩ := by
  induction n generalizing st with
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at hsrc
    have s1 : step P ⟨emb .loop,inp,st⟩ = some ⟨emb .psep,inp,Function.update st src rest⟩ := by
      simp [step, hP, writeCode, hsrc]
    have s2 : step P ⟨emb .psep,inp,Function.update st src rest⟩
        = some ⟨exit,inp,Function.update (Function.update st src rest) dst
          (false :: (Function.update st src rest) dst)⟩ := by
      simp [step, hP, writeCode]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [iter_step P s1, iter_one P s2]
    simp only [Function.update_noteq (Ne.symm hne), List.replicate_zero, List.nil_append]
  | succ n ih =>
    have hsrc' : st src = true :: (List.replicate n true ++ false :: rest) := by
      rw [hsrc, List.replicate_succ, List.cons_append]
    have s1 : step P ⟨emb .loop,inp,st⟩
        = some ⟨emb .pt,inp,Function.update st src (List.replicate n true ++ false :: rest)⟩ := by
      simp [step, hP, writeCode, hsrc']
    have s2 : ∀ u : Fin k → List Bool, step P ⟨emb .pt,inp,u⟩
        = some ⟨emb .loop,inp,Function.update u dst (true :: u dst)⟩ := by
      intro u; simp [step, hP, writeCode]
    have he : 2*(n+1)+2 = 1+(1+(2*n+2)) := by ring
    rw [he, iter_step' P s1, iter_step' P (s2 _)]
    have e1 : (Function.update st src (List.replicate n true ++ false :: rest)) dst = st dst := by
      simp only [Function.update_noteq (Ne.symm hne)]
    rw [e1]
    rw [ih (Function.update (Function.update st src (List.replicate n true ++ false :: rest))
      dst (true :: st dst))
      (by simp [Function.update_noteq hne, Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = dst
    · subst hy
      simp only [Function.update_same, Function.update_noteq hne, Function.update_idem,
        List.replicate_succ, List.cons_append]
      rw [replicate_cons]
    · by_cases hz : y = src
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same, Function.update_idem]
      · simp only [Function.update_noteq hy, Function.update_noteq hz]

end Write


/-! ## Multiplying two counters

The product construction indexes state pairs by `p*n+q`, so both factors are
data. With a stack to spare the three-stack trick of v1646 — marking the
working stack to tell the temporary markers from the multiplier — is no longer
needed: the sweep is stacked on a dedicated scratch stack and poured back.
-/

inductive MulSt
  | loop
  | inner
  | toAcc
  | toTmp
  | closeM
  | back
  | backPush
  deriving DecidableEq

def mulCode (m1 m2 acc tmp : Fin k) (emb : MulSt → Q) (exit fail : Q) : MulSt → Instr Q k
  | .loop => .pop m1 (emb .inner) exit exit
  | .inner => .pop m2 (emb .toAcc) (emb .closeM) fail
  | .toAcc => .push acc true (emb .toTmp)
  | .toTmp => .push tmp true (emb .inner)
  | .closeM => .push m2 false (emb .back)
  | .back => .pop tmp (emb .backPush) (emb .loop) (emb .loop)
  | .backPush => .push m2 true (emb .back)

section Mul

variable (P : Q → Instr Q k) (m1 m2 acc tmp : Fin k)
  (h12 : m1 ≠ m2) (h1a : m1 ≠ acc) (h1t : m1 ≠ tmp)
  (h2a : m2 ≠ acc) (h2t : m2 ≠ tmp) (hat : acc ≠ tmp)
  (emb : MulSt → Q) (exit fail : Q)
  (hP : ∀ s, P (emb s) = mulCode m1 m2 acc tmp emb exit fail s)

include hP h2a h2t hat

/-- The multiplicand is swept into the accumulator and stacked on the scratch
stack, and its separator is written back. -/
theorem mul_sweep (b : Nat) (inp : List Bool) (st : Fin k → List Bool) (restB : List Bool)
    (hm2 : st m2 = List.replicate b true ++ false :: restB) :
    iter P (3*b+2) ⟨emb .inner,inp,st⟩
      = ⟨emb .back,inp,Function.update (Function.update (Function.update st m2 (false :: restB))
          acc (List.replicate b true ++ st acc)) tmp (List.replicate b true ++ st tmp)⟩ := by
  induction b generalizing st with
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at hm2
    have s1 : step P ⟨emb .inner,inp,st⟩ = some ⟨emb .closeM,inp,Function.update st m2 restB⟩ := by
      simp [step, hP, mulCode, hm2]
    have s2 : step P ⟨emb .closeM,inp,Function.update st m2 restB⟩
        = some ⟨emb .back,inp,Function.update (Function.update st m2 restB) m2
          (false :: (Function.update st m2 restB) m2)⟩ := by
      simp [step, hP, mulCode]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [iter_step P s1, iter_one P s2]
    congr 1
    funext y
    by_cases hy : y = tmp
    · subst hy
      simp only [Function.update_same, Function.update_noteq h2t, List.replicate_zero,
        List.nil_append, Function.update_noteq (Ne.symm h2t)]
    · by_cases hz : y = acc
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same, List.replicate_zero,
          List.nil_append, Function.update_noteq (Ne.symm h2a)]
      · by_cases hw : y = m2
        · subst hw
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
            Function.update_idem]
        · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw]
  | succ b ih =>
    have hm2' : st m2 = true :: (List.replicate b true ++ false :: restB) := by
      rw [hm2, List.replicate_succ, List.cons_append]
    have s1 : step P ⟨emb .inner,inp,st⟩
        = some ⟨emb .toAcc,inp,Function.update st m2
          (List.replicate b true ++ false :: restB)⟩ := by
      simp [step, hP, mulCode, hm2']
    have s2 : ∀ u : Fin k → List Bool, step P ⟨emb .toAcc,inp,u⟩
        = some ⟨emb .toTmp,inp,Function.update u acc (true :: u acc)⟩ := by
      intro u; simp [step, hP, mulCode]
    have s3 : ∀ u : Fin k → List Bool, step P ⟨emb .toTmp,inp,u⟩
        = some ⟨emb .inner,inp,Function.update u tmp (true :: u tmp)⟩ := by
      intro u; simp [step, hP, mulCode]
    have he : 3*(b+1)+2 = 1+(1+(1+(3*b+2))) := by ring
    rw [he, iter_step' P s1, iter_step' P (s2 _), iter_step' P (s3 _)]
    have e1 : (Function.update st m2 (List.replicate b true ++ false :: restB)) acc = st acc := by
      simp only [Function.update_noteq (Ne.symm h2a)]
    have e2 : (Function.update (Function.update st m2 (List.replicate b true ++ false :: restB))
        acc (true :: st acc)) tmp = st tmp := by
      simp only [Function.update_noteq (Ne.symm hat), Function.update_noteq (Ne.symm h2t)]
    rw [e1, e2]
    rw [ih (Function.update (Function.update
        (Function.update st m2 (List.replicate b true ++ false :: restB)) acc (true :: st acc))
        tmp (true :: st tmp))
      (by simp [Function.update_noteq h2t, Function.update_noteq h2a, Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = tmp
    · subst hy
      simp only [Function.update_same, Function.update_noteq hat, Function.update_noteq h2t,
        Function.update_idem, List.replicate_succ, List.cons_append]
      rw [replicate_cons]
    · by_cases hz : y = acc
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same, Function.update_noteq h2a,
          Function.update_idem, List.replicate_succ, List.cons_append]
        rw [replicate_cons]
      · by_cases hw : y = m2
        · subst hw
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
            Function.update_idem]
        · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw]

/-- The scratch stack is poured back onto the multiplicand. -/
theorem mul_restore (b : Nat) (inp : List Bool) (st : Fin k → List Bool)
    (htmp : st tmp = List.replicate b true) :
    iter P (2*b+1) ⟨emb .back,inp,st⟩
      = ⟨emb .loop,inp,Function.update (Function.update st tmp [])
          m2 (List.replicate b true ++ st m2)⟩ := by
  induction b generalizing st with
  | zero =>
    simp only [List.replicate_zero] at htmp
    have s1 : step P ⟨emb .back,inp,st⟩ = some ⟨emb .loop,inp,st⟩ := by
      simp [step, hP, mulCode, htmp]
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [iter_one P s1]
    congr 1
    funext y
    by_cases hy : y = m2
    · subst hy
      simp only [Function.update_same, Function.update_noteq (Ne.symm h2t), List.replicate_zero,
        List.nil_append]
    · by_cases hz : y = tmp
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same, htmp]
      · simp only [Function.update_noteq hy, Function.update_noteq hz]
  | succ b ih =>
    have htmp' : st tmp = true :: List.replicate b true := by
      rw [htmp, List.replicate_succ]
    have s1 : step P ⟨emb .back,inp,st⟩
        = some ⟨emb .backPush,inp,Function.update st tmp (List.replicate b true)⟩ := by
      simp [step, hP, mulCode, htmp']
    have s2 : ∀ u : Fin k → List Bool, step P ⟨emb .backPush,inp,u⟩
        = some ⟨emb .back,inp,Function.update u m2 (true :: u m2)⟩ := by
      intro u; simp [step, hP, mulCode]
    have he : 2*(b+1)+1 = 1+(1+(2*b+1)) := by ring
    rw [he, iter_step' P s1, iter_step' P (s2 _)]
    have e1 : (Function.update st tmp (List.replicate b true)) m2 = st m2 := by
      simp only [Function.update_noteq h2t]
    rw [e1]
    rw [ih (Function.update (Function.update st tmp (List.replicate b true)) m2 (true :: st m2))
      (by simp [Function.update_noteq (Ne.symm h2t), Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = m2
    · subst hy
      simp only [Function.update_same, Function.update_noteq h2t, Function.update_idem,
        List.replicate_succ, List.cons_append]
      rw [replicate_cons]
    · by_cases hz : y = tmp
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same, Function.update_idem]
      · simp only [Function.update_noteq hy, Function.update_noteq hz]

include h12 h1a h1t

def mulTime (a b : Nat) : Nat := a*(5*b+4)+1

/-- `a` copies of `b` land on the accumulator; the multiplier is consumed, the
multiplicand and the scratch stack come back as they were. -/
theorem mul_component (a b : Nat) (inp : List Bool) (st : Fin k → List Bool)
    (restA restB : List Bool)
    (hm1 : st m1 = List.replicate a true ++ false :: restA)
    (hm2 : st m2 = List.replicate b true ++ false :: restB)
    (htmp : st tmp = []) :
    iter P (mulTime a b) ⟨emb .loop,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st m1 restA) acc
          (List.replicate (a*b) true ++ st acc)⟩ := by
  induction a generalizing st with
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at hm1
    have s1 : step P ⟨emb .loop,inp,st⟩ = some ⟨exit,inp,Function.update st m1 restA⟩ := by
      simp [step, hP, mulCode, hm1]
    simp only [mulTime, Nat.zero_mul, Nat.zero_add]
    rw [iter_one P s1]
    congr 1
    funext y
    by_cases hy : y = acc
    · subst hy
      simp only [Function.update_same, Function.update_noteq (Ne.symm h1a), List.replicate_zero,
        Nat.zero_mul, List.nil_append]
    · by_cases hz : y = m1
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same]
      · simp only [Function.update_noteq hy, Function.update_noteq hz]
  | succ a ih =>
    have hm1' : st m1 = true :: (List.replicate a true ++ false :: restA) := by
      rw [hm1, List.replicate_succ, List.cons_append]
    have s1 : step P ⟨emb .loop,inp,st⟩
        = some ⟨emb .inner,inp,Function.update st m1
          (List.replicate a true ++ false :: restA)⟩ := by
      simp [step, hP, mulCode, hm1']
    have he : mulTime (a+1) b = 1+((3*b+2)+((2*b+1)+mulTime a b)) := by
      simp only [mulTime]; ring
    rw [he, iter_step' P s1, iter_add]
    rw [mul_sweep P m1 m2 acc tmp h2a h2t hat emb exit fail hP b inp
      (Function.update st m1 (List.replicate a true ++ false :: restA)) restB
      (by simp [Function.update_noteq (Ne.symm h12), hm2])]
    simp only [Function.update_noteq (Ne.symm h1a), Function.update_noteq (Ne.symm h1t), htmp,
      List.append_nil]
    rw [iter_add]
    rw [mul_restore P m1 m2 acc tmp h2a h2t hat emb exit fail hP b inp
      (Function.update (Function.update (Function.update
        (Function.update st m1 (List.replicate a true ++ false :: restA)) m2 (false :: restB))
        acc (List.replicate b true ++ st acc)) tmp (List.replicate b true))
      (by simp [Function.update_same])]
    have em2 : (Function.update (Function.update (Function.update
        (Function.update st m1 (List.replicate a true ++ false :: restA)) m2 (false :: restB))
        acc (List.replicate b true ++ st acc)) tmp (List.replicate b true)) m2
        = false :: restB := by
      simp [Function.update_noteq h2t, Function.update_noteq h2a, Function.update_same]
    rw [em2]
    rw [ih (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update st m1 (List.replicate a true ++ false :: restA)) m2 (false :: restB))
        acc (List.replicate b true ++ st acc)) tmp (List.replicate b true)) tmp []) m2
        (List.replicate b true ++ false :: restB))
      (by
        simp [Function.update_noteq h12, Function.update_noteq h1t, Function.update_noteq h1a,
          Function.update_noteq (Ne.symm h12), Function.update_same])
      (by simp [Function.update_same])
      (by simp [Function.update_noteq (Ne.symm h2t), Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = acc
    · subst hy
      simp only [Function.update_noteq (Ne.symm h2a), Function.update_noteq hat,
        Function.update_same, Function.update_noteq (Ne.symm h1a), Function.update_idem]
      rw [← List.append_assoc, ← List.replicate_add]
      congr 2
      ring
    · by_cases hz : y = m1
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same, Function.update_noteq h12,
          Function.update_noteq h1t, Function.update_noteq h1a, Function.update_idem]
      · by_cases hw : y = m2
        · subst hw
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
            Function.update_noteq h2t, Function.update_noteq h2a, hm2,
            Function.update_idem, Function.update_noteq (Ne.symm h12)]
        · by_cases hv : y = tmp
          · subst hv
            simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
              Function.update_same, htmp]
          · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
              Function.update_noteq hv]

end Mul


/-! ## The pair index

A product automaton numbers the pair `(p,q)` by `p*n+q`. With the multiplier of
the previous section and a scaling by one — which is just "move the markers,
consume the separator" — that index is built on the accumulator by running two
components in sequence. This packages them, and is the innermost step of the
product construction.
-/

inductive IdxSt
  | mul (x : MulSt)
  | add (x : SSt)
  deriving DecidableEq

def indexCode (p n q acc tmp : Fin k) (emb : IdxSt → Q) (exit fail : Q) : IdxSt → Instr Q k
  | .mul x => mulCode p n acc tmp (fun t => emb (.mul t)) (emb (.add .loop)) fail x
  | .add x => scaleCode 1 q acc (fun t => emb (.add t)) exit x

def indexTime (a b c : Nat) : Nat := mulTime a b+(c*(1+2)+1)

theorem index_component (P : Q → Instr Q k) (p n q acc tmp : Fin k)
    (hpn : p ≠ n) (hpa : p ≠ acc) (hpt : p ≠ tmp)
    (hna : n ≠ acc) (hnt : n ≠ tmp) (hat : acc ≠ tmp) (hqa : q ≠ acc)
    (emb : IdxSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = indexCode p n q acc tmp emb exit fail s)
    (a b c : Nat) (inp : List Bool) (st : Fin k → List Bool) (restP restN restQ : List Bool)
    (hp : st p = List.replicate a true ++ false :: restP)
    (hn : st n = List.replicate b true ++ false :: restN)
    (hq : st q = List.replicate c true ++ false :: restQ)
    (htmp : st tmp = [])
    (hqp : q ≠ p) (hqt : q ≠ tmp) :
    iter P (indexTime a b c) ⟨emb (.mul .loop),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st p restP) q restQ) acc
          (List.replicate c true ++ (List.replicate (a*b) true ++ st acc))⟩ := by
  unfold indexTime
  rw [iter_add]
  rw [mul_component P p n acc tmp hpn hpa hpt hna hnt hat (fun t => emb (.mul t))
    (emb (.add .loop)) fail (fun s => by rw [hP (.mul s)]; rfl) a b inp st restP restN
    hp hn htmp]
  rw [scale_component P 1 q acc hqa (fun t => emb (.add t)) exit
    (fun s => by rw [hP (.add s)]; rfl) c inp
    (Function.update (Function.update st p restP) acc (List.replicate (a*b) true ++ st acc))
    restQ
    (by simp [Function.update_noteq hqa, Function.update_noteq hqp, hq])]
  congr 1
  funext y
  by_cases hy : y = acc
  · subst hy
    simp only [Function.update_same, Function.update_noteq (Ne.symm hqa), Nat.mul_one,
      Function.update_idem]
  · by_cases hz : y = q
    · subst hz
      simp only [Function.update_noteq hy, Function.update_same, Function.update_noteq hy,
        Function.update_noteq hqp]
    · by_cases hw : y = p
      · subst hw
        simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
          Function.update_noteq hy]
      · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw]


/-! ## Reading one entry and putting the table back

The composite the constructions actually call: look up entry number `i` of a
table, leave its value as a counter on a stack of its own, and restore the table
exactly. It is `skip`, then `copy`, then a `move` of the scanned part back.
-/

inductive ReadSt
  | sk (x : KSt)
  | cp (x : DSt)
  | mv (x : MSt)
  deriving DecidableEq

def readCode (idx tab tmp out : Fin k) (emb : ReadSt → Q) (exit fail : Q) : ReadSt → Instr Q k
  | .sk x => skipCode idx tab tmp (fun t => emb (.sk t)) (emb (.cp .loop)) fail x
  | .cp x => copyCode tab out tmp (fun t => emb (.cp t)) (emb (.mv .loop)) fail x
  | .mv x => moveCode tmp tab (fun t => emb (.mv t)) exit x

def readTime (pre : List Nat) (e : Nat) : Nat :=
  (3*pre.length+2*pre.sum+1)+((3*e+2)+(2*(1+e+(blocks pre).length)+1))

theorem read_component (P : Q → Instr Q k) (idx tab tmp out : Fin k)
    (hit : idx ≠ tab) (him : idx ≠ tmp) (hio : idx ≠ out)
    (htm : tab ≠ tmp) (hto : tab ≠ out) (hmo : tmp ≠ out)
    (emb : ReadSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = readCode idx tab tmp out emb exit fail s)
    (pre : List Nat) (e : Nat) (post : List Bool) (A : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hidx : st idx = List.replicate pre.length true ++ false :: A)
    (htab : st tab = blocks pre ++ (List.replicate e true ++ false :: post))
    (htmp : st tmp = []) :
    iter P (readTime pre e) ⟨emb (.sk .loop),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st idx A) out
          (List.replicate e true ++ st out)) tab (st tab)⟩ := by
  unfold readTime
  rw [iter_add]
  rw [skip_component P idx tab tmp hit him htm (fun t => emb (.sk t)) (emb (.cp .loop)) fail
    (fun s => by rw [hP (.sk s)]; rfl) pre inp st A (List.replicate e true ++ false :: post)
    hidx htab]
  simp only [htmp, List.append_nil]
  rw [iter_add]
  rw [copy_component P tab out tmp hto htm (Ne.symm hmo) (fun t => emb (.cp t)) (emb (.mv .loop)) fail
    (fun s => by rw [hP (.cp s)]; rfl) e inp
    (Function.update (Function.update (Function.update st idx A) tab
      (List.replicate e true ++ false :: post)) tmp ((blocks pre).reverse)) post
    (by simp [Function.update_noteq htm, Function.update_same])]
  rw [show 2*(1+e+(blocks pre).length)+1
      = 2*(false :: (List.replicate e true ++ (blocks pre).reverse)).length+1 from by
    simp; omega]
  rw [move_component P tmp tab (Ne.symm htm) (fun t => emb (.mv t)) exit
    (fun s => by rw [hP (.mv s)]; rfl)
    (false :: (List.replicate e true ++ (blocks pre).reverse)) inp _
    (by simp [Function.update_same])]
  congr 1
  funext y
  by_cases hy : y = tab
  · subst hy
    simp only [Function.update_same, Function.update_noteq (Ne.symm htm),
      Function.update_noteq hto, Function.update_noteq htm, Function.update_noteq hit,
      Function.update_idem, List.reverse_cons, List.reverse_append, List.reverse_replicate,
      List.reverse_reverse, List.append_assoc, List.singleton_append, htab]
  · by_cases hz : y = tmp
    · subst hz
      simp only [Function.update_noteq hy, Function.update_same, Function.update_idem,
        Function.update_noteq hmo, Function.update_noteq (Ne.symm him), htmp]
    · by_cases hw : y = out
      · subst hw
        simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
          Function.update_noteq hmo, Function.update_idem, Function.update_noteq (Ne.symm hio)]
      · by_cases hv : y = idx
        · subst hv
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
            Function.update_same, Function.update_idem]
        · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
            Function.update_noteq hv]


/-! ## Duplicating a stack

A counter that is read twice — the state `p` of the first automaton is needed
for both of its transitions — has to be copied first. Moving it to a scratch
stack reverses it; pouring the scratch stack back onto the original and onto a
second one gives two copies in the original order.
-/

inductive DupSt
  | up (x : MSt)
  | down (x : PSt)
  deriving DecidableEq

def dupCode (src tmp dst : Fin k) (emb : DupSt → Q) (exit : Q) : DupSt → Instr Q k
  | .up x => moveCode src tmp (fun t => emb (.up t)) (emb (.down .loop)) x
  | .down x => pourCode tmp src dst (fun t => emb (.down t)) exit x

def dupTime (S : List Bool) : Nat := (2*S.length+1)+(3*S.length+1)

theorem dup_component (P : Q → Instr Q k) (src tmp dst : Fin k)
    (hst : src ≠ tmp) (hsd : src ≠ dst) (htd : tmp ≠ dst)
    (emb : DupSt → Q) (exit : Q)
    (hP : ∀ s, P (emb s) = dupCode src tmp dst emb exit s)
    (S : List Bool) (inp : List Bool) (st : Fin k → List Bool)
    (hsrc : st src = S) (htmp : st tmp = []) :
    iter P (dupTime S) ⟨emb (.up .loop),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st dst (S ++ st dst)) tmp []⟩ := by
  unfold dupTime
  rw [iter_add]
  rw [move_component P src tmp hst (fun t => emb (.up t)) (emb (.down .loop))
    (fun s => by rw [hP (.up s)]; rfl) S inp st hsrc]
  rw [show 3*S.length+1 = 3*(S.reverse ++ st tmp).length+1 from by simp [htmp]]
  rw [pour_component P tmp src dst (Ne.symm hst) htd hsd (fun t => emb (.down t)) exit
    (fun s => by rw [hP (.down s)]; rfl) (S.reverse ++ st tmp) inp _
    (by simp [Function.update_same])]
  congr 1
  funext y
  by_cases hy : y = dst
  · subst hy
    simp only [Function.update_same, Function.update_noteq (Ne.symm htd),
      Function.update_noteq (Ne.symm hsd), htmp, List.append_nil, List.reverse_reverse]
  · by_cases hz : y = src
    · subst hz
      simp only [Function.update_noteq hy, Function.update_same, Function.update_noteq hst,
        Function.update_noteq (Ne.symm hst), htmp, List.append_nil, List.reverse_reverse,
        Function.update_idem, hsrc]
    · by_cases hw : y = tmp
      · subst hw
        simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
          Function.update_idem]
      · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw]


/-! ## The index of a state's entry block

With three entries per state, the entries of state `a` start at `3a`. This
composite builds that index on a stack of its own — separator first, so the
lookup can consume it — while leaving the state counter where it was.
-/

inductive TripleSt
  | sep
  | dup (x : DupSt)
  | mul (x : SSt)
  deriving DecidableEq

def tripleCode (src tmp cpy idx : Fin k) (emb : TripleSt → Q) (exit : Q) : TripleSt → Instr Q k
  | .sep => .push idx false (emb (.dup (.up .loop)))
  | .dup x => dupCode src tmp cpy (fun t => emb (.dup t)) (emb (.mul .loop)) x
  | .mul x => scaleCode 3 cpy idx (fun t => emb (.mul t)) exit x

def tripleTime (a : Nat) : Nat := 1+(dupTime (List.replicate a true ++ [false])+(a*(3+2)+1))

theorem triple_component (P : Q → Instr Q k) (src tmp cpy idx : Fin k)
    (hst : src ≠ tmp) (hsc : src ≠ cpy) (hsi : src ≠ idx)
    (htc : tmp ≠ cpy) (hti : tmp ≠ idx) (hci : cpy ≠ idx)
    (emb : TripleSt → Q) (exit : Q)
    (hP : ∀ s, P (emb s) = tripleCode src tmp cpy idx emb exit s)
    (a : Nat) (inp : List Bool) (st : Fin k → List Bool)
    (hsrc : st src = List.replicate a true ++ [false]) (htmp : st tmp = []) :
    iter P (tripleTime a) ⟨emb .sep,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st tmp [])
          idx (List.replicate (3*a) true ++ false :: st idx)⟩ := by
  unfold tripleTime
  have s1 : step P ⟨emb .sep,inp,st⟩
      = some ⟨emb (.dup (.up .loop)),inp,Function.update st idx (false :: st idx)⟩ := by
    simp [step, hP, tripleCode]
  rw [iter_step' P s1, iter_add]
  rw [dup_component P src tmp cpy hst hsc htc (fun t => emb (.dup t)) (emb (.mul .loop))
    (fun s => by rw [hP (.dup s)]; rfl) (List.replicate a true ++ [false]) inp
    (Function.update st idx (false :: st idx))
    (by simp [Function.update_noteq hsi, hsrc])
    (by simp [Function.update_noteq hti, htmp])]
  rw [scale_component P 3 cpy idx hci (fun t => emb (.mul t)) exit
    (fun s => by rw [hP (.mul s)]; rfl) a inp
    (Function.update (Function.update (Function.update st idx (false :: st idx)) cpy
      (List.replicate a true ++ [false] ++ (Function.update st idx (false :: st idx)) cpy)) tmp [])
    ((Function.update st idx (false :: st idx)) cpy)
    (by
      simp [Function.update_noteq (Ne.symm htc), Function.update_same])]
  congr 1
  funext y
  by_cases hy : y = idx
  · subst hy
    simp only [Function.update_same, Function.update_noteq (Ne.symm hci),
      Function.update_noteq (Ne.symm hti), Function.update_idem, List.append_assoc,
      List.singleton_append, Nat.mul_comm]
  · by_cases hz : y = tmp
    · subst hz
      simp only [Function.update_noteq hy, Function.update_noteq htc, Function.update_same,
        Function.update_idem]
    · by_cases hw : y = cpy
      · subst hw
        simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
          Function.update_noteq hci, Function.update_idem]
      · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw]


/-! ## Reading one transition

Putting the last three composites together: from a state counter and a bit, the
machine builds the entry index `3a+b`, looks that entry up and leaves its value
as a counter, with the table and the state counter exactly as they were. This is
what both the product construction and any simulation of a stored automaton call.
-/

inductive TransSt
  | tri (x : TripleSt)
  | bump
  | rd (x : ReadSt)
  deriving DecidableEq

def transCode (bit : Bool) (src tmp cpy idx tab out : Fin k)
    (emb : TransSt → Q) (exit fail : Q) : TransSt → Instr Q k
  | .tri x =>
    tripleCode src tmp cpy idx (fun t => emb (.tri t))
      (if bit then emb .bump else emb (.rd (.sk .loop))) x
  | .bump => .push idx true (emb (.rd (.sk .loop)))
  | .rd x => readCode idx tab tmp out (fun t => emb (.rd t)) exit fail x

def transTime (bit : Bool) (a : Nat) (pre : List Nat) (e : Nat) : Nat :=
  tripleTime a+((if bit then 1 else 0)+readTime pre e)

theorem trans_component (P : Q → Instr Q k) (bit : Bool) (src tmp cpy idx tab out : Fin k)
    (hst : src ≠ tmp) (hsc : src ≠ cpy) (hsi : src ≠ idx)
    (htc : tmp ≠ cpy) (hti : tmp ≠ idx) (hci : cpy ≠ idx)
    (hit : idx ≠ tab) (hio : idx ≠ out) (htt : tab ≠ tmp) (hto : tab ≠ out) (hmo : tmp ≠ out)
    (emb : TransSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = transCode bit src tmp cpy idx tab out emb exit fail s)
    (a : Nat) (pre : List Nat) (e : Nat) (post : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hsrc : st src = List.replicate a true ++ [false]) (htmp : st tmp = []) (hidx : st idx = [])
    (htab : st tab = blocks pre ++ (List.replicate e true ++ false :: post))
    (hlen : pre.length = 3*a+(if bit then 1 else 0)) :
    iter P (transTime bit a pre e) ⟨emb (.tri .sep),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st tmp []) out
          (List.replicate e true ++ st out)) tab (st tab)⟩ := by
  unfold transTime
  rw [iter_add]
  rw [triple_component P src tmp cpy idx hst hsc hsi htc hti hci (fun t => emb (.tri t))
    (if bit then emb .bump else emb (.rd (.sk .loop)))
    (fun s => by rw [hP (.tri s)]; rfl) a inp st hsrc htmp]
  cases bit with
  | false =>
    rw [show (if (false : Bool) = true then 1 else 0) = 0 from rfl, Nat.zero_add,
      show (if (false : Bool) = true then emb TransSt.bump
          else emb (TransSt.rd (ReadSt.sk KSt.loop))) = emb (TransSt.rd (ReadSt.sk KSt.loop))
        from rfl]
    rw [read_component P idx tab tmp out hit (Ne.symm hti) hio htt hto hmo
      (fun t => emb (.rd t)) exit fail (fun s => by rw [hP (.rd s)]; rfl) pre e post []
      inp (Function.update (Function.update st tmp []) idx
        (List.replicate (3*a) true ++ false :: st idx))
      (by
        simp [Function.update_same, hidx, hlen])
      (by
        simp [Function.update_noteq (Ne.symm hit), Function.update_noteq htt, htab])
      (by simp [Function.update_noteq hti, Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = tab
    · subst hy
      simp only [Function.update_same, Function.update_noteq hto,
        Function.update_noteq (Ne.symm hit), Function.update_noteq htt, Function.update_idem]
    · by_cases hz : y = out
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same,
          Function.update_noteq (Ne.symm hio), Function.update_noteq (Ne.symm hmo),
          Function.update_idem]
      · by_cases hw : y = idx
        · subst hw
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
            Function.update_noteq (Ne.symm hti), hidx, Function.update_idem]
        · by_cases hv : y = tmp
          · subst hv
            simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
              Function.update_same, Function.update_idem]
          · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
              Function.update_noteq hv]
  | true =>
    rw [show (if (true : Bool) = true then 1 else 0) = 1 from rfl,
      show (if (true : Bool) = true then emb TransSt.bump
          else emb (TransSt.rd (ReadSt.sk KSt.loop))) = emb TransSt.bump from rfl]
    have s1 : step P ⟨emb .bump,inp,Function.update (Function.update st tmp []) idx
        (List.replicate (3*a) true ++ false :: st idx)⟩
        = some ⟨emb (.rd (.sk .loop)),inp,Function.update (Function.update (Function.update st tmp [])
          idx (List.replicate (3*a) true ++ false :: st idx)) idx
          (true :: (List.replicate (3*a) true ++ false :: st idx))⟩ := by
      simp [step, hP, transCode, Function.update_same]
    rw [iter_step' P s1]
    rw [read_component P idx tab tmp out hit (Ne.symm hti) hio htt hto hmo
      (fun t => emb (.rd t)) exit fail (fun s => by rw [hP (.rd s)]; rfl) pre e post []
      inp (Function.update (Function.update (Function.update st tmp []) idx
        (List.replicate (3*a) true ++ false :: st idx)) idx
        (true :: (List.replicate (3*a) true ++ false :: st idx)))
      (by
        simp [Function.update_same, hidx, hlen, List.replicate_succ])
      (by
        simp [Function.update_noteq (Ne.symm hit), Function.update_noteq htt, htab])
      (by simp [Function.update_noteq hti, Function.update_same])]
    congr 1
    funext y
    by_cases hy : y = tab
    · subst hy
      simp only [Function.update_same, Function.update_noteq hto,
        Function.update_noteq (Ne.symm hit), Function.update_noteq htt, Function.update_idem]
    · by_cases hz : y = out
      · subst hz
        simp only [Function.update_noteq hy, Function.update_same,
          Function.update_noteq (Ne.symm hio), Function.update_noteq (Ne.symm hmo),
          Function.update_idem]
      · by_cases hw : y = idx
        · subst hw
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
            Function.update_noteq (Ne.symm hti), hidx, Function.update_idem]
        · by_cases hv : y = tmp
          · subst hv
            simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
              Function.update_same, Function.update_idem]
          · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
              Function.update_noteq hv]


/-! ## One step of the product automaton

The inner body of the product construction. Two stored automata are advanced by
the same bit, and the two successors are packed into one product index
`d1*n+d2`. Eleven stacks take part, so instead of listing the distinctness
hypotheses pairwise they are given by one injective assignment `v : Fin 16 → Fin k`:

    0 = first state counter    1 = second state counter
    2 = first table            3 = second table
    4 = the second automaton's size
    5 = the accumulator
    6, 7, 8 = scratch (empty on entry, empty on exit)
    9, 10 = the two successors
    11 = the output table      12, 13 = the two loop counters
    14, 15 = spare

The domain is `Fin 16` from the start so that later stages of the construction
can use the same assignment without renumbering.
-/

theorem vne {n : Nat} {v : Fin n → Fin k} (h : Function.Injective v) {i j : Fin n}
    (hij : i ≠ j) : v i ≠ v j := fun e => hij (h e)

inductive PairSt
  | t1 (x : TransSt)
  | t2 (x : TransSt)
  | ix (x : IdxSt)
  deriving DecidableEq

def pairCode (bit : Bool) (v : Fin 16 → Fin k) (emb : PairSt → Q) (exit fail : Q) :
    PairSt → Instr Q k
  | .t1 x =>
    transCode bit (v 0) (v 6) (v 7) (v 8) (v 2) (v 9) (fun t => emb (.t1 t))
      (emb (.t2 (.tri .sep))) fail x
  | .t2 x =>
    transCode bit (v 1) (v 6) (v 7) (v 8) (v 3) (v 10) (fun t => emb (.t2 t))
      (emb (.ix (.mul .loop))) fail x
  | .ix x => indexCode (v 9) (v 4) (v 10) (v 5) (v 6) (fun t => emb (.ix t)) exit fail x

def pairTime (bit : Bool) (a1 : Nat) (pre1 : List Nat) (e1 : Nat)
    (a2 : Nat) (pre2 : List Nat) (e2 : Nat) (nv : Nat) : Nat :=
  transTime bit a1 pre1 e1+(transTime bit a2 pre2 e2+indexTime e1 nv e2)

theorem pair_component (P : Q → Instr Q k) (bit : Bool) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : PairSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = pairCode bit v emb exit fail s)
    (a1 a2 nv e1 e2 : Nat) (pre1 pre2 : List Nat) (post1 post2 restN : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hp : st (v 0) = List.replicate a1 true ++ [false])
    (hq : st (v 1) = List.replicate a2 true ++ [false])
    (ht1 : st (v 2) = blocks pre1 ++ (List.replicate e1 true ++ false :: post1))
    (ht2 : st (v 3) = blocks pre2 ++ (List.replicate e2 true ++ false :: post2))
    (hn : st (v 4) = List.replicate nv true ++ false :: restN)
    (htmp : st (v 6) = []) (hidx : st (v 8) = [])
    (ho1 : st (v 9) = [false]) (ho2 : st (v 10) = [false])
    (hl1 : pre1.length = 3*a1+(if bit then 1 else 0))
    (hl2 : pre2.length = 3*a2+(if bit then 1 else 0)) :
    iter P (pairTime bit a1 pre1 e1 a2 pre2 e2 nv) ⟨emb (.t1 (.tri .sep)),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st (v 9) []) (v 10) [])
          (v 5) (List.replicate e2 true ++ (List.replicate (e1*nv) true ++ st (v 5)))⟩ := by
  unfold pairTime
  rw [iter_add]
  rw [trans_component P bit (v 0) (v 6) (v 7) (v 8) (v 2) (v 9)
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (fun t => emb (.t1 t)) (emb (.t2 (.tri .sep))) fail
    (fun s => by rw [hP (.t1 s)]; rfl) a1 pre1 e1 post1 inp st hp htmp hidx ht1 hl1]
  have hst1 : Function.update (Function.update (Function.update st (v 6) []) (v 9)
      (List.replicate e1 true ++ st (v 9))) (v 2) (st (v 2))
      = Function.update st (v 9) (List.replicate e1 true ++ [false]) := by
    funext y
    by_cases h2 : y = v 2
    · subst h2
      simp only [Function.update_same, Function.update_noteq (vne hv (by decide) : v 2 ≠ v 9)]
    · by_cases h9 : y = v 9
      · subst h9
        simp only [Function.update_noteq h2, Function.update_same, ho1]
      · by_cases h6 : y = v 6
        · subst h6
          simp only [Function.update_noteq h2, Function.update_noteq h9, Function.update_same,
            Function.update_noteq h9, htmp]
        · simp only [Function.update_noteq h2, Function.update_noteq h9, Function.update_noteq h6]
  rw [hst1]
  rw [iter_add]
  rw [trans_component P bit (v 1) (v 6) (v 7) (v 8) (v 3) (v 10)
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (fun t => emb (.t2 t)) (emb (.ix (.mul .loop))) fail
    (fun s => by rw [hP (.t2 s)]; rfl) a2 pre2 e2 post2 inp
    (Function.update st (v 9) (List.replicate e1 true ++ [false]))
    (by rw [Function.update_noteq (vne hv (by decide) : v 1 ≠ v 9), hq])
    (by rw [Function.update_noteq (vne hv (by decide) : v 6 ≠ v 9), htmp])
    (by rw [Function.update_noteq (vne hv (by decide) : v 8 ≠ v 9), hidx])
    (by rw [Function.update_noteq (vne hv (by decide) : v 3 ≠ v 9), ht2]) hl2]
  have hst2 : Function.update (Function.update (Function.update
      (Function.update st (v 9) (List.replicate e1 true ++ [false])) (v 6) []) (v 10)
      (List.replicate e2 true ++ Function.update st (v 9)
        (List.replicate e1 true ++ [false]) (v 10)))
      (v 3) (Function.update st (v 9) (List.replicate e1 true ++ [false]) (v 3))
      = Function.update (Function.update st (v 9) (List.replicate e1 true ++ [false]))
          (v 10) (List.replicate e2 true ++ [false]) := by
    have h109 : (v 10) ≠ (v 9) := vne hv (by decide)
    funext y
    by_cases h3 : y = v 3
    · subst h3
      simp only [Function.update_same, Function.update_noteq (vne hv (by decide) : v 3 ≠ v 10)]
    · by_cases h10 : y = v 10
      · subst h10
        simp only [Function.update_noteq h3, Function.update_same,
          Function.update_noteq h109, ho2]
      · by_cases h6 : y = v 6
        · subst h6
          simp only [Function.update_noteq h3, Function.update_noteq h10, Function.update_same,
            Function.update_noteq (vne hv (by decide) : v 6 ≠ v 9), htmp]
        · simp only [Function.update_noteq h3, Function.update_noteq h10, Function.update_noteq h6]
  rw [hst2]
  rw [index_component P (v 9) (v 4) (v 10) (v 5) (v 6)
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (fun t => emb (.ix t)) exit fail (fun s => by rw [hP (.ix s)]; rfl) e1 nv e2 inp
    (Function.update (Function.update st (v 9) (List.replicate e1 true ++ [false]))
      (v 10) (List.replicate e2 true ++ [false])) [] restN []
    (by
      rw [Function.update_noteq (vne hv (by decide) : v 9 ≠ v 10), Function.update_same])
    (by
      rw [Function.update_noteq (vne hv (by decide) : v 4 ≠ v 10),
        Function.update_noteq (vne hv (by decide) : v 4 ≠ v 9), hn])
    (by rw [Function.update_same])
    (by
      rw [Function.update_noteq (vne hv (by decide) : v 6 ≠ v 10),
        Function.update_noteq (vne hv (by decide) : v 6 ≠ v 9), htmp])
    (vne hv (by decide)) (vne hv (by decide))]
  congr 1
  funext y
  by_cases h5 : y = v 5
  · subst h5
    simp only [Function.update_same, Function.update_noteq (vne hv (by decide) : v 5 ≠ v 10),
      Function.update_noteq (vne hv (by decide) : v 5 ≠ v 9)]
  · by_cases h10 : y = v 10
    · subst h10
      simp only [Function.update_noteq h5, Function.update_same]
    · by_cases h9 : y = v 9
      · subst h9
        simp only [Function.update_noteq h5, Function.update_noteq h10, Function.update_same]
      · simp only [Function.update_noteq h5, Function.update_noteq h10, Function.update_noteq h9]


/-! ## Reading an arbitrary entry of a state's block

The generalisation of `transCode`: with three entries per state, entry `off` of
state `a` sits at `3a+off`, so the successors are `off = 0, 1` and the accepting
flag is `off = 2`. The offset is pushed one marker at a time by a small chain of
states, which is why the state type carries a `Nat`.
-/

inductive EntrySt
  | tri (x : TripleSt)
  | bump (j : Nat)
  | rd (x : ReadSt)
  deriving DecidableEq

def entryCode (off : Nat) (src tmp cpy idx tab out : Fin k)
    (emb : EntrySt → Q) (exit fail : Q) : EntrySt → Instr Q k
  | .tri x => tripleCode src tmp cpy idx (fun t => emb (.tri t)) (emb (.bump off)) x
  | .bump 0 => .nop (emb (.rd (.sk .loop)))
  | .bump (j+1) => .push idx true (emb (.bump j))
  | .rd x => readCode idx tab tmp out (fun t => emb (.rd t)) exit fail x

def entryTime (off : Nat) (a : Nat) (pre : List Nat) (e : Nat) : Nat :=
  tripleTime a+((off+1)+readTime pre e)

theorem bump_run (P : Q → Instr Q k) (off : Nat) (src tmp cpy idx tab out : Fin k)
    (emb : EntrySt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = entryCode off src tmp cpy idx tab out emb exit fail s)
    (j : Nat) (inp : List Bool) (st : Fin k → List Bool) :
    iter P (j+1) ⟨emb (.bump j),inp,st⟩
      = ⟨emb (.rd (.sk .loop)),inp,Function.update st idx (List.replicate j true ++ st idx)⟩ := by
  induction j generalizing st with
  | zero =>
    rw [iter_one P (c' := ⟨emb (.rd (.sk .loop)),inp,st⟩)
      (by simp [step, hP (.bump 0), entryCode])]
    simp [List.replicate, Function.update_eq_self]
  | succ j ih =>
    rw [Nat.add_comm (j+1) 1]
    rw [iter_step' P (c' := ⟨emb (.bump j),inp,Function.update st idx (true :: st idx)⟩)
      (by simp [step, hP (.bump (j+1)), entryCode])]
    rw [ih]
    simp only [Function.update_same, Function.update_idem, List.replicate_succ,
      List.cons_append, replicate_cons]

theorem entry_component (P : Q → Instr Q k) (off : Nat) (src tmp cpy idx tab out : Fin k)
    (hst : src ≠ tmp) (hsc : src ≠ cpy) (hsi : src ≠ idx)
    (htc : tmp ≠ cpy) (hti : tmp ≠ idx) (hci : cpy ≠ idx)
    (hit : idx ≠ tab) (hio : idx ≠ out) (htt : tab ≠ tmp) (hto : tab ≠ out) (hmo : tmp ≠ out)
    (emb : EntrySt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = entryCode off src tmp cpy idx tab out emb exit fail s)
    (a : Nat) (pre : List Nat) (e : Nat) (post : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hsrc : st src = List.replicate a true ++ [false]) (htmp : st tmp = []) (hidx : st idx = [])
    (htab : st tab = blocks pre ++ (List.replicate e true ++ false :: post))
    (hlen : pre.length = 3*a+off) :
    iter P (entryTime off a pre e) ⟨emb (.tri .sep),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st tmp []) out
          (List.replicate e true ++ st out)) tab (st tab)⟩ := by
  unfold entryTime
  rw [iter_add]
  rw [triple_component P src tmp cpy idx hst hsc hsi htc hti hci (fun t => emb (.tri t))
    (emb (.bump off)) (fun s => by rw [hP (.tri s)]; rfl) a inp st hsrc htmp]
  rw [iter_add]
  rw [bump_run P off src tmp cpy idx tab out emb exit fail hP off inp
    (Function.update (Function.update st tmp []) idx
      (List.replicate (3*a) true ++ false :: st idx))]
  rw [read_component P idx tab tmp out hit (Ne.symm hti) hio htt hto hmo
    (fun t => emb (.rd t)) exit fail (fun s => by rw [hP (.rd s)]; rfl) pre e post []
    inp (Function.update (Function.update (Function.update st tmp []) idx
      (List.replicate (3*a) true ++ false :: st idx)) idx
      (List.replicate off true ++ Function.update (Function.update st tmp []) idx
        (List.replicate (3*a) true ++ false :: st idx) idx))
    (by
      simp only [Function.update_same, hlen, Nat.add_comm (3*a) off, List.replicate_add,
        List.append_assoc, hidx, List.append_nil])
    (by
      simp only [Function.update_noteq (Ne.symm hit), Function.update_noteq htt, htab])
    (by simp only [Function.update_noteq hti, Function.update_noteq hti, Function.update_same])]
  congr 1
  funext y
  by_cases hy : y = tab
  · subst hy
    simp only [Function.update_same, Function.update_noteq hto,
      Function.update_noteq (Ne.symm hit), Function.update_noteq htt, Function.update_idem]
  · by_cases hz : y = out
    · subst hz
      simp only [Function.update_noteq hy, Function.update_same,
        Function.update_noteq (Ne.symm hio), Function.update_noteq (Ne.symm hmo),
        Function.update_idem]
    · by_cases hw : y = idx
      · subst hw
        simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_same,
          Function.update_noteq (Ne.symm hti), hidx, Function.update_idem]
      · by_cases hv : y = tmp
        · subst hv
          simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
            Function.update_same, Function.update_idem]
        · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw,
            Function.update_noteq hv]


/-! ## The accepting flag of a product state

The companion of `pairCode`: the third entry of each state's block is its
accepting flag, `0` or `1`, and the product state accepts exactly when both do,
so the flag of the pair is the PRODUCT of the two flags — which is what the
multiplier of v1652 computes. The stack assignment is the one `pairCode` uses,
so the two can be run one after the other on the same machine.
-/

inductive FlagSt
  | f1 (x : EntrySt)
  | f2 (x : EntrySt)
  | ml (x : MulSt)
  deriving DecidableEq

def flagCode (v : Fin 16 → Fin k) (emb : FlagSt → Q) (exit fail : Q) : FlagSt → Instr Q k
  | .f1 x =>
    entryCode 2 (v 0) (v 6) (v 7) (v 8) (v 2) (v 9) (fun t => emb (.f1 t))
      (emb (.f2 (.tri .sep))) fail x
  | .f2 x =>
    entryCode 2 (v 1) (v 6) (v 7) (v 8) (v 3) (v 10) (fun t => emb (.f2 t))
      (emb (.ml .loop)) fail x
  | .ml x => mulCode (v 9) (v 10) (v 5) (v 6) (fun t => emb (.ml t)) exit fail x

def flagTime (a1 : Nat) (pre1 : List Nat) (e1 : Nat)
    (a2 : Nat) (pre2 : List Nat) (e2 : Nat) : Nat :=
  entryTime 2 a1 pre1 e1+(entryTime 2 a2 pre2 e2+mulTime e1 e2)

theorem flag_component (P : Q → Instr Q k) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : FlagSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = flagCode v emb exit fail s)
    (a1 a2 e1 e2 : Nat) (pre1 pre2 : List Nat) (post1 post2 : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hp : st (v 0) = List.replicate a1 true ++ [false])
    (hq : st (v 1) = List.replicate a2 true ++ [false])
    (ht1 : st (v 2) = blocks pre1 ++ (List.replicate e1 true ++ false :: post1))
    (ht2 : st (v 3) = blocks pre2 ++ (List.replicate e2 true ++ false :: post2))
    (htmp : st (v 6) = []) (hidx : st (v 8) = [])
    (ho1 : st (v 9) = [false]) (ho2 : st (v 10) = [false])
    (hl1 : pre1.length = 3*a1+2) (hl2 : pre2.length = 3*a2+2) :
    iter P (flagTime a1 pre1 e1 a2 pre2 e2) ⟨emb (.f1 (.tri .sep)),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st (v 9) []) (v 10)
          (List.replicate e2 true ++ [false])) (v 5)
          (List.replicate (e1*e2) true ++ st (v 5))⟩ := by
  unfold flagTime
  rw [iter_add]
  rw [entry_component P 2 (v 0) (v 6) (v 7) (v 8) (v 2) (v 9)
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (fun t => emb (.f1 t)) (emb (.f2 (.tri .sep))) fail
    (fun s => by rw [hP (.f1 s)]; rfl) a1 pre1 e1 post1 inp st hp htmp hidx ht1 hl1]
  have hst1 : Function.update (Function.update (Function.update st (v 6) []) (v 9)
      (List.replicate e1 true ++ st (v 9))) (v 2) (st (v 2))
      = Function.update st (v 9) (List.replicate e1 true ++ [false]) := by
    funext y
    by_cases h2 : y = v 2
    · subst h2
      simp only [Function.update_same, Function.update_noteq (vne hv (by decide) : v 2 ≠ v 9)]
    · by_cases h9 : y = v 9
      · subst h9
        simp only [Function.update_noteq h2, Function.update_same, ho1]
      · by_cases h6 : y = v 6
        · subst h6
          simp only [Function.update_noteq h2, Function.update_noteq h9, Function.update_same,
            Function.update_noteq h9, htmp]
        · simp only [Function.update_noteq h2, Function.update_noteq h9, Function.update_noteq h6]
  rw [hst1]
  rw [iter_add]
  rw [entry_component P 2 (v 1) (v 6) (v 7) (v 8) (v 3) (v 10)
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (fun t => emb (.f2 t)) (emb (.ml .loop)) fail
    (fun s => by rw [hP (.f2 s)]; rfl) a2 pre2 e2 post2 inp
    (Function.update st (v 9) (List.replicate e1 true ++ [false]))
    (by rw [Function.update_noteq (vne hv (by decide) : v 1 ≠ v 9), hq])
    (by rw [Function.update_noteq (vne hv (by decide) : v 6 ≠ v 9), htmp])
    (by rw [Function.update_noteq (vne hv (by decide) : v 8 ≠ v 9), hidx])
    (by rw [Function.update_noteq (vne hv (by decide) : v 3 ≠ v 9), ht2]) hl2]
  have hst2 : Function.update (Function.update (Function.update
      (Function.update st (v 9) (List.replicate e1 true ++ [false])) (v 6) []) (v 10)
      (List.replicate e2 true ++ Function.update st (v 9)
        (List.replicate e1 true ++ [false]) (v 10)))
      (v 3) (Function.update st (v 9) (List.replicate e1 true ++ [false]) (v 3))
      = Function.update (Function.update st (v 9) (List.replicate e1 true ++ [false]))
          (v 10) (List.replicate e2 true ++ [false]) := by
    have h109 : (v 10) ≠ (v 9) := vne hv (by decide)
    funext y
    by_cases h3 : y = v 3
    · subst h3
      simp only [Function.update_same, Function.update_noteq (vne hv (by decide) : v 3 ≠ v 10)]
    · by_cases h10 : y = v 10
      · subst h10
        simp only [Function.update_noteq h3, Function.update_same,
          Function.update_noteq h109, ho2]
      · by_cases h6 : y = v 6
        · subst h6
          simp only [Function.update_noteq h3, Function.update_noteq h10, Function.update_same,
            Function.update_noteq (vne hv (by decide) : v 6 ≠ v 9), htmp]
        · simp only [Function.update_noteq h3, Function.update_noteq h10, Function.update_noteq h6]
  rw [hst2]
  rw [mul_component P (v 9) (v 10) (v 5) (v 6)
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide))
    (fun t => emb (.ml t)) exit fail (fun s => by rw [hP (.ml s)]; rfl) e1 e2 inp
    (Function.update (Function.update st (v 9) (List.replicate e1 true ++ [false]))
      (v 10) (List.replicate e2 true ++ [false])) [] []
    (by
      rw [Function.update_noteq (vne hv (by decide) : v 9 ≠ v 10), Function.update_same])
    (by rw [Function.update_same])
    (by
      rw [Function.update_noteq (vne hv (by decide) : v 6 ≠ v 10),
        Function.update_noteq (vne hv (by decide) : v 6 ≠ v 9), htmp])]
  congr 1
  funext y
  by_cases h5 : y = v 5
  · subst h5
    simp only [Function.update_same, Function.update_noteq (vne hv (by decide) : v 5 ≠ v 10),
      Function.update_noteq (vne hv (by decide) : v 5 ≠ v 9)]
  · by_cases h9 : y = v 9
    · subst h9
      simp only [Function.update_noteq h5, Function.update_same,
        Function.update_noteq (vne hv (by decide) : v 9 ≠ v 10), Function.update_same]
    · by_cases h10 : y = v 10
      · subst h10
        simp only [Function.update_noteq h5, Function.update_noteq h9, Function.update_same]
      · simp only [Function.update_noteq h5, Function.update_noteq h9, Function.update_noteq h10]


/-! ## A loop driven by a counter

Everything built so far is straight-line. The product construction needs two
nested loops, and what a loop needs on this machine is a control counter: the
head pops one marker and runs the body, and when the separator turns up instead
the loop is over.

The body is given abstractly, by its effect `f` on the stacks and its step count
`T`, with one condition: it must not look at the control counter, which is
`hcomm` — the body commutes with rewriting that one stack. Both loops of the
product construction satisfy it, since the body only reads the two state
counters, the two tables and the scratch stacks.

The count is exact: `n` iterations of a `T`-step body cost `n*(T+1)+1`.
-/

theorem iterate_update {f : (Fin k → List Bool) → (Fin k → List Bool)} {ctr : Fin k}
    (hcomm : ∀ st c, f (Function.update st ctr c) = Function.update (f st) ctr c) (n : Nat)
    (st : Fin k → List Bool) (c : List Bool) :
    f^[n] (Function.update st ctr c) = Function.update (f^[n] st) ctr c := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, hcomm, ih]

theorem loop_run (P : Q → Instr Q k) (hd bodyEntry exitQ : Q) (ctr : Fin k) (inp : List Bool)
    (hpop : P hd = .pop ctr bodyEntry exitQ exitQ)
    (f : (Fin k → List Bool) → (Fin k → List Bool)) (T : Nat)
    (hbody : ∀ st, iter P T ⟨bodyEntry,inp,st⟩ = ⟨hd,inp,f st⟩)
    (hcomm : ∀ st c, f (Function.update st ctr c) = Function.update (f st) ctr c)
    (n : Nat) (rest : List Bool) (st : Fin k → List Bool)
    (hctr : st ctr = List.replicate n true ++ false :: rest) :
    iter P (n*(T+1)+1) ⟨hd,inp,st⟩
      = ⟨exitQ,inp,Function.update (f^[n] st) ctr rest⟩ := by
  induction n generalizing st with
  | zero =>
    simp only [List.replicate_zero, List.nil_append] at hctr
    have s1 : step P ⟨hd,inp,st⟩ = some ⟨exitQ,inp,Function.update st ctr rest⟩ := by
      simp [step, hpop, hctr]
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [iter_one P s1]
    rfl
  | succ n ih =>
    have hc : st ctr = true :: (List.replicate n true ++ false :: rest) := by
      rw [hctr, List.replicate_succ, List.cons_append]
    have s1 : step P ⟨hd,inp,st⟩
        = some ⟨bodyEntry,inp,Function.update st ctr
            (List.replicate n true ++ false :: rest)⟩ := by
      simp [step, hpop, hc]
    have he : (n+1)*(T+1)+1 = 1+(T+(n*(T+1)+1)) := by ring
    rw [he, iter_step' P s1, iter_add, hbody]
    rw [ih (f (Function.update st ctr (List.replicate n true ++ false :: rest)))
      (by rw [hcomm, Function.update_same])]
    rw [hcomm, iterate_update hcomm, Function.update_idem, Function.iterate_succ_apply]


/-! ## Two consequences: clearing a counter, and emitting an entry

A loop whose body is empty is a counter clearer: it pops markers until the
separator, which is what a scratch counter left over by a component needs. It is
the `T = 0` case of `loop_run`, so it costs exactly `n+1` steps.

`emitCode` is the other half of every iteration of the product construction: the
accumulated value is written as a block onto the output table and the
accumulator is reopened with a fresh separator, ready for the next value.
Entries written in this order come out as a table when the output stack is
poured once, since pouring reverses.
-/

def clearCode (ctr : Fin k) (self exit : Q) : Instr Q k := .pop ctr self exit exit

theorem clear_component (P : Q → Instr Q k) (ctr : Fin k) (self exit : Q)
    (hP : P self = clearCode ctr self exit)
    (n : Nat) (rest inp : List Bool) (st : Fin k → List Bool)
    (hctr : st ctr = List.replicate n true ++ false :: rest) :
    iter P (n+1) ⟨self,inp,st⟩ = ⟨exit,inp,Function.update st ctr rest⟩ := by
  have h := loop_run P self self exit ctr inp hP id 0 (fun st => rfl)
    (fun st c => rfl) n rest st hctr
  simpa only [Nat.zero_add, Nat.mul_one, Function.iterate_id, id_eq] using h

inductive EmitSt
  | w (x : WSt)
  | sep
  deriving DecidableEq

def emitCode (acc tab : Fin k) (emb : EmitSt → Q) (exit : Q) : EmitSt → Instr Q k
  | .w x => writeCode acc tab (fun t => emb (.w t)) (emb .sep) x
  | .sep => .push acc false exit

def emitTime (n : Nat) : Nat := (2*n+2)+1

theorem emit_component (P : Q → Instr Q k) (acc tab : Fin k) (hne : acc ≠ tab)
    (emb : EmitSt → Q) (exit : Q)
    (hP : ∀ s, P (emb s) = emitCode acc tab emb exit s)
    (n : Nat) (inp : List Bool) (st : Fin k → List Bool)
    (hacc : st acc = List.replicate n true ++ [false]) :
    iter P (emitTime n) ⟨emb (.w .loop),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st acc [false]) tab
          (false :: (List.replicate n true ++ st tab))⟩ := by
  unfold emitTime
  rw [iter_add]
  rw [write_component P acc tab hne (fun t => emb (.w t)) (emb .sep)
    (fun s => by rw [hP (.w s)]; rfl) n inp st [] hacc]
  rw [iter_one P (c' := ⟨exit,inp,Function.update (Function.update (Function.update st acc []) tab
    (false :: (List.replicate n true ++ st tab))) acc
    (false :: Function.update (Function.update st acc []) tab
      (false :: (List.replicate n true ++ st tab)) acc)⟩) (by simp [step, hP .sep, emitCode])]
  congr 1
  funext y
  by_cases hy : y = acc
  · subst hy
    simp only [Function.update_same, Function.update_noteq hne, Function.update_idem]
  · by_cases hz : y = tab
    · subst hz
      simp only [Function.update_noteq hy, Function.update_same, Function.update_noteq hy,
        Function.update_noteq (Ne.symm hne)]
    · simp only [Function.update_noteq hy, Function.update_noteq hz]


/-! ## One emitted transition of the product

The product's body, packaged so that it composes: compute one transition of the
product state `(p,q)` under one bit, write it as an entry of the output table,
and put the two successor stacks back the way they were. The net effect on the
stacks is then a single update — the output table grows by one block — which is
what makes the loop around it provable.
-/

inductive EPSt
  | pr (x : PairSt)
  | em (x : EmitSt)
  | r9
  | r10
  deriving DecidableEq

def emitPairCode (bit : Bool) (v : Fin 16 → Fin k) (emb : EPSt → Q) (exit fail : Q) :
    EPSt → Instr Q k
  | .pr x => pairCode bit v (fun t => emb (.pr t)) (emb (.em (.w .loop))) fail x
  | .em x => emitCode (v 5) (v 11) (fun t => emb (.em t)) (emb .r9) x
  | .r9 => .push (v 9) false (emb .r10)
  | .r10 => .push (v 10) false exit

def emitPairTime (bit : Bool) (a1 : Nat) (pre1 : List Nat) (e1 : Nat)
    (a2 : Nat) (pre2 : List Nat) (e2 : Nat) (nv : Nat) : Nat :=
  pairTime bit a1 pre1 e1 a2 pre2 e2 nv+(emitTime (e1*nv+e2)+(1+1))

theorem emitPair_component (P : Q → Instr Q k) (bit : Bool) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : EPSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = emitPairCode bit v emb exit fail s)
    (a1 a2 nv e1 e2 : Nat) (pre1 pre2 : List Nat) (post1 post2 restN : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hp : st (v 0) = List.replicate a1 true ++ [false])
    (hq : st (v 1) = List.replicate a2 true ++ [false])
    (ht1 : st (v 2) = blocks pre1 ++ (List.replicate e1 true ++ false :: post1))
    (ht2 : st (v 3) = blocks pre2 ++ (List.replicate e2 true ++ false :: post2))
    (hn : st (v 4) = List.replicate nv true ++ false :: restN)
    (htmp : st (v 6) = []) (hidx : st (v 8) = [])
    (ho1 : st (v 9) = [false]) (ho2 : st (v 10) = [false]) (hacc : st (v 5) = [false])
    (hl1 : pre1.length = 3*a1+(if bit then 1 else 0))
    (hl2 : pre2.length = 3*a2+(if bit then 1 else 0)) :
    iter P (emitPairTime bit a1 pre1 e1 a2 pre2 e2 nv) ⟨emb (.pr (.t1 (.tri .sep))),inp,st⟩
      = ⟨exit,inp,Function.update st (v 11)
          (false :: (List.replicate (e1*nv+e2) true ++ st (v 11)))⟩ := by
  have s9 : ∀ u : Fin k → List Bool, step P ⟨emb .r9,inp,u⟩
      = some ⟨emb .r10,inp,Function.update u (v 9) (false :: u (v 9))⟩ := by
    intro u; simp [step, hP .r9, emitPairCode]
  have s10 : ∀ u : Fin k → List Bool, step P ⟨emb .r10,inp,u⟩
      = some ⟨exit,inp,Function.update u (v 10) (false :: u (v 10))⟩ := by
    intro u; simp [step, hP .r10, emitPairCode]
  unfold emitPairTime
  rw [iter_add]
  rw [pair_component P bit v hv (fun t => emb (.pr t)) (emb (.em (.w .loop))) fail
    (fun s => by rw [hP (.pr s)]; rfl) a1 a2 nv e1 e2 pre1 pre2 post1 post2 restN inp st
    hp hq ht1 ht2 hn htmp hidx ho1 ho2 hl1 hl2]
  rw [iter_add]
  rw [emit_component P (v 5) (v 11) (vne hv (by decide)) (fun t => emb (.em t)) (emb .r9)
    (fun s => by rw [hP (.em s)]; rfl) (e1*nv+e2) inp
    (Function.update (Function.update (Function.update st (v 9) []) (v 10) []) (v 5)
      (List.replicate e2 true ++ (List.replicate (e1*nv) true ++ st (v 5))))
    (by
      rw [Function.update_same, hacc, ← List.append_assoc, ← List.replicate_add,
        Nat.add_comm e2 (e1*nv)])]
  rw [iter_step' P (s9 _), iter_one P (s10 _)]
  congr 1
  funext y
  have h911 : (v 9) ≠ (v 11) := vne hv (by decide)
  have h1011 : (v 10) ≠ (v 11) := vne hv (by decide)
  have h95 : (v 9) ≠ (v 5) := vne hv (by decide)
  have h105 : (v 10) ≠ (v 5) := vne hv (by decide)
  have h109 : (v 10) ≠ (v 9) := vne hv (by decide)
  have h511 : (v 5) ≠ (v 11) := vne hv (by decide)
  by_cases h10 : y = v 10
  · subst h10
    simp only [Function.update_same, Function.update_noteq h1011, Function.update_noteq h105,
      Function.update_noteq h109, Function.update_same, Function.update_noteq h1011, ho2]
  · by_cases h9 : y = v 9
    · subst h9
      simp only [Function.update_noteq h10, Function.update_same, Function.update_noteq h911,
        Function.update_noteq h95, Function.update_same, Function.update_noteq h911, ho1]
    · by_cases h11 : y = v 11
      · subst h11
        simp only [Function.update_noteq h10, Function.update_noteq h9, Function.update_same,
          Function.update_noteq (Ne.symm h511), Function.update_noteq (Ne.symm h911),
          Function.update_noteq (Ne.symm h1011)]
      · by_cases h5 : y = v 5
        · subst h5
          simp only [Function.update_noteq h10, Function.update_noteq h9,
            Function.update_noteq h11, Function.update_same, Function.update_noteq h511, hacc]
        · simp only [Function.update_noteq h10, Function.update_noteq h9,
            Function.update_noteq h11, Function.update_noteq h5]


/-! ## The emitted accepting flag

The twin of `emitPairCode` for the third entry of a product state's block. The
flag computation of v1661 leaves the second flag on a scratch stack, so this one
clears it (v1663) before putting the two successor stacks back. The net effect
is again a single update of the output table.
-/

inductive EFSt
  | fl (x : FlagSt)
  | em (x : EmitSt)
  | cl
  | r9
  | r10
  deriving DecidableEq

def emitFlagCode (v : Fin 16 → Fin k) (emb : EFSt → Q) (exit fail : Q) : EFSt → Instr Q k
  | .fl x => flagCode v (fun t => emb (.fl t)) (emb (.em (.w .loop))) fail x
  | .em x => emitCode (v 5) (v 11) (fun t => emb (.em t)) (emb .cl) x
  | .cl => clearCode (v 10) (emb .cl) (emb .r9)
  | .r9 => .push (v 9) false (emb .r10)
  | .r10 => .push (v 10) false exit

def emitFlagTime (a1 : Nat) (pre1 : List Nat) (e1 : Nat)
    (a2 : Nat) (pre2 : List Nat) (e2 : Nat) : Nat :=
  flagTime a1 pre1 e1 a2 pre2 e2+(emitTime (e1*e2)+((e2+1)+(1+1)))

theorem emitFlag_component (P : Q → Instr Q k) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : EFSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = emitFlagCode v emb exit fail s)
    (a1 a2 e1 e2 : Nat) (pre1 pre2 : List Nat) (post1 post2 : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hp : st (v 0) = List.replicate a1 true ++ [false])
    (hq : st (v 1) = List.replicate a2 true ++ [false])
    (ht1 : st (v 2) = blocks pre1 ++ (List.replicate e1 true ++ false :: post1))
    (ht2 : st (v 3) = blocks pre2 ++ (List.replicate e2 true ++ false :: post2))
    (htmp : st (v 6) = []) (hidx : st (v 8) = [])
    (ho1 : st (v 9) = [false]) (ho2 : st (v 10) = [false]) (hacc : st (v 5) = [false])
    (hl1 : pre1.length = 3*a1+2) (hl2 : pre2.length = 3*a2+2) :
    iter P (emitFlagTime a1 pre1 e1 a2 pre2 e2) ⟨emb (.fl (.f1 (.tri .sep))),inp,st⟩
      = ⟨exit,inp,Function.update st (v 11)
          (false :: (List.replicate (e1*e2) true ++ st (v 11)))⟩ := by
  have s9 : ∀ u : Fin k → List Bool, step P ⟨emb .r9,inp,u⟩
      = some ⟨emb .r10,inp,Function.update u (v 9) (false :: u (v 9))⟩ := by
    intro u; simp [step, hP .r9, emitFlagCode]
  have s10 : ∀ u : Fin k → List Bool, step P ⟨emb .r10,inp,u⟩
      = some ⟨exit,inp,Function.update u (v 10) (false :: u (v 10))⟩ := by
    intro u; simp [step, hP .r10, emitFlagCode]
  have h911 : (v 9) ≠ (v 11) := vne hv (by decide)
  have h1011 : (v 10) ≠ (v 11) := vne hv (by decide)
  have h95 : (v 9) ≠ (v 5) := vne hv (by decide)
  have h105 : (v 10) ≠ (v 5) := vne hv (by decide)
  have h109 : (v 10) ≠ (v 9) := vne hv (by decide)
  have h511 : (v 5) ≠ (v 11) := vne hv (by decide)
  unfold emitFlagTime
  rw [iter_add]
  rw [flag_component P v hv (fun t => emb (.fl t)) (emb (.em (.w .loop))) fail
    (fun s => by rw [hP (.fl s)]; rfl) a1 a2 e1 e2 pre1 pre2 post1 post2 inp st
    hp hq ht1 ht2 htmp hidx ho1 ho2 hl1 hl2]
  rw [iter_add]
  rw [emit_component P (v 5) (v 11) h511 (fun t => emb (.em t)) (emb .cl)
    (fun s => by rw [hP (.em s)]; rfl) (e1*e2) inp
    (Function.update (Function.update (Function.update st (v 9) []) (v 10)
      (List.replicate e2 true ++ [false])) (v 5)
      (List.replicate (e1*e2) true ++ st (v 5)))
    (by rw [Function.update_same, hacc])]
  rw [iter_add]
  rw [clear_component P (v 10) (emb .cl) (emb .r9) (hP .cl) e2 [] inp
    (Function.update (Function.update (Function.update (Function.update (Function.update st (v 9) [])
      (v 10) (List.replicate e2 true ++ [false])) (v 5)
      (List.replicate (e1*e2) true ++ st (v 5))) (v 5) [false]) (v 11)
      (false :: (List.replicate (e1*e2) true ++ Function.update (Function.update
        (Function.update st (v 9) []) (v 10) (List.replicate e2 true ++ [false])) (v 5)
        (List.replicate (e1*e2) true ++ st (v 5)) (v 11))))
    (by
      rw [Function.update_noteq h1011, Function.update_noteq h105, Function.update_noteq h105,
        Function.update_same])]
  rw [iter_step' P (s9 _), iter_one P (s10 _)]
  congr 1
  funext y
  by_cases h10 : y = v 10
  · subst h10
    simp only [Function.update_same, Function.update_noteq h109, Function.update_noteq h1011,
      Function.update_noteq h105, ho2]
  · by_cases h9 : y = v 9
    · subst h9
      simp only [Function.update_noteq h10, Function.update_same, Function.update_noteq h911,
        Function.update_noteq h95, Function.update_noteq h109, ho1]
    · by_cases h11 : y = v 11
      · subst h11
        simp only [Function.update_noteq h10, Function.update_noteq h9,
          Function.update_noteq (Ne.symm h1011), Function.update_noteq (Ne.symm h911),
          Function.update_same, Function.update_noteq (Ne.symm h511)]
      · by_cases h5 : y = v 5
        · subst h5
          simp only [Function.update_noteq h10, Function.update_noteq h9,
            Function.update_noteq h11, Function.update_noteq h511, Function.update_same, hacc]
        · simp only [Function.update_noteq h10, Function.update_noteq h9,
            Function.update_noteq h11, Function.update_noteq h5]


/-! ## Loops whose body changes from one iteration to the next

`loop_run` asks the body for one effect and one step count, valid for every
stack state. The product construction's loops are not like that: the body reads
a state counter that grows, and both its effect and its cost depend on the
iteration. What is true instead is that the stack state at the start of
iteration `i` is a known function `F i` of `i`, and one iteration takes `S i`
steps and turns `F i` into `F (i+1)`.

`loop_chain` is that rule. It says nothing about how the loop is controlled —
the pop that tests the control counter is part of the iteration — so it applies
to any loop whose successive states can be named. `chainTime_le` turns the exact
cost into the bound the complexity statement needs.
-/

def chainTime (S : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n+1 => S 0+chainTime (fun i => S (i+1)) n

theorem chainTime_le (S : Nat → Nat) (B : Nat) :
    ∀ (n : Nat), (∀ i, i < n → S i ≤ B) → chainTime S n ≤ n*B+1 := by
  intro n
  induction n generalizing S with
  | zero => intro _; simp [chainTime]
  | succ n ih =>
    intro h
    have h0 : S 0 ≤ B := h 0 (Nat.succ_pos n)
    have hrest : chainTime (fun i => S (i+1)) n ≤ n*B+1 :=
      ih (fun i => S (i+1)) (fun i hi => h (i+1) (Nat.succ_lt_succ hi))
    have : chainTime S (n+1) = S 0+chainTime (fun i => S (i+1)) n := rfl
    rw [this]
    have hmul : (n+1)*B = n*B+B := by ring
    omega

theorem loop_chain (P : Q → Instr Q k) (hd exitQ : Q) (inp : List Bool)
    (G : Fin k → List Bool) :
    ∀ (n : Nat) (F : Nat → Fin k → List Bool) (S : Nat → Nat),
      (∀ i, i < n → iter P (S i) ⟨hd,inp,F i⟩ = ⟨hd,inp,F (i+1)⟩) →
      step P ⟨hd,inp,F n⟩ = some ⟨exitQ,inp,G⟩ →
      iter P (chainTime S n) ⟨hd,inp,F 0⟩ = ⟨exitQ,inp,G⟩ := by
  intro n
  induction n with
  | zero =>
    intro F S _ hfin
    exact iter_one P hfin
  | succ n ih =>
    intro F S hstep hfin
    have h0 := hstep 0 (Nat.succ_pos n)
    have he : chainTime S (n+1) = S 0+chainTime (fun i => S (i+1)) n := rfl
    rw [he, iter_add, h0]
    exact ih (fun i => F (i+1)) (fun i => S (i+1))
      (fun i hi => hstep (i+1) (Nat.succ_lt_succ hi)) hfin


/-! ## The inner body: one product state, written out

Three entries per product state: the two transitions and the accepting flag.
The tables are now given whole — `st (v 2) = blocks T1` with the entries read
through `T1.getD` — which is what the loop needs, since the entry read changes
from iteration to iteration while the table does not.
-/

theorem blocks_split (T : List Nat) (j : Nat) (h : j < T.length) :
    blocks T = blocks (T.take j)
      ++ (List.replicate (T.getD j 0) true ++ false :: blocks (T.drop (j+1))) := by
  conv_lhs => rw [← List.take_append_drop j T, List.drop_eq_getElem_cons h]
  rw [blocks_append]
  simp [blocks, List.getD_eq_getElem, h]

theorem take_len (T : List Nat) (j : Nat) (h : j ≤ T.length) : (T.take j).length = j := by
  simp [List.length_take, Nat.min_eq_left h]

/-- The blocks a run of emissions leaves on the output stack, outermost last. -/
def emitBlocks : List Nat → List Bool → List Bool
  | [], A => A
  | e :: es, A => emitBlocks es (false :: (List.replicate e true ++ A))

/-- The three entries of the product state `(p,q)`: the two transitions, indexed
`d1*nv+d2`, and the flag, the product of the two flags. -/
def prodEntries (T1 T2 : List Nat) (p q nv : Nat) : List Nat :=
  [T1.getD (3*p) 0*nv+T2.getD (3*q) 0,
   T1.getD (3*p+1) 0*nv+T2.getD (3*q+1) 0,
   T1.getD (3*p+2) 0*T2.getD (3*q+2) 0]

inductive IBSt
  | e0 (x : EPSt)
  | e1 (x : EPSt)
  | ef (x : EFSt)
  | inc
  deriving DecidableEq

def innerBodyCode (v : Fin 16 → Fin k) (emb : IBSt → Q) (exit fail : Q) : IBSt → Instr Q k
  | .e0 x =>
    emitPairCode false v (fun t => emb (.e0 t)) (emb (.e1 (.pr (.t1 (.tri .sep))))) fail x
  | .e1 x =>
    emitPairCode true v (fun t => emb (.e1 t)) (emb (.ef (.fl (.f1 (.tri .sep))))) fail x
  | .ef x => emitFlagCode v (fun t => emb (.ef t)) (emb .inc) fail x
  | .inc => .push (v 1) true exit

def innerBodyTime (T1 T2 : List Nat) (p q nv : Nat) : Nat :=
  emitPairTime false p (T1.take (3*p)) (T1.getD (3*p) 0) q (T2.take (3*q))
      (T2.getD (3*q) 0) nv
    +(emitPairTime true p (T1.take (3*p+1)) (T1.getD (3*p+1) 0) q (T2.take (3*q+1))
        (T2.getD (3*q+1) 0) nv
      +(emitFlagTime p (T1.take (3*p+2)) (T1.getD (3*p+2) 0) q (T2.take (3*q+2))
          (T2.getD (3*q+2) 0)+1))

theorem innerBody_component (P : Q → Instr Q k) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : IBSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = innerBodyCode v emb exit fail s)
    (T1 T2 : List Nat) (p q nv : Nat) (restN : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hp : st (v 0) = List.replicate p true ++ [false])
    (hq : st (v 1) = List.replicate q true ++ [false])
    (ht1 : st (v 2) = blocks T1) (ht2 : st (v 3) = blocks T2)
    (hb1 : 3*p+2 < T1.length) (hb2 : 3*q+2 < T2.length)
    (hn : st (v 4) = List.replicate nv true ++ false :: restN)
    (htmp : st (v 6) = []) (hidx : st (v 8) = [])
    (ho1 : st (v 9) = [false]) (ho2 : st (v 10) = [false]) (hacc : st (v 5) = [false]) :
    iter P (innerBodyTime T1 T2 p q nv) ⟨emb (.e0 (.pr (.t1 (.tri .sep)))),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st (v 11)
          (emitBlocks (prodEntries T1 T2 p q nv) (st (v 11)))) (v 1) (true :: st (v 1))⟩ := by
  have h011 : (v 0) ≠ (v 11) := vne hv (by decide)
  have h111 : (v 1) ≠ (v 11) := vne hv (by decide)
  have h211 : (v 2) ≠ (v 11) := vne hv (by decide)
  have h311 : (v 3) ≠ (v 11) := vne hv (by decide)
  have h411 : (v 4) ≠ (v 11) := vne hv (by decide)
  have h511 : (v 5) ≠ (v 11) := vne hv (by decide)
  have h611 : (v 6) ≠ (v 11) := vne hv (by decide)
  have h811 : (v 8) ≠ (v 11) := vne hv (by decide)
  have h911 : (v 9) ≠ (v 11) := vne hv (by decide)
  have h1011 : (v 10) ≠ (v 11) := vne hv (by decide)
  have sinc : ∀ u : Fin k → List Bool, step P ⟨emb .inc,inp,u⟩
      = some ⟨exit,inp,Function.update u (v 1) (true :: u (v 1))⟩ := by
    intro u; simp [step, hP .inc, innerBodyCode]
  -- the six table decompositions
  have k1 : ∀ j, j < T1.length → st (v 2)
      = blocks (T1.take j) ++ (List.replicate (T1.getD j 0) true ++ false :: blocks (T1.drop (j+1))) :=
    fun j hj => by rw [ht1]; exact blocks_split T1 j hj
  have k2 : ∀ j, j < T2.length → st (v 3)
      = blocks (T2.take j) ++ (List.replicate (T2.getD j 0) true ++ false :: blocks (T2.drop (j+1))) :=
    fun j hj => by rw [ht2]; exact blocks_split T2 j hj
  have l1 : ∀ j, j ≤ T1.length → (T1.take j).length = j := fun j hj => take_len T1 j hj
  have l2 : ∀ j, j ≤ T2.length → (T2.take j).length = j := fun j hj => take_len T2 j hj
  unfold innerBodyTime
  rw [iter_add]
  rw [emitPair_component P false v hv (fun t => emb (.e0 t))
    (emb (.e1 (.pr (.t1 (.tri .sep))))) fail (fun s => by rw [hP (.e0 s)]; rfl)
    p q nv (T1.getD (3*p) 0) (T2.getD (3*q) 0) (T1.take (3*p)) (T2.take (3*q))
    (blocks (T1.drop (3*p+1))) (blocks (T2.drop (3*q+1))) restN inp st
    hp hq (k1 (3*p) (by omega)) (k2 (3*q) (by omega)) hn htmp hidx ho1 ho2 hacc
    (by rw [l1 (3*p) (by omega)]; rfl) (by rw [l2 (3*q) (by omega)]; rfl)]
  rw [iter_add]
  rw [emitPair_component P true v hv (fun t => emb (.e1 t))
    (emb (.ef (.fl (.f1 (.tri .sep))))) fail (fun s => by rw [hP (.e1 s)]; rfl)
    p q nv (T1.getD (3*p+1) 0) (T2.getD (3*q+1) 0) (T1.take (3*p+1)) (T2.take (3*q+1))
    (blocks (T1.drop (3*p+1+1))) (blocks (T2.drop (3*q+1+1))) restN inp
    (Function.update st (v 11) (false :: (List.replicate
      (T1.getD (3*p) 0*nv+T2.getD (3*q) 0) true ++ st (v 11))))
    (by rw [Function.update_noteq h011, hp])
    (by rw [Function.update_noteq h111, hq])
    (by rw [Function.update_noteq h211]; exact k1 (3*p+1) (by omega))
    (by rw [Function.update_noteq h311]; exact k2 (3*q+1) (by omega))
    (by rw [Function.update_noteq h411, hn])
    (by rw [Function.update_noteq h611, htmp])
    (by rw [Function.update_noteq h811, hidx])
    (by rw [Function.update_noteq h911, ho1])
    (by rw [Function.update_noteq h1011, ho2])
    (by rw [Function.update_noteq h511, hacc])
    (by rw [l1 (3*p+1) (by omega)]; rfl) (by rw [l2 (3*q+1) (by omega)]; rfl)]
  rw [Function.update_same, Function.update_idem]
  rw [iter_add]
  rw [emitFlag_component P v hv (fun t => emb (.ef t)) (emb .inc) fail
    (fun s => by rw [hP (.ef s)]; rfl)
    p q (T1.getD (3*p+2) 0) (T2.getD (3*q+2) 0) (T1.take (3*p+2)) (T2.take (3*q+2))
    (blocks (T1.drop (3*p+2+1))) (blocks (T2.drop (3*q+2+1))) inp
    (Function.update st (v 11) (false :: (List.replicate
        (T1.getD (3*p+1) 0*nv+T2.getD (3*q+1) 0) true ++
      (false :: (List.replicate (T1.getD (3*p) 0*nv+T2.getD (3*q) 0) true ++ st (v 11))))))
    (by rw [Function.update_noteq h011, hp])
    (by rw [Function.update_noteq h111, hq])
    (by rw [Function.update_noteq h211]; exact k1 (3*p+2) (by omega))
    (by rw [Function.update_noteq h311]; exact k2 (3*q+2) (by omega))
    (by rw [Function.update_noteq h611, htmp])
    (by rw [Function.update_noteq h811, hidx])
    (by rw [Function.update_noteq h911, ho1])
    (by rw [Function.update_noteq h1011, ho2])
    (by rw [Function.update_noteq h511, hacc])
    (by rw [l1 (3*p+2) (by omega)]) (by rw [l2 (3*q+2) (by omega)])]
  rw [Function.update_same, Function.update_idem]
  rw [iter_one P (sinc _)]
  rw [Function.update_noteq h111]
  rfl


/-! ## The inner loop: every second-component state, for one first state

The first loop of the product construction. The control counter on stack 12
holds the number of states of the second automaton; each iteration writes one
product state's block and advances the inner state counter, so after the loop
the output table has grown by `n2` blocks of three and the inner counter has
reached `n2`.
-/

def innerBlocks (T1 T2 : List Nat) (p nv : Nat) : Nat → List Bool → List Bool
  | 0, A => A
  | q+1, A => emitBlocks (prodEntries T1 T2 p q nv) (innerBlocks T1 T2 p nv q A)

inductive ILSt
  | hd
  | body (x : IBSt)
  deriving DecidableEq

def innerLoopCode (v : Fin 16 → Fin k) (emb : ILSt → Q) (exit fail : Q) : ILSt → Instr Q k
  | .hd => .pop (v 12) (emb (.body (.e0 (.pr (.t1 (.tri .sep)))))) exit exit
  | .body x => innerBodyCode v (fun t => emb (.body t)) (emb .hd) fail x

def innerLoopTime (T1 T2 : List Nat) (p nv n2 : Nat) : Nat :=
  chainTime (fun q => 1+innerBodyTime T1 T2 p q nv) n2

theorem innerLoop_component (P : Q → Instr Q k) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : ILSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = innerLoopCode v emb exit fail s)
    (T1 T2 : List Nat) (p nv n2 : Nat) (rest restN : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hp : st (v 0) = List.replicate p true ++ [false])
    (hq : st (v 1) = [false])
    (ht1 : st (v 2) = blocks T1) (ht2 : st (v 3) = blocks T2)
    (hb1 : 3*p+2 < T1.length) (hb2 : ∀ q, q < n2 → 3*q+2 < T2.length)
    (hn : st (v 4) = List.replicate nv true ++ false :: restN)
    (htmp : st (v 6) = []) (hidx : st (v 8) = [])
    (ho1 : st (v 9) = [false]) (ho2 : st (v 10) = [false]) (hacc : st (v 5) = [false])
    (hctr : st (v 12) = List.replicate n2 true ++ false :: rest) :
    iter P (innerLoopTime T1 T2 p nv n2) ⟨emb .hd,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st
          (v 1) (List.replicate n2 true ++ [false]))
          (v 11) (innerBlocks T1 T2 p nv n2 (st (v 11)))) (v 12) rest⟩ := by
  have h112 : (v 1) ≠ (v 12) := vne hv (by decide)
  have h1112 : (v 11) ≠ (v 12) := vne hv (by decide)
  have h111 : (v 1) ≠ (v 11) := vne hv (by decide)
  set F : Nat → Fin k → List Bool := fun q =>
    Function.update (Function.update (Function.update st
      (v 1) (List.replicate q true ++ [false]))
      (v 11) (innerBlocks T1 T2 p nv q (st (v 11)))) (v 12)
      (List.replicate (n2-q) true ++ false :: rest) with hFdef
  have hFother : ∀ (i : Fin 16), i ≠ 1 → i ≠ 11 → i ≠ 12 → ∀ q, F q (v i) = st (v i) := by
    intro i h1 h11 h12 q
    simp only [hFdef]
    rw [Function.update_noteq (vne hv h12), Function.update_noteq (vne hv h11),
      Function.update_noteq (vne hv h1)]
  have hF0 : F 0 = st := by
    funext y
    simp only [hFdef]
    by_cases h12 : y = v 12
    · subst h12
      rw [Function.update_same, Nat.sub_zero, ← hctr]
    · by_cases h11 : y = v 11
      · subst h11
        rw [Function.update_noteq h12, Function.update_same]
        rfl
      · by_cases h1 : y = v 1
        · subst h1
          rw [Function.update_noteq h12, Function.update_noteq h11, Function.update_same,
            List.replicate_zero, List.nil_append, ← hq]
        · rw [Function.update_noteq h12, Function.update_noteq h11, Function.update_noteq h1]
  have hFctr : ∀ q, F q (v 12) = List.replicate (n2-q) true ++ false :: rest := by
    intro q; simp only [hFdef, Function.update_same]
  have hF11 : ∀ q, F q (v 11) = innerBlocks T1 T2 p nv q (st (v 11)) := by
    intro q
    simp only [hFdef, Function.update_noteq h1112, Function.update_same]
  have hF1 : ∀ q, F q (v 1) = List.replicate q true ++ [false] := by
    intro q
    simp only [hFdef, Function.update_noteq h112, Function.update_noteq h111, Function.update_same]
  have hstep : ∀ q, q < n2 →
      iter P (1+innerBodyTime T1 T2 p q nv) ⟨emb .hd,inp,F q⟩ = ⟨emb .hd,inp,F (q+1)⟩ := by
    intro q hqn
    have hrem : n2-q = (n2-(q+1))+1 := by omega
    have htop : F q (v 12) = true :: (List.replicate (n2-(q+1)) true ++ false :: rest) := by
      rw [hFctr, hrem, List.replicate_succ, List.cons_append]
    have s1 : step P ⟨emb .hd,inp,F q⟩
        = some ⟨emb (.body (.e0 (.pr (.t1 (.tri .sep))))),inp,
            Function.update (F q) (v 12) (List.replicate (n2-(q+1)) true ++ false :: rest)⟩ := by
      simp [step, hP .hd, innerLoopCode, htop]
    rw [iter_step' P s1]
    rw [innerBody_component P v hv (fun t => emb (.body t)) (emb .hd) fail
      (fun s => by rw [hP (.body s)]; rfl) T1 T2 p q nv restN inp
      (Function.update (F q) (v 12) (List.replicate (n2-(q+1)) true ++ false :: rest))
      (by rw [Function.update_noteq (vne hv (by decide) : (v 0) ≠ (v 12)),
          hFother 0 (by decide) (by decide) (by decide) q]; exact hp)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 1) ≠ (v 12)), hF1])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 2) ≠ (v 12)),
          hFother 2 (by decide) (by decide) (by decide) q]; exact ht1)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 3) ≠ (v 12)),
          hFother 3 (by decide) (by decide) (by decide) q]; exact ht2)
      hb1 (hb2 q hqn)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 4) ≠ (v 12)),
          hFother 4 (by decide) (by decide) (by decide) q]; exact hn)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 6) ≠ (v 12)),
          hFother 6 (by decide) (by decide) (by decide) q]; exact htmp)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 8) ≠ (v 12)),
          hFother 8 (by decide) (by decide) (by decide) q]; exact hidx)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 9) ≠ (v 12)),
          hFother 9 (by decide) (by decide) (by decide) q]; exact ho1)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 10) ≠ (v 12)),
          hFother 10 (by decide) (by decide) (by decide) q]; exact ho2)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 5) ≠ (v 12)),
          hFother 5 (by decide) (by decide) (by decide) q]; exact hacc)]
    congr 1
    funext y
    rw [Function.update_noteq (vne hv (by decide) : (v 11) ≠ (v 12)), hF11,
      Function.update_noteq (vne hv (by decide) : (v 1) ≠ (v 12)), hF1]
    by_cases h1 : y = v 1
    · subst h1
      simp only [Function.update_same, hFdef, Function.update_noteq h112,
        Function.update_noteq h111, Function.update_same, List.replicate_succ, List.cons_append]
    · by_cases h11 : y = v 11
      · subst h11
        simp only [Function.update_noteq h1, Function.update_same, hFdef,
          Function.update_noteq h1112, Function.update_same, innerBlocks]
      · by_cases h12 : y = v 12
        · subst h12
          simp only [Function.update_noteq h1, Function.update_noteq h11, Function.update_same,
            hFdef]
        · simp only [Function.update_noteq h1, Function.update_noteq h11,
            Function.update_noteq h12, hFdef]
  have hfin : step P ⟨emb .hd,inp,F n2⟩
      = some ⟨exit,inp,Function.update (F n2) (v 12) rest⟩ := by
    have hz : F n2 (v 12) = false :: rest := by
      rw [hFctr, Nat.sub_self, List.replicate_zero, List.nil_append]
    simp [step, hP .hd, innerLoopCode, hz]
  have hres : Function.update (F n2) (v 12) rest
      = Function.update (Function.update (Function.update st
          (v 1) (List.replicate n2 true ++ [false]))
          (v 11) (innerBlocks T1 T2 p nv n2 (st (v 11)))) (v 12) rest := by
    simp only [hFdef, Function.update_idem]
  have main := loop_chain P (emb .hd) exit inp (Function.update (F n2) (v 12) rest) n2 F
    (fun q => 1+innerBodyTime T1 T2 p q nv) hstep hfin
  rw [hF0] at main
  unfold innerLoopTime
  rw [main, hres]


/-! ## The outer body: one first-component state

One pass of the outer loop. The inner control counter is refilled by duplicating
the stored state count, the inner loop of v1667 runs, the inner state counter is
reset and the outer one advanced. Like the inner body, the net effect is on two
stacks only: the output table grows and the outer counter goes up by one.
-/

inductive OBSt
  | rf (x : DupSt)
  | inr (x : ILSt)
  | cl
  | rs
  | inc
  deriving DecidableEq

def outerBodyCode (v : Fin 16 → Fin k) (emb : OBSt → Q) (exit fail : Q) : OBSt → Instr Q k
  | .rf x => dupCode (v 4) (v 6) (v 12) (fun t => emb (.rf t)) (emb (.inr .hd)) x
  | .inr x => innerLoopCode v (fun t => emb (.inr t)) (emb .cl) fail x
  | .cl => clearCode (v 1) (emb .cl) (emb .rs)
  | .rs => .push (v 1) false (emb .inc)
  | .inc => .push (v 0) true exit

def outerBodyTime (T1 T2 : List Nat) (p nv : Nat) : Nat :=
  dupTime (List.replicate nv true ++ [false])
    +(innerLoopTime T1 T2 p nv nv+((nv+1)+(1+1)))

theorem outerBody_component (P : Q → Instr Q k) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : OBSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = outerBodyCode v emb exit fail s)
    (T1 T2 : List Nat) (p nv : Nat) (inp : List Bool) (st : Fin k → List Bool)
    (hp : st (v 0) = List.replicate p true ++ [false])
    (hq : st (v 1) = [false])
    (ht1 : st (v 2) = blocks T1) (ht2 : st (v 3) = blocks T2)
    (hb1 : 3*p+2 < T1.length) (hb2 : ∀ q, q < nv → 3*q+2 < T2.length)
    (hn : st (v 4) = List.replicate nv true ++ [false])
    (htmp : st (v 6) = []) (hidx : st (v 8) = [])
    (ho1 : st (v 9) = [false]) (ho2 : st (v 10) = [false]) (hacc : st (v 5) = [false])
    (hctr : st (v 12) = []) :
    iter P (outerBodyTime T1 T2 p nv) ⟨emb (.rf (.up .loop)),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st
          (v 11) (innerBlocks T1 T2 p nv nv (st (v 11)))) (v 0) (true :: st (v 0))⟩ := by
  have h612 : (v 6) ≠ (v 12) := vne hv (by decide)
  have h1112 : (v 11) ≠ (v 12) := vne hv (by decide)
  have h112 : (v 1) ≠ (v 12) := vne hv (by decide)
  have h011 : (v 0) ≠ (v 11) := vne hv (by decide)
  have h111 : (v 1) ≠ (v 11) := vne hv (by decide)
  have h01 : (v 0) ≠ (v 1) := vne hv (by decide)
  have sinc : ∀ u : Fin k → List Bool, step P ⟨emb .inc,inp,u⟩
      = some ⟨exit,inp,Function.update u (v 0) (true :: u (v 0))⟩ := by
    intro u; simp [step, hP .inc, outerBodyCode]
  have srs : ∀ u : Fin k → List Bool, step P ⟨emb .rs,inp,u⟩
      = some ⟨emb .inc,inp,Function.update u (v 1) (false :: u (v 1))⟩ := by
    intro u; simp [step, hP .rs, outerBodyCode]
  unfold outerBodyTime
  rw [iter_add]
  rw [dup_component P (v 4) (v 6) (v 12) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (fun t => emb (.rf t)) (emb (.inr .hd))
    (fun s => by rw [hP (.rf s)]; rfl) (List.replicate nv true ++ [false]) inp st hn htmp]
  have hA : Function.update (Function.update st (v 12)
      ((List.replicate nv true ++ [false]) ++ st (v 12))) (v 6) []
      = Function.update st (v 12) (List.replicate nv true ++ [false]) := by
    funext y
    by_cases h6 : y = v 6
    · subst h6
      rw [Function.update_same, Function.update_noteq h612, htmp]
    · by_cases h12 : y = v 12
      · subst h12
        rw [Function.update_noteq h6, Function.update_same, Function.update_same, hctr,
          List.append_nil]
      · rw [Function.update_noteq h6, Function.update_noteq h12, Function.update_noteq h12]
  rw [hA]
  rw [iter_add]
  rw [innerLoop_component P v hv (fun t => emb (.inr t)) (emb .cl) fail
    (fun s => by rw [hP (.inr s)]; rfl) T1 T2 p nv nv [] [] inp
    (Function.update st (v 12) (List.replicate nv true ++ [false]))
    (by rw [Function.update_noteq (vne hv (by decide) : (v 0) ≠ (v 12)), hp])
    (by rw [Function.update_noteq h112, hq])
    (by rw [Function.update_noteq (vne hv (by decide) : (v 2) ≠ (v 12)), ht1])
    (by rw [Function.update_noteq (vne hv (by decide) : (v 3) ≠ (v 12)), ht2])
    hb1 hb2
    (by rw [Function.update_noteq (vne hv (by decide) : (v 4) ≠ (v 12)), hn])
    (by rw [Function.update_noteq h612, htmp])
    (by rw [Function.update_noteq (vne hv (by decide) : (v 8) ≠ (v 12)), hidx])
    (by rw [Function.update_noteq (vne hv (by decide) : (v 9) ≠ (v 12)), ho1])
    (by rw [Function.update_noteq (vne hv (by decide) : (v 10) ≠ (v 12)), ho2])
    (by rw [Function.update_noteq (vne hv (by decide) : (v 5) ≠ (v 12)), hacc])
    (by rw [Function.update_same])]
  have hB : Function.update (Function.update (Function.update
      (Function.update st (v 12) (List.replicate nv true ++ [false]))
      (v 1) (List.replicate nv true ++ [false])) (v 11)
      (innerBlocks T1 T2 p nv nv (Function.update st (v 12)
        (List.replicate nv true ++ [false]) (v 11)))) (v 12) []
      = Function.update (Function.update st (v 1) (List.replicate nv true ++ [false]))
          (v 11) (innerBlocks T1 T2 p nv nv (st (v 11))) := by
    rw [Function.update_noteq h1112]
    funext y
    by_cases h12 : y = v 12
    · subst h12
      rw [Function.update_same, Function.update_noteq (Ne.symm h1112),
        Function.update_noteq (Ne.symm h112), hctr]
    · by_cases h11 : y = v 11
      · subst h11
        rw [Function.update_noteq h12, Function.update_same, Function.update_same]
      · by_cases h1 : y = v 1
        · subst h1
          rw [Function.update_noteq h12, Function.update_noteq h11, Function.update_same,
            Function.update_noteq h11, Function.update_same]
        · rw [Function.update_noteq h12, Function.update_noteq h11, Function.update_noteq h1,
            Function.update_noteq h11, Function.update_noteq h1, Function.update_noteq h12]
  rw [hB]
  rw [iter_add]
  rw [clear_component P (v 1) (emb .cl) (emb .rs) (hP .cl) nv [] inp
    (Function.update (Function.update st (v 1) (List.replicate nv true ++ [false])) (v 11)
      (innerBlocks T1 T2 p nv nv (st (v 11))))
    (by rw [Function.update_noteq h111, Function.update_same])]
  rw [iter_step' P (srs _), iter_one P (sinc _)]
  congr 1
  funext y
  by_cases h0 : y = v 0
  · subst h0
    simp only [Function.update_same, Function.update_noteq h01, Function.update_noteq h011]
  · by_cases h1 : y = v 1
    · subst h1
      simp only [Function.update_noteq h0, Function.update_same, Function.update_noteq h111,
        Function.update_idem, hq]
    · by_cases h11 : y = v 11
      · subst h11
        simp only [Function.update_noteq h0, Function.update_noteq h1, Function.update_same]
      · simp only [Function.update_noteq h0, Function.update_noteq h1, Function.update_noteq h11]


/-! ## The outer loop: the whole product table

The second loop. Its control counter, on stack 13, holds the first automaton's
state count; each pass writes the `nv` product states whose first component is
the current state. When it ends, the output stack holds the blocks of every
product state, in the order a single pour turns into the table.
-/

def outerBlocks (T1 T2 : List Nat) (nv : Nat) : Nat → List Bool → List Bool
  | 0, A => A
  | p+1, A => innerBlocks T1 T2 p nv nv (outerBlocks T1 T2 nv p A)

inductive OLSt
  | hd
  | body (x : OBSt)
  deriving DecidableEq

def outerLoopCode (v : Fin 16 → Fin k) (emb : OLSt → Q) (exit fail : Q) : OLSt → Instr Q k
  | .hd => .pop (v 13) (emb (.body (.rf (.up .loop)))) exit exit
  | .body x => outerBodyCode v (fun t => emb (.body t)) (emb .hd) fail x

def outerLoopTime (T1 T2 : List Nat) (nv n1 : Nat) : Nat :=
  chainTime (fun p => 1+outerBodyTime T1 T2 p nv) n1

theorem outerLoop_component (P : Q → Instr Q k) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : OLSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = outerLoopCode v emb exit fail s)
    (T1 T2 : List Nat) (nv n1 : Nat) (rest : List Bool)
    (inp : List Bool) (st : Fin k → List Bool)
    (hp : st (v 0) = [false])
    (hq : st (v 1) = [false])
    (ht1 : st (v 2) = blocks T1) (ht2 : st (v 3) = blocks T2)
    (hb1 : ∀ p, p < n1 → 3*p+2 < T1.length) (hb2 : ∀ q, q < nv → 3*q+2 < T2.length)
    (hn : st (v 4) = List.replicate nv true ++ [false])
    (htmp : st (v 6) = []) (hidx : st (v 8) = [])
    (ho1 : st (v 9) = [false]) (ho2 : st (v 10) = [false]) (hacc : st (v 5) = [false])
    (hin : st (v 12) = [])
    (hctr : st (v 13) = List.replicate n1 true ++ false :: rest) :
    iter P (outerLoopTime T1 T2 nv n1) ⟨emb .hd,inp,st⟩
      = ⟨exit,inp,Function.update (Function.update (Function.update st
          (v 0) (List.replicate n1 true ++ [false]))
          (v 11) (outerBlocks T1 T2 nv n1 (st (v 11)))) (v 13) rest⟩ := by
  have h013 : (v 0) ≠ (v 13) := vne hv (by decide)
  have h1113 : (v 11) ≠ (v 13) := vne hv (by decide)
  have h011 : (v 0) ≠ (v 11) := vne hv (by decide)
  set F : Nat → Fin k → List Bool := fun p =>
    Function.update (Function.update (Function.update st
      (v 0) (List.replicate p true ++ [false]))
      (v 11) (outerBlocks T1 T2 nv p (st (v 11)))) (v 13)
      (List.replicate (n1-p) true ++ false :: rest) with hFdef
  have hFother : ∀ (i : Fin 16), i ≠ 0 → i ≠ 11 → i ≠ 13 → ∀ p, F p (v i) = st (v i) := by
    intro i h0 h11 h13 p
    simp only [hFdef]
    rw [Function.update_noteq (vne hv h13), Function.update_noteq (vne hv h11),
      Function.update_noteq (vne hv h0)]
  have hF0 : F 0 = st := by
    funext y
    simp only [hFdef]
    by_cases h13 : y = v 13
    · subst h13
      rw [Function.update_same, Nat.sub_zero, ← hctr]
    · by_cases h11 : y = v 11
      · subst h11
        rw [Function.update_noteq h13, Function.update_same]
        rfl
      · by_cases h0 : y = v 0
        · subst h0
          rw [Function.update_noteq h13, Function.update_noteq h11, Function.update_same,
            List.replicate_zero, List.nil_append, ← hp]
        · rw [Function.update_noteq h13, Function.update_noteq h11, Function.update_noteq h0]
  have hFctr : ∀ p, F p (v 13) = List.replicate (n1-p) true ++ false :: rest := by
    intro p; simp only [hFdef, Function.update_same]
  have hF11 : ∀ p, F p (v 11) = outerBlocks T1 T2 nv p (st (v 11)) := by
    intro p
    simp only [hFdef, Function.update_noteq h1113, Function.update_same]
  have hF0' : ∀ p, F p (v 0) = List.replicate p true ++ [false] := by
    intro p
    simp only [hFdef, Function.update_noteq h013, Function.update_noteq h011, Function.update_same]
  have hstep : ∀ p, p < n1 →
      iter P (1+outerBodyTime T1 T2 p nv) ⟨emb .hd,inp,F p⟩ = ⟨emb .hd,inp,F (p+1)⟩ := by
    intro p hpn
    have hrem : n1-p = (n1-(p+1))+1 := by omega
    have htop : F p (v 13) = true :: (List.replicate (n1-(p+1)) true ++ false :: rest) := by
      rw [hFctr, hrem, List.replicate_succ, List.cons_append]
    have s1 : step P ⟨emb .hd,inp,F p⟩
        = some ⟨emb (.body (.rf (.up .loop))),inp,
            Function.update (F p) (v 13) (List.replicate (n1-(p+1)) true ++ false :: rest)⟩ := by
      simp [step, hP .hd, outerLoopCode, htop]
    rw [iter_step' P s1]
    rw [outerBody_component P v hv (fun t => emb (.body t)) (emb .hd) fail
      (fun s => by rw [hP (.body s)]; rfl) T1 T2 p nv inp
      (Function.update (F p) (v 13) (List.replicate (n1-(p+1)) true ++ false :: rest))
      (by rw [Function.update_noteq (vne hv (by decide) : (v 0) ≠ (v 13)), hF0'])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 1) ≠ (v 13)),
          hFother 1 (by decide) (by decide) (by decide) p]; exact hq)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 2) ≠ (v 13)),
          hFother 2 (by decide) (by decide) (by decide) p]; exact ht1)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 3) ≠ (v 13)),
          hFother 3 (by decide) (by decide) (by decide) p]; exact ht2)
      (hb1 p hpn) hb2
      (by rw [Function.update_noteq (vne hv (by decide) : (v 4) ≠ (v 13)),
          hFother 4 (by decide) (by decide) (by decide) p]; exact hn)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 6) ≠ (v 13)),
          hFother 6 (by decide) (by decide) (by decide) p]; exact htmp)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 8) ≠ (v 13)),
          hFother 8 (by decide) (by decide) (by decide) p]; exact hidx)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 9) ≠ (v 13)),
          hFother 9 (by decide) (by decide) (by decide) p]; exact ho1)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 10) ≠ (v 13)),
          hFother 10 (by decide) (by decide) (by decide) p]; exact ho2)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 5) ≠ (v 13)),
          hFother 5 (by decide) (by decide) (by decide) p]; exact hacc)
      (by rw [Function.update_noteq (vne hv (by decide) : (v 12) ≠ (v 13)),
          hFother 12 (by decide) (by decide) (by decide) p]; exact hin)]
    congr 1
    funext y
    rw [Function.update_noteq (vne hv (by decide) : (v 11) ≠ (v 13)), hF11,
      Function.update_noteq (vne hv (by decide) : (v 0) ≠ (v 13)), hF0']
    by_cases h0 : y = v 0
    · subst h0
      simp only [Function.update_same, hFdef, Function.update_noteq h013,
        Function.update_noteq h011, Function.update_same, List.replicate_succ, List.cons_append]
    · by_cases h11 : y = v 11
      · subst h11
        simp only [Function.update_noteq h0, Function.update_same, hFdef,
          Function.update_noteq h1113, Function.update_same, outerBlocks]
      · by_cases h13 : y = v 13
        · subst h13
          simp only [Function.update_noteq h0, Function.update_noteq h11, Function.update_same,
            hFdef]
        · simp only [Function.update_noteq h0, Function.update_noteq h11,
            Function.update_noteq h13, hFdef]
  have hfin : step P ⟨emb .hd,inp,F n1⟩
      = some ⟨exit,inp,Function.update (F n1) (v 13) rest⟩ := by
    have hz : F n1 (v 13) = false :: rest := by
      rw [hFctr, Nat.sub_self, List.replicate_zero, List.nil_append]
    simp [step, hP .hd, outerLoopCode, hz]
  have hres : Function.update (F n1) (v 13) rest
      = Function.update (Function.update (Function.update st
          (v 0) (List.replicate n1 true ++ [false]))
          (v 11) (outerBlocks T1 T2 nv n1 (st (v 11)))) (v 13) rest := by
    simp only [hFdef, Function.update_idem]
  have main := loop_chain P (emb .hd) exit inp (Function.update (F n1) (v 13) rest) n1 F
    (fun p => 1+outerBodyTime T1 T2 p nv) hstep hfin
  rw [hF0] at main
  unfold outerLoopTime
  rw [main, hres]


/-! ## What the output stack holds

The emissions build the table backwards, because a stack grows at the top. These
identities say exactly what is there: the reverse of the blocks of the product's
table. So one pour — which reverses — turns the output stack into a table in the
same format as the two input tables, ready to be read by the very components
that read them.
-/

def prodRow (T1 T2 : List Nat) (nv p : Nat) : Nat → List Nat
  | 0 => []
  | q+1 => prodRow T1 T2 nv p q ++ prodEntries T1 T2 p q nv

def prodTable (T1 T2 : List Nat) (nv : Nat) : Nat → List Nat
  | 0 => []
  | p+1 => prodTable T1 T2 nv p ++ prodRow T1 T2 nv p nv

theorem emitBlocks_eq (es : List Nat) (A : List Bool) :
    emitBlocks es A = (blocks es).reverse ++ A := by
  induction es generalizing A with
  | nil => simp [emitBlocks, blocks]
  | cons e es ih =>
    simp only [emitBlocks, blocks, ih, List.reverse_append, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.singleton_append, List.cons_append,
      List.nil_append]

theorem innerBlocks_eq (T1 T2 : List Nat) (p nv q : Nat) (A : List Bool) :
    innerBlocks T1 T2 p nv q A = (blocks (prodRow T1 T2 nv p q)).reverse ++ A := by
  induction q generalizing A with
  | zero => simp [innerBlocks, prodRow, blocks]
  | succ q ih =>
    simp only [innerBlocks, prodRow, emitBlocks_eq, ih, blocks_append, List.reverse_append,
      List.append_assoc]

theorem outerBlocks_eq (T1 T2 : List Nat) (nv n1 : Nat) (A : List Bool) :
    outerBlocks T1 T2 nv n1 A = (blocks (prodTable T1 T2 nv n1)).reverse ++ A := by
  induction n1 generalizing A with
  | zero => simp [outerBlocks, prodTable, blocks]
  | succ n ih =>
    simp only [outerBlocks, prodTable, innerBlocks_eq, ih, blocks_append, List.reverse_append,
      List.append_assoc]

/-- The product table has three entries for each of the `n1*nv` product states. -/
theorem prodRow_length (T1 T2 : List Nat) (nv p q : Nat) :
    (prodRow T1 T2 nv p q).length = 3*q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [prodRow, List.length_append, ih, prodEntries, List.length_cons, List.length_nil]
    omega

theorem prodTable_length (T1 T2 : List Nat) (nv n1 : Nat) :
    (prodTable T1 T2 nv n1).length = 3*(n1*nv) := by
  induction n1 with
  | zero => simp [prodTable]
  | succ n ih =>
    simp only [prodTable, List.length_append, ih, prodRow_length]
    ring


/-! ## Writing one entry of a table in place

Reachability needs the opposite of a lookup: given an index, SET that entry.
The table is opened at the index (v1645's skip), the entry there is cleared
(v1663) and rewritten as the value one, and the part that was skipped is poured
back. The result is the table with one entry replaced, in the same format.
-/

inductive SetSt
  | sk (x : KSt)
  | cl
  | ps
  | pt
  | mv (x : MSt)
  deriving DecidableEq

def setOneCode (idx tab tmp : Fin k) (emb : SetSt → Q) (exit fail : Q) : SetSt → Instr Q k
  | .sk x => skipCode idx tab tmp (fun t => emb (.sk t)) (emb .cl) fail x
  | .cl => clearCode tab (emb .cl) (emb .ps)
  | .ps => .push tab false (emb .pt)
  | .pt => .push tab true (emb (.mv .loop))
  | .mv x => moveCode tmp tab (fun t => emb (.mv t)) exit x

def setOneTime (T : List Nat) (j : Nat) : Nat :=
  (3*j+2*(T.take j).sum+1)
    +((T.getD j 0+1)+(1+(1+(2*(blocks (T.take j)).reverse.length+1))))

theorem setOne_component (P : Q → Instr Q k) (idx tab tmp : Fin k)
    (hit : idx ≠ tab) (him : idx ≠ tmp) (htm : tab ≠ tmp)
    (emb : SetSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = setOneCode idx tab tmp emb exit fail s)
    (T : List Nat) (j : Nat) (hj : j < T.length)
    (inp : List Bool) (st : Fin k → List Bool)
    (hidx : st idx = List.replicate j true ++ [false])
    (htab : st tab = blocks T) (htmp : st tmp = []) :
    iter P (setOneTime T j) ⟨emb (.sk .loop),inp,st⟩
      = ⟨exit,inp,Function.update (Function.update st idx []) tab
          (blocks (T.take j ++ 1 :: T.drop (j+1)))⟩ := by
  have hlen : (T.take j).length = j := take_len T j (Nat.le_of_lt hj)
  have sps : ∀ u : Fin k → List Bool, step P ⟨emb .ps,inp,u⟩
      = some ⟨emb .pt,inp,Function.update u tab (false :: u tab)⟩ := by
    intro u; simp [step, hP .ps, setOneCode]
  have spt : ∀ u : Fin k → List Bool, step P ⟨emb .pt,inp,u⟩
      = some ⟨emb (.mv .loop),inp,Function.update u tab (true :: u tab)⟩ := by
    intro u; simp [step, hP .pt, setOneCode]
  unfold setOneTime
  rw [show 3*j+2*(T.take j).sum+1 = 3*(T.take j).length+2*(T.take j).sum+1 from by rw [hlen]]
  rw [iter_add]
  rw [skip_component P idx tab tmp hit him htm (fun t => emb (.sk t)) (emb .cl) fail
    (fun s => by rw [hP (.sk s)]; rfl) (T.take j) inp st []
    (List.replicate (T.getD j 0) true ++ false :: blocks (T.drop (j+1)))
    (by rw [hidx, hlen]) (by rw [htab]; exact blocks_split T j hj)]
  rw [iter_add]
  rw [clear_component P tab (emb .cl) (emb .ps) (hP .cl) (T.getD j 0)
    (blocks (T.drop (j+1))) inp
    (Function.update (Function.update (Function.update st idx []) tab
      (List.replicate (T.getD j 0) true ++ false :: blocks (T.drop (j+1)))) tmp
      ((blocks (T.take j)).reverse ++ st tmp))
    (by rw [Function.update_noteq htm, Function.update_same])]
  rw [iter_step' P (sps _), iter_step' P (spt _)]
  rw [Function.update_same, Function.update_same]
  rw [move_component P tmp tab (Ne.symm htm) (fun t => emb (.mv t)) exit
    (fun s => by rw [hP (.mv s)]; rfl) ((blocks (T.take j)).reverse) inp _
    (by
      rw [Function.update_noteq (Ne.symm htm), Function.update_noteq (Ne.symm htm),
        Function.update_noteq (Ne.symm htm), Function.update_same, htmp, List.append_nil])]
  congr 1
  funext y
  by_cases hy : y = tab
  · subst hy
    simp only [Function.update_same, Function.update_noteq htm, Function.update_idem,
      List.reverse_reverse, blocks_append, blocks, List.append_assoc, List.cons_append,
      List.nil_append, List.replicate, List.singleton_append]
  · by_cases hz : y = tmp
    · subst hz
      simp only [Function.update_noteq hy, Function.update_same, Function.update_idem,
        Function.update_noteq hy, Function.update_noteq (Ne.symm him), htmp]
    · by_cases hw : y = idx
      · subst hw
        simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hy,
          Function.update_noteq hz, Function.update_same]
      · simp only [Function.update_noteq hy, Function.update_noteq hz, Function.update_noteq hw]


def markSet (M : List Nat) (d : Nat) : List Nat := M.take d ++ 1 :: M.drop (d+1)

theorem markSet_length (M : List Nat) (d : Nat) (h : d < M.length) :
    (markSet M d).length = M.length := by
  simp only [markSet, List.length_append, List.length_cons, List.length_take, List.length_drop]
  omega

/-! ## Spreading a mark along one transition

The marking sweep's atom: read where state `r` goes on one bit, and mark that
state. The marks are a table with one entry per state, `0` or `1`, in the same
block format as the transition table, so the two operations that meet here are
the lookup of v1656 and the in-place write of v1670.

The stack assignment is the one the product construction uses; stack 14, spare
until now, holds the marks.
-/

inductive SPSt
  | rd (x : EntrySt)
  | set (x : SetSt)
  | rp
  deriving DecidableEq

def spreadCode (off : Nat) (v : Fin 16 → Fin k) (emb : SPSt → Q) (exit fail : Q) :
    SPSt → Instr Q k
  | .rd x =>
    entryCode off (v 0) (v 6) (v 7) (v 8) (v 2) (v 9) (fun t => emb (.rd t))
      (emb (.set (.sk .loop))) fail x
  | .set x => setOneCode (v 9) (v 14) (v 6) (fun t => emb (.set t)) (emb .rp) fail x
  | .rp => .push (v 9) false exit

def spreadTime (T M : List Nat) (r off : Nat) : Nat :=
  entryTime off r (T.take (3*r+off)) (T.getD (3*r+off) 0)
    +(setOneTime M (T.getD (3*r+off) 0)+1)

theorem spread_component (P : Q → Instr Q k) (off : Nat) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : SPSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = spreadCode off v emb exit fail s)
    (T M : List Nat) (r : Nat)
    (inp : List Bool) (st : Fin k → List Bool)
    (hr : st (v 0) = List.replicate r true ++ [false])
    (ht : st (v 2) = blocks T) (hm : st (v 14) = blocks M)
    (htmp : st (v 6) = []) (hidx : st (v 8) = []) (ho : st (v 9) = [false])
    (hb : 3*r+off < T.length) (hd : T.getD (3*r+off) 0 < M.length) :
    iter P (spreadTime T M r off) ⟨emb (.rd (.tri .sep)),inp,st⟩
      = ⟨exit,inp,Function.update st (v 14) (blocks (markSet M (T.getD (3*r+off) 0)))⟩ := by
  have h914 : (v 9) ≠ (v 14) := vne hv (by decide)
  have h96 : (v 9) ≠ (v 6) := vne hv (by decide)
  have h146 : (v 14) ≠ (v 6) := vne hv (by decide)
  have h92 : (v 9) ≠ (v 2) := vne hv (by decide)
  have h62 : (v 6) ≠ (v 2) := vne hv (by decide)
  have srp : ∀ u : Fin k → List Bool, step P ⟨emb .rp,inp,u⟩
      = some ⟨exit,inp,Function.update u (v 9) (false :: u (v 9))⟩ := by
    intro u; simp [step, hP .rp, spreadCode]
  unfold spreadTime
  rw [iter_add]
  rw [entry_component P off (v 0) (v 6) (v 7) (v 8) (v 2) (v 9)
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (fun t => emb (.rd t)) (emb (.set (.sk .loop))) fail
    (fun s => by rw [hP (.rd s)]; rfl) r (T.take (3*r+off)) (T.getD (3*r+off) 0)
    (blocks (T.drop (3*r+off+1))) inp st hr htmp hidx
    (by rw [ht]; exact blocks_split T (3*r+off) hb)
    (by rw [take_len T (3*r+off) (Nat.le_of_lt hb)])]
  have hA : Function.update (Function.update (Function.update st (v 6) []) (v 9)
      (List.replicate (T.getD (3*r+off) 0) true ++ st (v 9))) (v 2) (st (v 2))
      = Function.update st (v 9) (List.replicate (T.getD (3*r+off) 0) true ++ [false]) := by
    funext y
    by_cases h2 : y = v 2
    · subst h2
      simp only [Function.update_same, Function.update_noteq (Ne.symm h92)]
    · by_cases h9 : y = v 9
      · subst h9
        simp only [Function.update_noteq h2, Function.update_same, ho]
      · by_cases h6 : y = v 6
        · subst h6
          simp only [Function.update_noteq h2, Function.update_noteq h9, Function.update_same,
            Function.update_noteq h9, htmp]
        · simp only [Function.update_noteq h2, Function.update_noteq h9, Function.update_noteq h6]
  rw [hA]
  rw [iter_add]
  rw [setOne_component P (v 9) (v 14) (v 6) h914 h96 h146 (fun t => emb (.set t)) (emb .rp) fail
    (fun s => by rw [hP (.set s)]; rfl) M (T.getD (3*r+off) 0) hd inp
    (Function.update st (v 9) (List.replicate (T.getD (3*r+off) 0) true ++ [false]))
    (by rw [Function.update_same])
    (by rw [Function.update_noteq (Ne.symm h914), hm])
    (by rw [Function.update_noteq (Ne.symm h96), htmp])]
  rw [iter_one P (srp _)]
  congr 1
  funext y
  by_cases h9 : y = v 9
  · subst h9
    simp only [Function.update_same, Function.update_noteq h914, Function.update_idem, ho]
  · by_cases h14 : y = v 14
    · subst h14
      simp only [Function.update_noteq h9, Function.update_same, markSet]
    · simp only [Function.update_noteq h9, Function.update_noteq h14, Function.update_noteq h9]


/-! ## One state's turn in the marking sweep

Look up whether the state is marked; if it is, spread the mark along both of its
transitions. The mark is read as a counter of value `0` or `1`, and the test is
a single pop: a marker means marked, an empty stack means not.
-/

def markStepM (T M : List Nat) (r : Nat) : List Nat :=
  if M.getD r 0 = 1 then markSet (markSet M (T.getD (3*r) 0)) (T.getD (3*r+1) 0) else M

inductive MSSt
  | dup (x : DupSt)
  | rd (x : ReadSt)
  | tst
  | s0 (x : SPSt)
  | s1 (x : SPSt)
  deriving DecidableEq

def markStepCode (v : Fin 16 → Fin k) (emb : MSSt → Q) (exit fail : Q) : MSSt → Instr Q k
  | .dup x => dupCode (v 0) (v 6) (v 15) (fun t => emb (.dup t)) (emb (.rd (.sk .loop))) x
  | .rd x => readCode (v 15) (v 14) (v 6) (v 10) (fun t => emb (.rd t)) (emb .tst) fail x
  | .tst => .pop (v 10) (emb (.s0 (.rd (.tri .sep)))) exit exit
  | .s0 x => spreadCode 0 v (fun t => emb (.s0 t)) (emb (.s1 (.rd (.tri .sep)))) fail x
  | .s1 x => spreadCode 1 v (fun t => emb (.s1 t)) exit fail x

def markStepTime (T M : List Nat) (r : Nat) : Nat :=
  dupTime (List.replicate r true ++ [false])
    +(readTime (M.take r) (M.getD r 0)
      +(1+(if M.getD r 0 = 1 then
          spreadTime T M r 0+spreadTime T (markSet M (T.getD (3*r) 0)) r 1 else 0)))

theorem markStep_component (P : Q → Instr Q k) (v : Fin 16 → Fin k)
    (hv : Function.Injective v) (emb : MSSt → Q) (exit fail : Q)
    (hP : ∀ s, P (emb s) = markStepCode v emb exit fail s)
    (T M : List Nat) (r : Nat)
    (inp : List Bool) (st : Fin k → List Bool)
    (hr : st (v 0) = List.replicate r true ++ [false])
    (ht : st (v 2) = blocks T) (hm : st (v 14) = blocks M)
    (htmp : st (v 6) = []) (hidx : st (v 8) = []) (ho : st (v 9) = [false])
    (hten : st (v 10) = []) (hfif : st (v 15) = [])
    (hrM : r < M.length) (hm1 : M.getD r 0 ≤ 1)
    (hb : 3*r+1 < T.length)
    (hd0 : T.getD (3*r) 0 < M.length) (hd1 : T.getD (3*r+1) 0 < M.length) :
    iter P (markStepTime T M r) ⟨emb (.dup (.up .loop)),inp,st⟩
      = ⟨exit,inp,Function.update st (v 14) (blocks (markStepM T M r))⟩ := by
  have h156 : (v 15) ≠ (v 6) := vne hv (by decide)
  have h1514 : (v 15) ≠ (v 14) := vne hv (by decide)
  have h1510 : (v 15) ≠ (v 10) := vne hv (by decide)
  have h1410 : (v 14) ≠ (v 10) := vne hv (by decide)
  have h610 : (v 6) ≠ (v 10) := vne hv (by decide)
  have h1415 : (v 14) ≠ (v 15) := vne hv (by decide)
  have h1015 : (v 10) ≠ (v 15) := vne hv (by decide)
  have h1014 : (v 10) ≠ (v 14) := vne hv (by decide)
  unfold markStepTime
  rw [iter_add]
  rw [dup_component P (v 0) (v 6) (v 15) (vne hv (by decide)) (vne hv (by decide))
    (vne hv (by decide)) (fun t => emb (.dup t)) (emb (.rd (.sk .loop)))
    (fun s => by rw [hP (.dup s)]; rfl) (List.replicate r true ++ [false]) inp st hr htmp]
  have hA : Function.update (Function.update st (v 15)
      ((List.replicate r true ++ [false]) ++ st (v 15))) (v 6) []
      = Function.update st (v 15) (List.replicate r true ++ [false]) := by
    funext y
    by_cases h6 : y = v 6
    · subst h6
      rw [Function.update_same, Function.update_noteq (Ne.symm h156), htmp]
    · by_cases h15 : y = v 15
      · subst h15
        rw [Function.update_noteq h6, Function.update_same, Function.update_same, hfif,
          List.append_nil]
      · rw [Function.update_noteq h6, Function.update_noteq h15, Function.update_noteq h15]
  rw [hA]
  rw [iter_add]
  rw [read_component P (v 15) (v 14) (v 6) (v 10) h1514 h156 h1510
    (vne hv (by decide)) (vne hv (by decide)) (vne hv (by decide))
    (fun t => emb (.rd t)) (emb .tst) fail (fun s => by rw [hP (.rd s)]; rfl)
    (M.take r) (M.getD r 0) (blocks (M.drop (r+1))) [] inp
    (Function.update st (v 15) (List.replicate r true ++ [false]))
    (by rw [Function.update_same, take_len M r (Nat.le_of_lt hrM)])
    (by rw [Function.update_noteq h1415, hm]; exact blocks_split M r hrM)
    (by rw [Function.update_noteq (Ne.symm h156), htmp])]
  have hB : Function.update (Function.update (Function.update
      (Function.update st (v 15) (List.replicate r true ++ [false])) (v 15) []) (v 10)
      (List.replicate (M.getD r 0) true ++ Function.update st (v 15)
        (List.replicate r true ++ [false]) (v 10))) (v 14)
      (Function.update st (v 15) (List.replicate r true ++ [false]) (v 14))
      = Function.update st (v 10) (List.replicate (M.getD r 0) true) := by
    rw [Function.update_noteq h1015, hten, List.append_nil]
    funext y
    by_cases h14 : y = v 14
    · subst h14
      simp only [Function.update_same, Function.update_noteq h1410,
        Function.update_noteq h1415, hm]
    · by_cases h10 : y = v 10
      · subst h10
        simp only [Function.update_noteq h14, Function.update_same,
          Function.update_noteq h1015]
      · by_cases h15 : y = v 15
        · subst h15
          simp only [Function.update_noteq h14, Function.update_noteq h10,
            Function.update_same, hfif]
        · simp only [Function.update_noteq h14, Function.update_noteq h10,
            Function.update_noteq h15]
  rw [hB]
  have hcases : M.getD r 0 = 0 ∨ M.getD r 0 = 1 := by omega
  rcases hcases with hv0 | hv0
  · -- the state is not marked
    have hne1 : ¬(M.getD r 0 = 1) := by omega
    simp only [markStepM, hv0, if_neg (by decide : ¬(0 = 1)), List.replicate_zero,
      Nat.add_zero]
    have s1 : step P ⟨emb .tst,inp,Function.update st (v 10) []⟩
        = some ⟨exit,inp,Function.update st (v 10) []⟩ := by
      simp [step, hP .tst, markStepCode, Function.update_same]
    rw [iter_one P s1]
    congr 1
    funext y
    by_cases h10 : y = v 10
    · subst h10
      rw [Function.update_same, Function.update_noteq h1014, hten]
    · by_cases h14 : y = v 14
      · subst h14
        rw [Function.update_noteq h10, Function.update_same, hm]
      · rw [Function.update_noteq h10, Function.update_noteq h14]
  · -- the state is marked: spread along both transitions
    simp only [markStepM, hv0, if_pos rfl, if_true, List.replicate_one]
    have s1 : step P ⟨emb .tst,inp,Function.update st (v 10) [true]⟩
        = some ⟨emb (.s0 (.rd (.tri .sep))),inp,Function.update st (v 10) []⟩ := by
      simp [step, hP .tst, markStepCode, Function.update_same]
    rw [iter_step' P s1]
    rw [iter_add]
    rw [spread_component P 0 v hv (fun t => emb (.s0 t)) (emb (.s1 (.rd (.tri .sep)))) fail
      (fun s => by rw [hP (.s0 s)]; rfl) T M r inp (Function.update st (v 10) [])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 0) ≠ (v 10)), hr])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 2) ≠ (v 10)), ht])
      (by rw [Function.update_noteq h1410, hm])
      (by rw [Function.update_noteq h610, htmp])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 8) ≠ (v 10)), hidx])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 9) ≠ (v 10)), ho])
      (by omega) hd0]
    simp only [Nat.add_zero]
    rw [spread_component P 1 v hv (fun t => emb (.s1 t)) exit fail
      (fun s => by rw [hP (.s1 s)]; rfl) T (markSet M (T.getD (3*r) 0)) r inp
      (Function.update (Function.update st (v 10) []) (v 14)
        (blocks (markSet M (T.getD (3*r) 0))))
      (by rw [Function.update_noteq (vne hv (by decide) : (v 0) ≠ (v 14)),
          Function.update_noteq (vne hv (by decide) : (v 0) ≠ (v 10)), hr])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 2) ≠ (v 14)),
          Function.update_noteq (vne hv (by decide) : (v 2) ≠ (v 10)), ht])
      (by rw [Function.update_same])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 6) ≠ (v 14)),
          Function.update_noteq h610, htmp])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 8) ≠ (v 14)),
          Function.update_noteq (vne hv (by decide) : (v 8) ≠ (v 10)), hidx])
      (by rw [Function.update_noteq (vne hv (by decide) : (v 9) ≠ (v 14)),
          Function.update_noteq (vne hv (by decide) : (v 9) ≠ (v 10)), ho])
      hb (by rw [markSet_length M (T.getD (3*r) 0) hd0]; exact hd1)]
    congr 1
    funext y
    by_cases h14 : y = v 14
    · subst h14
      simp only [Function.update_same]
    · by_cases h10 : y = v 10
      · subst h10
        simp only [Function.update_noteq h14, Function.update_same, hten]
      · simp only [Function.update_noteq h14, Function.update_noteq h10]

end NSSE.BitMachineK
