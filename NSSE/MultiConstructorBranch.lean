import NSSE.MultiConstructorSelectorHead
import NSSE.P0DZDecision

/-! A concrete full D/Z branch built from an original input and a finite
reset-selector choice. Acceptance is the existing all-origin ray predicate;
coverage of all first original witnesses is a separate theorem. -/
namespace NSSE.MultiConstructorBranch
open MultiConstructorConstraints MultiConstructorTokens MultiConstructorRawTrace
open MultiConstructorRawValidity MultiConstructorSelectorHead MultiConstructorTrees
variable {H : Type*} {arity : H → Nat} {n : Nat}

structure Parameters (arity : H → Nat) (n : Nat) where
  input : Constraints arity n
  left : Fin n
  right : Fin n
  reset : Row n
  fallback : H
  endX : Label H
  endY : Label H

abbrev State (n : Nat) := Row n × Row n

theorem card_row (n : Nat) : Fintype.card (Row n) = (2^n)^2 := by
  simp only [Row,Tokens,Fintype.card_prod,Fintype.card_finset,Fintype.card_fin]
  ring

theorem card_state (n : Nat) : Fintype.card (State n) = (2^n)^4 := by
  simp only [State,Row,Tokens,Fintype.card_prod,Fintype.card_finset,Fintype.card_fin]
  ring

variable [DecidableEq H]

def output (C : Parameters arity n) (s : State n) : H := choose C.input s.2 C.fallback

def successor (C : Parameters arity n) (s : State n) (i : Nat) : State n :=
  (step C.input s.1 i,next C.input C.reset s.2 i)

def Ready (C : Parameters arity n) (s : State n) : Prop :=
  Valid C.input s.1 ∧ Proper C.input s.2 ∧ Compatible C.input s.1 (output C s)

def readyDecision (C : Parameters arity n) (s : State n) : Decidable (Ready C s) := by
  letI := validDecision C.input s.1
  letI := properDecision C.input s.2
  letI := compatibleDecision C.input s.1 (output C s)
  unfold Ready
  infer_instance

def StepGuard (C : Parameters arity n) (s : State n) (i : Nat) : Prop :=
  Ready C s ∧ i < arity (output C s)

def stepDecision (C : Parameters arity n) (s : State n) (i : Nat) : Decidable (StepGuard C s i) := by
  letI := readyDecision C s
  unfold StepGuard
  infer_instance

def DGuard (C : Parameters arity n) (s : State n) (i : Nat) : Prop :=
  StepGuard C s i ∧ Ready C (successor C s i)

def dDecision (C : Parameters arity n) (s : State n) (i : Nat) : Decidable (DGuard C s i) := by
  letI := stepDecision C s i
  letI := readyDecision C (successor C s i)
  unfold DGuard
  infer_instance

def ZGuard (C : Parameters arity n) (s : State n) (i : Nat) : Prop :=
  StepGuard C s i ∧ Valid C.input (step C.input s.1 i) ∧
  UpperDomain C.input (step C.input s.1 i) C.endX ∧
  LowerDomain C.input (step C.input s.1 i) C.endY ∧ C.endX ≠ C.endY

def zDecision (C : Parameters arity n) (s : State n) (i : Nat) : Decidable (ZGuard C s i) := by
  letI := stepDecision C s i
  letI := validDecision C.input (step C.input s.1 i)
  letI := upperDomainDecision C.input (step C.input s.1 i) C.endX
  letI := lowerDomainDecision C.input (step C.input s.1 i) C.endY
  unfold ZGuard
  infer_instance

def raw : State n ⊕ Row n → Row n
  | .inl s => s.1
  | .inr s => s

def branch (C : Parameters arity n) (D : Nat) : P0DZBranch.Branch (State n) (Row n) (Fin D) H where
  initial := (initial C.input C.left C.right,initial C.input C.left C.right)
  next s i := @ite _ (DGuard C s i.val) (dDecision C s i.val) (some (successor C s i.val)) none
  final s i := @ite _ (ZGuard C s i.val) (zDecision C s i.val) (some (step C.input s.1 i.val)) none
  head := output C
  endX := C.endX
  endY := C.endY
  birth q s t r := s = false ∧ r = true ∧ ((raw q).1 ∩ (raw t).2).Nonempty

def birthDecision (C : Parameters arity n) (D : Nat) : P0DZDecision.BirthDecision (branch C D) := by
  intro q s t r
  change Decidable (s = false ∧ r = true ∧ ((raw q).1 ∩ (raw t).2).Nonempty)
  infer_instance

theorem next_iff (C : Parameters arity n) (D : Nat) (s t : State n) (i : Fin D) :
    (branch C D).next s i = some t ↔ DGuard C s i.val ∧ successor C s i.val = t := by
  by_cases hg : DGuard C s i.val <;> simp [branch,hg]

theorem final_iff (C : Parameters arity n) (D : Nat) (s : State n) (t : Row n) (i : Fin D) :
    (branch C D).final s i = some t ↔ ZGuard C s i.val ∧ step C.input s.1 i.val = t := by
  by_cases hg : ZGuard C s i.val <;> simp [branch,hg]

theorem next_raw (C : Parameters arity n) (D : Nat) (s t : State n) (i : Fin D)
    (he : (branch C D).next s i = some t) : t.1 = step C.input s.1 i.val :=
  (congrArg Prod.fst ((next_iff C D s t i).mp he).2).symm

theorem final_raw (C : Parameters arity n) (D : Nat) (s : State n) (t : Row n) (i : Fin D)
    (he : (branch C D).final s i = some t) : t = step C.input s.1 i.val :=
  ((final_iff C D s t i).mp he).2.symm

theorem ready_domains (C : Parameters arity n) (s : State n) (hr : Ready C s) :
    UpperDomain C.input s.1 (.node (output C s)) ∧ LowerDomain C.input s.1 (.node (output C s)) :=
  (common_domains C.input s.1 _).mpr hr.2.2

theorem step_raw_arity (C : Parameters arity n) (s : State n) (i : Nat)
    (hg : StepGuard C s i) : ArityOK C.input s.1 i :=
  compatible_arity C.input s.1 (output C s) i hg.1.2.2 hg.2

theorem branch_birth (C : Parameters arity n) (D : Nat) (q t : State n ⊕ Row n) :
    (branch C D).birth q false t true ↔ ∃ v ∈ (raw q).1, v ∈ (raw t).2 := by
  simp only [branch,true_and,Finset.Nonempty,Finset.mem_inter]

end NSSE.MultiConstructorBranch
