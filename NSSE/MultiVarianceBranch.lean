import NSSE.MultiVarianceSelectorStep
import NSSE.P0DZDecision

/-! Concrete finite signed D/Z branches. RAW and SELECTOR frames keep
separate signs. Births and final IDs use only the actual RAW frame; the
final Z guard imposes no readiness requirement on a selector successor. -/
namespace NSSE.MultiVarianceBranch
open MultiConstructorConstraints (Query)
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceTokenExact
open MultiVarianceClashCharacterization MultiVarianceLocalDecision MultiVarianceSelectorHead
variable {H : Type*} {arity : H → Nat} {n : Nat}

structure Parameters (arity : H → Nat) (n : Nat) where
  query : Query arity n
  reset : Frame n
  fallback : H
  endX : Label H
  endY : Label H

abbrev State (n : Nat) := Frame n × Frame n

theorem card_state (n : Nat) : Fintype.card (State n)=2^(4*n+2) := by
  calc
    Fintype.card (State n) = (2*4^n)^2 := by simp only [State,Fintype.card_prod,card_frames,pow_two]
    _ = (2^(2*n+1))^2 := by
      congr 1
      simp only [pow_add,pow_mul,pow_one]
      norm_num
      ring
    _ = 2^((2*n+1)*2) := (pow_mul _ _ _).symm
    _ = 2^(4*n+2) := by congr 1; omega

variable [DecidableEq H]

def output (C : Parameters arity n) (s : State n) : H := choose C.query.constraints s.2 C.fallback

def Ready (C : Parameters arity n) (s : State n) : Prop :=
  MultiVarianceSelectorHead.Ready C.query.constraints s.1 (output C s) ∧
    MultiVarianceSelectorHead.Ready C.query.constraints s.2 (output C s)

def readyDecision (C : Parameters arity n) (s : State n) : Decidable (Ready C s) := by
  letI := MultiVarianceSelectorHead.readyDecision C.query.constraints s.1 (output C s)
  letI := MultiVarianceSelectorHead.readyDecision C.query.constraints s.2 (output C s)
  unfold Ready
  infer_instance

def StepGuard (C : Parameters arity n) (s : State n) (i : Nat) : Prop := Ready C s ∧ i<arity (output C s)

def stepDecision (C : Parameters arity n) (s : State n) (i : Nat) : Decidable (StepGuard C s i) := by
  letI := readyDecision C s
  unfold StepGuard
  infer_instance

def EndValid (C : Parameters arity n) (F : Frame n) : Prop :=
  Compatible C.query.constraints F.sign F.x C.endX ∧
    Compatible C.query.constraints (!F.sign) F.y C.endY ∧
    (if F.sign then ¬C.endY ≤ C.endX else ¬C.endX ≤ C.endY)

def endDecision (C : Parameters arity n) (F : Frame n) : Decidable (EndValid C F) := by
  letI := compatibleDecision C.query.constraints F.sign F.x C.endX
  letI := compatibleDecision C.query.constraints (!F.sign) F.y C.endY
  unfold EndValid
  infer_instance

omit [DecidableEq H] in
theorem ends_distinct (C : Parameters arity n) (F : Frame n) (he : EndValid C F) : C.endX ≠ C.endY := by
  intro hh
  have hn := he.2.2
  rw [hh] at hn
  simp only [ite_self] at hn
  exact hn le_rfl

def raw : State n ⊕ Frame n → Frame n
  | .inl s => s.1
  | .inr F => F

def RawBirth (F : Frame n) (side : Bool) (G : Frame n) (other : Bool) : Prop :=
  inspectBirth (roleOf F.sign side) (tokensOf F side) (roleOf G.sign other) (tokensOf G other)=true

theorem no_same_vertex_birth (F : Frame n) (side : Bool) : ¬RawBirth F side F side := by
  unfold RawBirth inspectBirth
  cases roleOf F.sign side <;> simp

variable (pol : Polarity arity)

def successor (C : Parameters arity n) (s : State n) (i : Nat) : State n :=
  (MultiVarianceSelectorStep.step pol C.query.constraints s.1 (output C s) i,
    MultiVarianceSelectorStep.next pol C.query.constraints C.reset C.fallback s.2 i)

def DGuard (C : Parameters arity n) (s : State n) (i : Nat) : Prop :=
  StepGuard C s i ∧ Ready C (successor pol C s i)

def dDecision (C : Parameters arity n) (s : State n) (i : Nat) : Decidable (DGuard pol C s i) := by
  letI := stepDecision C s i
  letI := readyDecision C (successor pol C s i)
  unfold DGuard
  infer_instance

def ZGuard (C : Parameters arity n) (s : State n) (i : Nat) : Prop :=
  StepGuard C s i ∧ EndValid C (successor pol C s i).1

def zDecision (C : Parameters arity n) (s : State n) (i : Nat) : Decidable (ZGuard pol C s i) := by
  letI := stepDecision C s i
  letI := endDecision C (successor pol C s i).1
  unfold ZGuard
  infer_instance

def branch (C : Parameters arity n) (D : Nat) : P0DZBranch.Branch (State n) (Frame n) (Fin D) H where
  initial := (startFrame pol C.query,startFrame pol C.query)
  next s i := @ite _ (DGuard pol C s i.val) (dDecision pol C s i.val) (some (successor pol C s i.val)) none
  final s i := @ite _ (ZGuard pol C s i.val) (zDecision pol C s i.val) (some (successor pol C s i.val).1) none
  head := output C
  endX := C.endX
  endY := C.endY
  birth q s t r := RawBirth (raw q) s (raw t) r

def birthDecision (C : Parameters arity n) (D : Nat) : P0DZDecision.BirthDecision (branch pol C D) := by
  intro q s t r
  change Decidable (RawBirth (raw q) s (raw t) r)
  unfold RawBirth
  infer_instance

theorem next_iff (C : Parameters arity n) (D : Nat) (s t : State n) (i : Fin D) :
    (branch pol C D).next s i=some t ↔ DGuard pol C s i.val ∧ successor pol C s i.val=t := by
  by_cases hg : DGuard pol C s i.val <;> simp [branch,hg]

theorem final_iff (C : Parameters arity n) (D : Nat) (s : State n) (t : Frame n) (i : Fin D) :
    (branch pol C D).final s i=some t ↔ ZGuard pol C s i.val ∧ (successor pol C s i.val).1=t := by
  by_cases hg : ZGuard pol C s i.val <;> simp [branch,hg]

end NSSE.MultiVarianceBranch
