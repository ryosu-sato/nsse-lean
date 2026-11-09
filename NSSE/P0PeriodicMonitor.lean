import NSSE.P0PeriodicMonitorInvariant
import NSSE.P0ProperWords
import NSSE.P0PeriodicInspectionDecision
import Mathlib.Computability.DFA

/-! A concrete finite Boolean-array monitor for permanent comparisons in a
supplied periodic continuation. All transition decisions are finite; no
recognition or infinite-stream decidability premise is supplied. -/
namespace NSSE.P0PeriodicMonitor
open P0ProperMachine P0PeriodicDriver P0PeriodicFutures P0PeriodicMonitorInvariant
variable {Q A H : Type*} {r : Nat}

abbrev State (Q : Type*) (r : Nat) :=
  Q × ((Q × Fin r × Fin r) → Bool) × (Fin r → Bool) × Bool

theorem card_state [Fintype Q] [DecidableEq Q] (r : Nat) :
    Fintype.card (State Q r) = Fintype.card Q * 2^(Fintype.card Q*r^2+r+1) := by
  simp only [State,Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  rw [show 2^r*2 = 2^(r+1) by simp [pow_succ],← pow_add]
  congr 2
  simp only [pow_two,Nat.mul_assoc,Nat.add_assoc]

def originStep [DecidableEq Q] [DecidableEq A] (hr : 0 < r) (cycle : Fin r → A)
    (old : (Q × Fin r × Fin r) → Bool) (qnew : Q) (letter : A)
    (t : Q × Fin r × Fin r) : Bool :=
  decide ((qnew = t.1 ∧ t.2.1 = t.2.2) ∨
    ∃ d : Fin r, old (t.1,t.2.1,d) = true ∧ cycle d = letter ∧ advance hr d 1 = t.2.2)

def hitStep [Fintype Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A)
    (old : Fin r → Bool) (origins : (Q × Fin r × Fin r) → Bool)
    (qnew : Q) (letter : A) (c : Fin r) : Bool := by
  letI := birthDecision
  letI : DecidableRel (RotationEq hr cycle) := fun _ _ => by
    unfold RotationEq
    infer_instance
  exact decide ((∃ d : Fin r, old d = true ∧ cycle d = letter ∧ advance hr d 1 = c) ∨
    ∃ q p, origins (q,p,c) = true ∧ M.birth q qnew ∧ RotationEq hr cycle p c)

def start [DecidableEq Q] (M : Machine Q A H) (birthDecision : DecidableRel M.birth) :
    State Q r :=
  let diag := @decide (M.birth M.initial M.initial) (birthDecision _ _)
  (M.initial,(fun t => decide (M.initial = t.1 ∧ t.2.1 = t.2.2)),fun _ => diag,diag)

def step [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A)
    (s : State Q r) (letter : A) : State Q r :=
  let qnew := M.step s.1 letter
  let origins := originStep hr cycle s.2.1 qnew letter
  (qnew,origins,hitStep M birthDecision hr cycle s.2.2.1 origins qnew letter,
    s.2.2.2 || @decide (M.birth qnew qnew) (birthDecision _ _))

def trace [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) : Nat → State Q r
  | 0 => start M birthDecision
  | n+1 => step M birthDecision hr cycle (trace M birthDecision hr cycle z n) (z n)

def Invariant (M : Machine Q A H) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) (s : State Q r) : Prop :=
  s.1 = run M z n ∧
  (∀ q p c, s.2.1 (q,p,c) = true ↔ Origin M hr cycle z n q p c) ∧
  (∀ c, s.2.2.1 c = true ↔ Hit M hr cycle z n c) ∧
  (s.2.2.2 = true ↔ Diagonal M z n)

theorem invariant_start [DecidableEq Q] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) : Invariant M hr cycle z 0 (start M birthDecision) := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro q p c
    simp only [start,decide_eq_true_eq,origin_zero]
  · intro c
    simp only [start,decide_eq_true_eq,hit_zero]
  · simp only [start,decide_eq_true_eq,diagonal_zero]

theorem invariant_step [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) (s : State Q r) (hi : Invariant M hr cycle z n s) :
    Invariant M hr cycle z (n+1) (step M birthDecision hr cycle s (z n)) := by
  obtain ⟨hstate,ho,hh,hd⟩ := hi
  have hnew : M.step s.1 (z n) = run M z (n+1) := by rw [hstate,run_succ]
  have honew (q : Q) (p c : Fin r) :
      originStep hr cycle s.2.1 (M.step s.1 (z n)) (z n) (q,p,c) = true ↔
        Origin M hr cycle z (n+1) q p c := by
    simp only [originStep,decide_eq_true_eq,hnew,origin_succ]
    simp_rw [ho]
  refine ⟨hnew,honew,?_,?_⟩
  · intro c
    change hitStep M birthDecision hr cycle s.2.2.1
      (originStep hr cycle s.2.1 (M.step s.1 (z n)) (z n)) (M.step s.1 (z n)) (z n) c = true ↔ _
    simp only [hitStep,decide_eq_true_eq]
    simp_rw [hh,honew,hnew]
    exact (hit_succ M hr cycle z n c).symm
  · change (s.2.2.2 || @decide _ (birthDecision _ _)) = true ↔ _
    simp only [Bool.or_eq_true,decide_eq_true_eq,hd,hnew,diagonal_succ]

theorem invariant_trace [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) : Invariant M hr cycle z n (trace M birthDecision hr cycle z n) := by
  induction n with
  | zero => exact invariant_start M birthDecision hr cycle z
  | succ n ih => exact invariant_step M birthDecision hr cycle z n _ ih

def accepts (hr : 0 < r) (s : State Q r) : Bool := s.2.2.2 || s.2.2.1 (phase r hr 0)

theorem accepts_trace_iff [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) (hp : PeriodicFrom z n r hr cycle) :
    accepts hr (trace M birthDecision hr cycle z n) = true ↔ Permanent M z n := by
  have hi := invariant_trace M birthDecision hr cycle z n
  simp only [accepts,Bool.or_eq_true,hi.2.2.2,hi.2.2.1,permanent_iff M z n hr cycle hp]

def automaton [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A) : DFA A (State Q r) :=
  ⟨step M birthDecision hr cycle,start M birthDecision,fun s => accepts hr s = true⟩

theorem eval_prefix [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) :
    (automaton M birthDecision hr cycle).eval (P0ProperWords.prefixWord z n) =
      trace M birthDecision hr cycle z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hw : P0ProperWords.prefixWord z (n+1) = P0ProperWords.prefixWord z n ++ [z n] := by
      unfold P0ProperWords.prefixWord
      rw [List.ofFn_succ']
      rw [List.concat_eq_append]
      rfl
    rw [hw,DFA.eval_append_singleton,ih]
    rfl

theorem accepts_prefix_iff [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A)
    (z : Nat → A) (n : Nat) (hp : PeriodicFrom z n r hr cycle) :
    P0ProperWords.prefixWord z n ∈ (automaton M birthDecision hr cycle).accepts ↔ Permanent M z n := by
  rw [DFA.mem_accepts,eval_prefix]
  exact accepts_trace_iff M birthDecision hr cycle z n hp

theorem prefix_lasso (w : List A) (hr : 0 < r) (cycle : Fin r → A) :
    P0ProperWords.prefixWord (P0PeriodicInspectionDecision.lasso w hr cycle) w.length = w := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < w.length
  · simp [P0ProperWords.prefixWord,P0PeriodicInspectionDecision.lasso,hk,List.getElem?_eq_getElem]
  · simp [P0ProperWords.prefixWord,hk,List.getElem?_eq_none (by omega : w.length ≤ k)]

def permanentLanguage (M : Machine Q A H) (hr : 0 < r) (cycle : Fin r → A) : Language A :=
  {w | Permanent M (P0PeriodicInspectionDecision.lasso w hr cycle) w.length}

theorem recognizes [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A) :
    (automaton M birthDecision hr cycle).accepts = permanentLanguage M hr cycle := by
  ext w
  have h := accepts_prefix_iff M birthDecision hr cycle
    (P0PeriodicInspectionDecision.lasso w hr cycle) w.length
    (P0PeriodicInspectionDecision.lasso_periodic w hr cycle)
  rwa [prefix_lasso] at h

theorem regular [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A) :
    (permanentLanguage M hr cycle).IsRegular :=
  Language.isRegular_iff.mpr ⟨State Q r,inferInstance,automaton M birthDecision hr cycle,
    recognizes M birthDecision hr cycle⟩

def inspect [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A) (w : List A) : Bool :=
  accepts hr ((automaton M birthDecision hr cycle).eval w)

theorem inspect_correct [Fintype Q] [DecidableEq Q] [DecidableEq A] (M : Machine Q A H)
    (birthDecision : DecidableRel M.birth) (hr : 0 < r) (cycle : Fin r → A) (w : List A) :
    inspect M birthDecision hr cycle w = true ↔
      Permanent M (P0PeriodicInspectionDecision.lasso w hr cycle) w.length := by
  change w ∈ (automaton M birthDecision hr cycle).accepts ↔ _
  rw [recognizes]
  rfl

end NSSE.P0PeriodicMonitor
