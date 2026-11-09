import NSSE.MultiVarianceBranchAssignment

/-! The actual current-head decoration of a signed branch word. The
decoration has exactly the input length and exactly the selected raw
token evolution on every locally complete branch. -/
namespace NSSE.MultiVarianceBranchLetters
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceBranch
open MultiVarianceBranchLocal
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def ArityRun (C : Parameters arity n) (s : State n) : List (Fin D) → Prop
  | [] => True
  | a::w => a.val < arity (output C s) ∧ ArityRun C (successor pol C s a.val) w

theorem local_arities (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (hl : LocalRun pol C s w) : ArityRun pol C s w := by
  induction w generalizing s with
  | nil => trivial
  | cons a w ih =>
    cases w with
    | nil => exact ⟨hl.1.2,trivial⟩
    | cons b w => exact ⟨hl.1.2,ih _ hl.2⟩

def letters (C : Parameters arity n) (s : State n) : List (Fin D) → List (Letter arity)
  | [] => []
  | a::w => if hi : a.val < arity (output C s) then
      ⟨output C s,⟨a.val,hi⟩⟩ :: letters C (successor pol C s a.val) w else []

theorem letters_length (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (ha : ArityRun pol C s w) : (letters pol C s w).length=w.length := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simp only [letters,dif_pos ha.1,List.length_cons,ih _ ha.2]

theorem letters_indices (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (ha : ArityRun pol C s w) :
    (letters pol C s w).map (fun a => a.2.val)=w.map Fin.val := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => simp only [letters,dif_pos ha.1,List.map_cons,ih _ ha.2]

theorem arities_take (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (ha : ArityRun pol C s w) (k : Nat) : ArityRun pol C s (w.take k) := by
  induction w generalizing s k with
  | nil => simp only [List.take_nil,ArityRun]
  | cons a w ih =>
    cases k with
    | zero => trivial
    | succ k => exact ⟨ha.1,ih _ ha.2 k⟩

theorem letters_take (C : Parameters arity n) (s : State n) (w : List (Fin D)) (k : Nat) :
    letters pol C s (w.take k) = (letters pol C s w).take k := by
  induction w generalizing s k with
  | nil => simp [letters]
  | cons a w ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.take_succ_cons,letters]
      split
      · simp only [List.take_succ_cons,ih]
      · simp only [List.take_nil]

theorem letters_run (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (ha : ArityRun pol C s w) :
    runPhysical pol C.query.constraints s.1 (letters pol C s w)=(walk pol C s w).1 := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    rw [letters,dif_pos ha.1]
    change runPhysical pol C.query.constraints
      (physicalMove pol C.query.constraints s.1 (output C s) ⟨a.val,ha.1⟩)
      (letters pol C (successor pol C s a.val) w) = _
    have hs : (successor pol C s a.val).1 =
        physicalMove pol C.query.constraints s.1 (output C s) ⟨a.val,ha.1⟩ :=
      MultiVarianceSelectorStep.step_valid pol C.query.constraints s.1 (output C s) ⟨a.val,ha.1⟩
    rw [← hs,ih _ ha.2]
    rfl

theorem letters_prefix_run (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (ha : ArityRun pol C s w) (k : Nat) :
    runPhysical pol C.query.constraints s.1 ((letters pol C s w).take k)=
      (walk pol C s (w.take k)).1 := by
  rw [← letters_take]
  exact letters_run pol C s (w.take k) (arities_take pol C s w ha k)

theorem letters_current_head (C : Parameters arity n) (s : State n) (w : List (Fin D))
    (ha : ArityRun pol C s w) (k : Nat) (hk : k<w.length) :
    ((letters pol C s w)[k]?).map Sigma.fst =
      some (output C (walk pol C s (w.take k))) := by
  induction w generalizing s k with
  | nil => simp at hk
  | cons a w ih =>
    rw [letters,dif_pos ha.1]
    cases k with
    | zero => rfl
    | succ k => exact ih _ ha.2 k (by simpa using hk)

end NSSE.MultiVarianceBranchLetters
