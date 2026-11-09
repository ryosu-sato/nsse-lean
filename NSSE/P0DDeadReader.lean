import NSSE.P0MarkerComparison

/-! Concrete deterministic readers with one terminal sink and failed
transitions. `none` inside a successful transition is the terminal;
an outer `none` is failure. A terminal has no outgoing transitions. -/
namespace NSSE.P0DDeadReader
open P0MarkerComparison P0ProperWords
variable {Q A H : Type*}

structure Reader (Q A H : Type*) where
  initial : Q
  step : Q → A → Option (Option Q)
  head : Q → H
  endX : H
  endY : H
  birth : Option Q → Option Q → Prop

def move (J : Reader Q A H) : Option (Option Q) → A → Option (Option Q)
  | some (some q), a => J.step q a
  | _, _ => none

def pathFrom (J : Reader Q A H) (q : Q) (w : List A) : Option (Option Q) :=
  w.foldl (move J) (some (some q))

def trace (J : Reader Q A H) (w : List A) (k : Nat) : Option (Option Q) :=
  pathFrom J J.initial (w.take k)

def Complete (J : Reader Q A H) (w : List A) : Prop :=
  pathFrom J J.initial w = some none

def leftAt (J : Reader Q A H) (w : List A) (k : Nat) : H :=
  match trace J w k with
  | some (some q) => J.head q
  | _ => J.endX

def rightAt (J : Reader Q A H) (w : List A) (k : Nat) : H :=
  match trace J w k with
  | some (some q) => J.head q
  | _ => J.endY

def bornAt (J : Reader Q A H) (w : List A) (a b : Nat) : Prop :=
  ∃ q t, trace J w a = some q ∧ trace J w b = some t ∧ J.birth q t

def Accepted (J : Reader Q A H) (w : List A) : Prop :=
  Complete J w ∧ Safe w (leftAt J w) (rightAt J w) (bornAt J w)

theorem fold_failure (J : Reader Q A H) (w : List A) : w.foldl (move J) none = none := by
  induction w with
  | nil => rfl
  | cons a w ih => exact ih

theorem fold_terminal (J : Reader Q A H) (w : List A) :
    w.foldl (move J) (some none) = some none ↔ w = [] := by
  cases w with
  | nil => simp
  | cons a w => simp only [List.foldl_cons,move,fold_failure,reduceCtorEq]

@[simp] theorem trace_zero (J : Reader Q A H) (w : List A) :
    trace J w 0 = some (some J.initial) := rfl

theorem trace_succ (J : Reader Q A H) (w : List A) (k : Nat) (hk : k < w.length) :
    trace J w (k+1) = move J (trace J w k) w[k] := by
  simp only [trace,pathFrom,List.take_succ_eq_append_getElem hk,List.foldl_append,
    List.foldl_cons,List.foldl_nil]

theorem complete_trace (J : Reader Q A H) (w : List A) (h : Complete J w) :
    trace J w w.length = some none := by
  simpa only [trace,List.take_length] using h

end NSSE.P0DDeadReader
