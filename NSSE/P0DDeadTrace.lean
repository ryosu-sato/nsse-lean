import NSSE.P0DDeadReader

/-! Prefix facts for actual complete sink-reader words. A terminal occurs
only at the final position, and equal states reading equal bounded factors
have equal endpoint states. These facts justify the D-dead colour argument. -/
namespace NSSE.P0DDeadTrace
open P0DDeadReader P0ProperWords
variable {Q A H : Type*}

theorem path_split (J : Reader Q A H) (w : List A) (k : Nat) :
    pathFrom J J.initial w = (w.drop k).foldl (move J) (trace J w k) := by
  unfold trace pathFrom
  rw [← List.foldl_append,List.take_append_drop]

theorem trace_ne_failure (J : Reader Q A H) (w : List A) (hc : Complete J w) (k : Nat) :
    trace J w k ≠ none := by
  intro h
  have he := path_split J w k
  rw [h,fold_failure] at he
  rw [hc] at he
  cases he

theorem terminal_iff (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (k : Nat) (hk : k ≤ w.length) : trace J w k = some none ↔ k = w.length := by
  constructor
  · intro h
    have he := path_split J w k
    rw [h,hc] at he
    have hn := (fold_terminal J (w.drop k)).mp he.symm
    have hlen := congrArg List.length hn
    simp only [List.length_drop,List.length_nil] at hlen
    omega
  · intro he
    subst k
    exact complete_trace J w hc

theorem trace_proper (J : Reader Q A H) (w : List A) (hc : Complete J w)
    (k : Nat) (hk : k < w.length) : ∃ q, trace J w k = some (some q) := by
  cases he : trace J w k with
  | none => exact False.elim (trace_ne_failure J w hc k he)
  | some q =>
    cases q with
    | none => have := (terminal_iff J w hc k (by omega)).mp he; omega
    | some q => exact ⟨q,rfl⟩

theorem trace_equal (J : Reader Q A H) (w : List A) (a b l : Nat)
    (ha : a+l ≤ w.length) (hb : b+l ≤ w.length)
    (hs : trace J w a = trace J w b) (hm : WordMatch w a b l) :
    trace J w (a+l) = trace J w (b+l) := by
  induction l with
  | zero => simpa using hs
  | succ l ih =>
    have hal : a+l < w.length := by omega
    have hbl : b+l < w.length := by omega
    have he : w[a+l] = w[b+l] := by
      simpa only [List.getElem?_eq_getElem hal,List.getElem?_eq_getElem hbl,Option.some.injEq]
        using hm l (by omega)
    rw [Nat.add_succ,Nat.add_succ,trace_succ J w (a+l) hal,trace_succ J w (b+l) hbl,
      ih (by omega) (by omega) (fun k hk => hm k (by omega)),he]

end NSSE.P0DDeadTrace
