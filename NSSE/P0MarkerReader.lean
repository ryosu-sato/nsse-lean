import NSSE.P0DDeadReader
import NSSE.P0RegularProduct

/-! A real partial-transition fresh-marker reader. Old-letter steps check
the current proper guard; the marker checks the last guard and the supplied
final predicate, then enters the unique terminal. -/
namespace NSSE.P0MarkerReader
open P0ProperMachine P0ProperWords P0MarkerComparison P0DDeadReader
variable {Q A H : Type*}

def compile [DecidableEq Q] (M : Machine Q A H) (validDecision : DecidablePred M.valid)
    (final : Q → Prop) (finalDecision : DecidablePred final) : Reader Q (Option A) (H ⊕ Bool) := by
  letI := validDecision
  letI := finalDecision
  exact {
    initial := M.initial
    step := fun q a => if M.valid q then
      match a with
      | some b => some (some (M.step q b))
      | none => if final q then some none else none
      else none
    head := fun q => Sum.inl (M.head q)
    endX := Sum.inr false
    endY := Sum.inr true
    birth := fun q t => match q,t with
      | some q,some t => M.birth q t ∧ q ≠ t
      | _,_ => False }

def Ready (M : Machine Q A H) (final : Q → Prop) : Q → List A → Prop
  | q, [] => M.valid q ∧ final q
  | q, a::w => M.valid q ∧ Ready M final (M.step q a) w

theorem path_marker [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final)
    (q : Q) (w : List A) :
    pathFrom (compile M vd final fd) q (marked w) = some none ↔ Ready M final q w := by
  induction w generalizing q with
  | nil =>
    change (if M.valid q then (if final q then some none else none) else none) = some none ↔ _
    by_cases hv : M.valid q <;> by_cases hf : final q <;> simp [hv,hf,Ready]
  | cons a w ih =>
    change (marked w).foldl (move (compile M vd final fd))
      (if M.valid q then some (some (M.step q a)) else none) = some none ↔ _
    by_cases hv : M.valid q
    · rw [if_pos hv]
      exact (ih (M.step q a)).trans (by simp only [Ready,hv,true_and])
    · rw [if_neg hv,fold_failure]
      simp [Ready,hv]

theorem complete_shape [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final)
    (q : Q) (v : List (Option A))
    (h : pathFrom (compile M vd final fd) q v = some none) :
    ∃ w : List A, v = marked w := by
  induction v generalizing q with
  | nil => cases h
  | cons a v ih =>
    by_cases hv : M.valid q
    · cases a with
      | none =>
        by_cases hf : final q
        · change v.foldl (move (compile M vd final fd))
            (if M.valid q then (if final q then some none else none) else none) = some none at h
          rw [if_pos hv,if_pos hf] at h
          have he := (fold_terminal (compile M vd final fd) v).mp h
          subst v
          exact ⟨[],rfl⟩
        · change v.foldl (move (compile M vd final fd))
            (if M.valid q then (if final q then some none else none) else none) = some none at h
          rw [if_pos hv,if_neg hf,fold_failure] at h
          cases h
      | some a =>
        change v.foldl (move (compile M vd final fd))
          (if M.valid q then some (some (M.step q a)) else none) = some none at h
        rw [if_pos hv] at h
        obtain ⟨w,hw⟩ := ih (M.step q a) h
        exact ⟨a::w,by simp only [marked,List.map_cons,List.cons_append,hw]⟩
    · change v.foldl (move (compile M vd final fd))
        (if M.valid q then _ else none) = some none at h
      rw [if_neg hv,fold_failure] at h
      cases h

theorem ready_iff (M : Machine Q A H) (final : Q → Prop) (q : Q) (w : List A) :
    Ready M final q w ↔
      (∀ k, k ≤ w.length → M.valid ((w.take k).foldl M.step q)) ∧ final (w.foldl M.step q) := by
  induction w generalizing q with
  | nil => simp [Ready]
  | cons a w ih =>
    rw [Ready,ih]
    constructor
    · rintro ⟨hv,hall,hfinal⟩
      refine ⟨?_,hfinal⟩
      intro k hk
      cases k with
      | zero => exact hv
      | succ k => exact hall k (by simpa using hk)
    · rintro ⟨hall,hfinal⟩
      refine ⟨hall 0 (by omega),?_,hfinal⟩
      intro k hk
      exact hall (k+1) (by simpa using hk)

theorem complete_marker_iff [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final) (w : List A) :
    Complete (compile M vd final fd) (marked w) ↔
      (∀ k, k ≤ w.length → M.valid (state M w k)) ∧ final (state M w w.length) := by
  rw [Complete,path_marker,ready_iff]
  simp only [state,List.take_length,compile]

theorem trace_old [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final) (w : List A)
    (hv : ∀ k, k ≤ w.length → M.valid (state M w k)) (k : Nat) (hk : k ≤ w.length) :
    trace (compile M vd final fd) (marked w) k = some (some (state M w k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkw : k < w.length := by omega
    have hkm : k < (marked w).length := by simp only [marked_length]; omega
    have hletter : (marked w)[k] = some w[k] := by
      have he := marked_get_old w k hkw
      rwa [List.getElem?_eq_getElem hkm,Option.some.injEq] at he
    rw [trace_succ _ _ k hkm,ih (by omega),hletter]
    change (if M.valid (state M w k) then some (some (M.step (state M w k) w[k])) else none) = _
    rw [if_pos (hv k (by omega)),P0ProperWordLemmas.state_step M w k hkw]

theorem trace_marker [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final) (w : List A)
    (hc : Complete (compile M vd final fd) (marked w)) (k : Nat) (hk : k ≤ (marked w).length) :
    trace (compile M vd final fd) (marked w) k =
      if k ≤ w.length then some (some (state M w k)) else some none := by
  by_cases hko : k ≤ w.length
  · rw [if_pos hko]
    exact trace_old M vd final fd w ((complete_marker_iff M vd final fd w).mp hc).1 k hko
  · have he : k = (marked w).length := by rw [marked_length] at hk ⊢; omega
    rw [if_neg hko,he]
    exact complete_trace _ _ hc

theorem left_marker [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final) (w : List A)
    (hc : Complete (compile M vd final fd) (marked w)) (k : Nat) (hk : k ≤ (marked w).length) :
    leftAt (compile M vd final fd) (marked w) k = endpoint M w false k := by
  unfold leftAt
  rw [trace_marker M vd final fd w hc k hk]
  by_cases he : k ≤ w.length <;> simp [he,compile,endpoint]

theorem right_marker [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final) (w : List A)
    (hc : Complete (compile M vd final fd) (marked w)) (k : Nat) (hk : k ≤ (marked w).length) :
    rightAt (compile M vd final fd) (marked w) k = endpoint M w true k := by
  unfold rightAt
  rw [trace_marker M vd final fd w hc k hk]
  by_cases he : k ≤ w.length <;> simp [he,compile,endpoint]

theorem born_marker [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final) (w : List A)
    (hc : Complete (compile M vd final fd) (marked w)) (a b : Nat)
    (ha : a ≤ (marked w).length) (hb : b ≤ (marked w).length) :
    bornAt (compile M vd final fd) (marked w) a b ↔ born M w a b := by
  unfold bornAt
  rw [trace_marker M vd final fd w hc a ha,trace_marker M vd final fd w hc b hb]
  by_cases hao : a ≤ w.length <;> by_cases hbo : b ≤ w.length <;>
    simp [hao,hbo,compile,born]

theorem safe_marker_iff [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final) (w : List A)
    (hc : Complete (compile M vd final fd) (marked w)) :
    Safe (marked w) (leftAt (compile M vd final fd) (marked w))
      (rightAt (compile M vd final fd) (marked w)) (bornAt (compile M vd final fd) (marked w)) ↔
        MarkedSafe M w := by
  constructor
  · intro hs a ha b hb l hl hal hbl hborn hm
    have he := hs a ha b hb l hl hal hbl ((born_marker M vd final fd w hc a b ha hb).mpr hborn) hm
    rwa [left_marker M vd final fd w hc (a+l) hal,right_marker M vd final fd w hc (b+l) hbl] at he
  · intro hs a ha b hb l hl hal hbl hborn hm
    rw [left_marker M vd final fd w hc (a+l) hal,right_marker M vd final fd w hc (b+l) hbl]
    exact hs a ha b hb l hl hal hbl ((born_marker M vd final fd w hc a b ha hb).mp hborn) hm

theorem accepted_marker_iff [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final) (w : List A) :
    Accepted (compile M vd final fd) (marked w) ↔ GoodWord M w ∧ final (state M w w.length) := by
  constructor
  · rintro ⟨hc,hs⟩
    obtain ⟨hv,hfinal⟩ := (complete_marker_iff M vd final fd w).mp hc
    exact ⟨good_of_markedSafe M w hv ((safe_marker_iff M vd final fd w hc).mp hs),hfinal⟩
  · rintro ⟨hg,hfinal⟩
    have hc := (complete_marker_iff M vd final fd w).mpr ⟨hg.1,hfinal⟩
    exact ⟨hc,(safe_marker_iff M vd final fd w hc).mpr (markedSafe_of_good M w hg)⟩

theorem accepted_iff [DecidableEq Q] (M : Machine Q A H)
    (vd : DecidablePred M.valid) (final : Q → Prop) (fd : DecidablePred final) (v : List (Option A)) :
    Accepted (compile M vd final fd) v ↔
      ∃ w, v = marked w ∧ GoodWord M w ∧ final (state M w w.length) := by
  constructor
  · intro h
    obtain ⟨w,rfl⟩ := complete_shape M vd final fd M.initial v h.1
    exact ⟨w,rfl,(accepted_marker_iff M vd final fd w).mp h⟩
  · rintro ⟨w,rfl,h⟩
    exact (accepted_marker_iff M vd final fd w).mpr h

end NSSE.P0MarkerReader
