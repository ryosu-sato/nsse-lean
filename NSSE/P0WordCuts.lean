import NSSE.P0DDeadReader
import Init.Data.List.Nat.Pairwise

/-! Actual deletion words from strictly increasing retained-position maps.
The terminal is retained. The source of a seam is the successor of the
previous retained position (zero at the initial cut). Thus cuts remove
literal intervals and the state-loop conditions are finite equalities. -/
namespace NSSE.P0WordCuts
open P0DDeadReader
variable {Q A H : Type*}

structure Cut (w : List A) (n : Nat) where
  lift : Nat → Nat
  increasing : ∀ a b, a < b → b ≤ n → lift a < lift b
  terminal : lift n = w.length

namespace Cut
variable {w : List A} {n : Nat}

theorem lift_lt (C : Cut w n) (k : Nat) (hk : k < n) : C.lift k < w.length := by
  rw [← C.terminal]
  exact C.increasing k n hk (by omega)

theorem lift_le (C : Cut w n) (k : Nat) (hk : k ≤ n) : C.lift k ≤ w.length := by
  by_cases he : k = n
  · rw [he,C.terminal]
  · exact Nat.le_of_lt (C.lift_lt k (by omega))

theorem lift_injective (C : Cut w n) (a b : Nat) (ha : a ≤ n) (hb : b ≤ n)
    (he : C.lift a = C.lift b) : a = b := by
  by_contra h
  rcases lt_or_gt_of_ne h with hab | hba
  · have := C.increasing a b hab hb
    omega
  · have := C.increasing b a hba ha
    omega

def source (C : Cut w n) : Nat → Nat
  | 0 => 0
  | k+1 => C.lift k+1

theorem source_le (C : Cut w n) (k : Nat) (hk : k ≤ n) : C.source k ≤ w.length := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k => have := C.lift_lt k (by omega); exact Nat.succ_le_of_lt this

def word (C : Cut w n) : List A :=
  List.ofFn (fun k : Fin n => w[C.lift k.val]'(C.lift_lt k.val k.isLt))

@[simp] theorem word_length (C : Cut w n) : C.word.length = n := by simp [word]

theorem word_get (C : Cut w n) (k : Nat) (hk : k < n) :
    C.word[k]'(by simpa using hk) = w[C.lift k]'(C.lift_lt k hk) := by
  simp [word]

theorem word_getElem? (C : Cut w n) (k : Nat) (hk : k < n) :
    C.word[k]? = w[C.lift k]? := by
  rw [List.getElem?_eq_getElem (by simpa using hk),List.getElem?_eq_getElem (C.lift_lt k hk),C.word_get k hk]

theorem word_sublist (C : Cut w n) : C.word.Sublist w := by
  let indices : List (Fin w.length) := List.ofFn (fun k : Fin n => ⟨C.lift k,C.lift_lt k k.isLt⟩)
  have hp : indices.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hjn : j < n := by simpa [indices] using hj
    simpa [indices] using C.increasing i j hij (by omega)
  have hs := List.map_getElem_sublist hp
  simpa [indices,word,List.map_ofFn] using hs

theorem length_le (C : Cut w n) : n ≤ w.length := by
  simpa using C.word_sublist.length_le

def Loops (C : Cut w n) (J : Reader Q A H) : Prop :=
  ∀ k, k ≤ n → trace J w (C.source k) = trace J w (C.lift k)

theorem trace_word (C : Cut w n) (J : Reader Q A H) (hloop : C.Loops J)
    (k : Nat) (hk : k ≤ n) : trace J C.word k = trace J w (C.lift k) := by
  induction k with
  | zero => exact hloop 0 (by omega)
  | succ k ih =>
    have hkn : k < n := by omega
    rw [trace_succ J C.word k (by simpa using hkn),ih (by omega),C.word_get k hkn,
      ← trace_succ J w (C.lift k) (C.lift_lt k hkn)]
    exact hloop (k+1) hk

theorem complete_word (C : Cut w n) (J : Reader Q A H) (hloop : C.Loops J)
    (hc : Complete J w) : Complete J C.word := by
  have he := C.trace_word J hloop n (by omega)
  rw [C.terminal,complete_trace J w hc] at he
  change pathFrom J J.initial (C.word.take n) = some none at he
  rw [show C.word.take n = C.word by simpa only [C.word_length] using (@List.take_length A C.word)] at he
  exact he

theorem left_word (C : Cut w n) (J : Reader Q A H) (hloop : C.Loops J)
    (k : Nat) (hk : k ≤ n) : leftAt J C.word k = leftAt J w (C.lift k) := by
  unfold leftAt
  rw [C.trace_word J hloop k hk]

theorem right_word (C : Cut w n) (J : Reader Q A H) (hloop : C.Loops J)
    (k : Nat) (hk : k ≤ n) : rightAt J C.word k = rightAt J w (C.lift k) := by
  unfold rightAt
  rw [C.trace_word J hloop k hk]

theorem born_word (C : Cut w n) (J : Reader Q A H) (hloop : C.Loops J)
    (a b : Nat) (ha : a ≤ n) (hb : b ≤ n) :
    bornAt J C.word a b ↔ bornAt J w (C.lift a) (C.lift b) := by
  unfold bornAt
  rw [C.trace_word J hloop a ha,C.trace_word J hloop b hb]

end Cut
end NSSE.P0WordCuts
