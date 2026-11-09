import NSSE.P0LoopStreams
import NSSE.P0BoundedWords

/-! Finite nested repetitions with a computable length recurrence.
Depth zero is a nonempty factor; every next level repeats the preceding
factor with a nonempty gap. The alphabet may be empty. -/
namespace NSSE.P0NestedRepeats
open P0ProperMachine P0ProperWords P0LoopStreams
variable {A : Type*}

def Nest (z : Nat → A) (a L : Nat) : Nat → Prop
  | 0 => 0 < L
  | k+1 => ∃ l d, l < d ∧ L = d+l ∧ Nest z a l k ∧ Match z a (a+d) l

theorem nest_positive (z : Nat → A) (a L k : Nat) (h : Nest z a L k) : 0 < L := by
  cases k with
  | zero => exact h
  | succ k => obtain ⟨l,d,hd,rfl,_,_⟩ := h; omega

theorem nest_map {B : Type*} (f : A → B) (z : Nat → A) (a L k : Nat)
    (h : Nest z a L k) : Nest (fun i => f (z i)) a L k := by
  induction k generalizing L with
  | zero => exact h
  | succ k ih =>
    obtain ⟨l,d,hd,rfl,hn,hm⟩ := h
    exact ⟨l,d,hd,rfl,ih l hn,fun i hi => congrArg f (hm i hi)⟩

theorem segment_match (z : Nat → A) (a b L : Nat)
    (he : segment z a L = segment z b L) : Match z a b L := by
  intro k hk
  have ha := segment_spells z a L k (by simpa using hk)
  have hb := segment_spells z b L k (by simpa using hk)
  rw [he,hb] at ha
  exact (Option.some.inj ha).symm

theorem segment_letters (z : Nat → A) (alphabet : Finset A)
    (hz : ∀ k, z k ∈ alphabet) (a L : Nat) :
    ∀ x ∈ segment z a L, x ∈ alphabet := by
  intro x hx
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hx
  exact hz (a+k.val)

variable [DecidableEq A]

def bound (alphabet : Finset A) : Nat → Nat
  | 0 => 1
  | k+1 => ((P0BoundedWords.words alphabet (bound alphabet k)).card+1) * (bound alphabet k+1)

theorem bound_positive (alphabet : Finset A) (k : Nat) : 0 < bound alphabet k := by
  cases k with
  | zero => exact Nat.zero_lt_one
  | succ k => exact Nat.mul_pos (by omega) (by omega)

theorem bound_step (alphabet : Finset A) (k : Nat) : bound alphabet k < bound alphabet (k+1) := by
  have h := Nat.le_mul_of_pos_left (bound alphabet k+1)
    (show 0 < (P0BoundedWords.words alphabet (bound alphabet k)).card+1 by omega)
  change bound alphabet k < ((P0BoundedWords.words alphabet (bound alphabet k)).card+1) * _
  omega

end NSSE.P0NestedRepeats
