import NSSE
import Lean.Elab.Tactic.Omega

/-!
# Commuting finite words have a common root

Free-monoid theorem used by insertion-square holonomy.
-/

namespace NSSE

universe u

namespace Word

def power (z : Word α) : Nat → Word α
  | 0 => []
  | n + 1 => z ++ power z n

@[simp] theorem power_zero (z : Word α) : power z 0 = [] := rfl

@[simp] theorem power_succ (z : Word α) (n : Nat) :
    power z (n + 1) = z ++ power z n := rfl

theorem power_add (z : Word α) (m n : Nat) :
    power z (m + n) = power z m ++ power z n := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Nat.succ_add, power_succ, ih, List.append_assoc]

theorem power_length (z : Word α) (n : Nat) :
    (power z n).length = n * z.length := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [power_succ, List.length_append, ih, Nat.succ_mul]
      omega

theorem power_power (z : Word α) (m n : Nat) :
    power (power z m) n = power z (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [power_succ, ih]
      calc
        power z m ++ power z (m * n) =
            power z (m + m * n) := (power_add z m (m * n)).symm
        _ = power z (m * (n + 1)) := by
          congr 1
          rw [Nat.mul_succ, Nat.add_comm]

@[simp] theorem power_nil (n : Nat) :
    power ([] : Word α) n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [power_succ, ih]

theorem take_length_append (x y : Word α) :
    (x ++ y).take x.length = x := by
  simp

theorem eq_take_of_commute_of_length_le
    {x y : Word α} (hxy : x ++ y = y ++ x)
    (hlen : x.length ≤ y.length) :
    x = y.take x.length := by
  calc
    x = (x ++ y).take x.length := by simp
    _ = (y ++ x).take x.length := congrArg (List.take x.length) hxy
    _ = y.take x.length := List.take_append_of_le_length hlen

theorem split_right_of_commute_of_length_le
    {x y : Word α} (hxy : x ++ y = y ++ x)
    (hlen : x.length ≤ y.length) :
    ∃ tail, y = x ++ tail := by
  refine ⟨y.drop x.length, ?_⟩
  calc
    y = y.take x.length ++ y.drop x.length :=
      (List.take_append_drop x.length y).symm
    _ = x ++ y.drop x.length := by
      exact congrArg (fun p => p ++ y.drop x.length)
        (eq_take_of_commute_of_length_le hxy hlen).symm

/--
Lyndon--Schützenberger commutation theorem for finite lists, in the form
needed by the SOA proof.  The common word need not be primitive; choosing
its primitive root is a subsequent finite minimization.
-/
theorem commute_iff_common_power (x y : Word α) :
    x ++ y = y ++ x ↔
      ∃ z m n, x = power z m ∧ y = power z n := by
  constructor
  · intro hcomm
    have main :
        ∀ total, ∀ x y : Word α,
          x.length + y.length = total →
          x ++ y = y ++ x →
          ∃ z m n, x = power z m ∧ y = power z n := by
      intro total
      induction total using Nat.strongRecOn with
      | ind total ih =>
          intro x y htotal hxy
          by_cases hx : x = []
          · subst x
            exact ⟨y, 0, 1, rfl, by simp⟩
          by_cases hy : y = []
          · subst y
            exact ⟨x, 1, 0, by simp, rfl⟩
          by_cases hlen : x.length ≤ y.length
          · obtain ⟨tail, rfl⟩ :=
              split_right_of_commute_of_length_le hxy hlen
            have hcancel : x ++ tail = tail ++ x := by
              apply List.append_cancel_left (as := x)
              simpa [List.append_assoc] using hxy
            have hxtail : x.length + tail.length < total := by
              have hxpos : 0 < x.length := List.length_pos_iff.mpr hx
              simp only [List.length_append] at htotal
              omega
            obtain ⟨z, m, n, hxm, htn⟩ :=
              ih (x.length + tail.length) hxtail x tail rfl hcancel
            refine ⟨z, m, m + n, hxm, ?_⟩
            rw [hxm, htn, power_add]
          · have hyx : y ++ x = x ++ y := hxy.symm
            have hylen : y.length ≤ x.length := by omega
            obtain ⟨tail, rfl⟩ :=
              split_right_of_commute_of_length_le hyx hylen
            have hcancel : y ++ tail = tail ++ y := by
              apply List.append_cancel_left (as := y)
              simpa [List.append_assoc] using hyx
            have hytail : y.length + tail.length < total := by
              have hypos : 0 < y.length := List.length_pos_iff.mpr hy
              simp only [List.length_append] at htotal
              omega
            obtain ⟨z, m, n, hym, htn⟩ :=
              ih (y.length + tail.length) hytail y tail rfl hcancel
            refine ⟨z, m + n, m, ?_, hym⟩
            rw [hym, htn, power_add]
    exact main (x.length + y.length) x y rfl hcomm
  · rintro ⟨z, m, n, rfl, rfl⟩
    rw [← power_add, Nat.add_comm, power_add]

def IsPrimitive (z : Word α) : Prop :=
  ¬ ∃ root k, 1 < k ∧ z = power root k

/-- Every nonempty finite word is a positive power of a primitive word. -/
theorem exists_primitive_root
    (z : Word α) (hz : z ≠ []) :
    ∃ root k, 0 < k ∧ root.IsPrimitive ∧ z = power root k := by
  classical
  have main :
      ∀ n, ∀ z : Word α, z.length = n → z ≠ [] →
        ∃ root k, 0 < k ∧ root.IsPrimitive ∧ z = power root k := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro z hlen hz
        by_cases hprim : z.IsPrimitive
        · exact ⟨z, 1, by omega, hprim, by simp⟩
        · unfold IsPrimitive at hprim
          rw [Classical.not_not] at hprim
          obtain ⟨r, k, hk, hpow⟩ := hprim
          have hr : r ≠ [] := by
            intro hrnil
            subst r
            exact hz (hpow.trans (power_nil k))
          have hrlen : r.length < n := by
            have hpowerlen := congrArg List.length hpow
            rw [power_length] at hpowerlen
            have hrpos : 0 < r.length := List.length_pos_iff.mpr hr
            have hlt := Nat.mul_lt_mul_of_pos_right hk hrpos
            simp only [Nat.one_mul] at hlt
            omega
          obtain ⟨q, m, hm, hqprim, hrpow⟩ :=
            ih r.length hrlen r rfl hr
          refine ⟨q, m * k, Nat.mul_pos hm (by omega), hqprim, ?_⟩
          rw [hpow, hrpow, power_power]
  exact main z.length z rfl hz

/-- Commuting nonempty words are powers of one primitive root. -/
theorem commute_iff_common_primitive_power
    (x y : Word α) (hx : x ≠ []) :
    x ++ y = y ++ x ↔
      ∃ z m n,
        z.IsPrimitive ∧ 0 < m ∧
        x = power z m ∧ y = power z n := by
  constructor
  · intro hcomm
    obtain ⟨r, a, b, hxa, hyb⟩ :=
      (commute_iff_common_power x y).1 hcomm
    have hr : r ≠ [] := by
      intro hrnil
      subst r
      exact hx (hxa.trans (power_nil a))
    obtain ⟨z, k, hk, hzprim, hrk⟩ := exists_primitive_root r hr
    have hane : a ≠ 0 := by
      intro ha0
      subst a
      exact hx hxa
    have ha : 0 < a := Nat.pos_of_ne_zero hane
    refine ⟨z, k * a, k * b, hzprim, Nat.mul_pos hk ha, ?_, ?_⟩
    · rw [hxa, hrk, power_power]
    · rw [hyb, hrk, power_power]
  · rintro ⟨z, m, n, _, _, hxm, hyn⟩
    exact (commute_iff_common_power _ _).2 ⟨z, m, n, hxm, hyn⟩

end Word

end NSSE
