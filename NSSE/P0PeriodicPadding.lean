import NSSE.P0PeriodicSuffixGood
import Mathlib.Data.Nat.Periodic

/-! An eventual literal period supplies a full inspection suffix without
changing the stream. The padded prefix extends strictly beyond the cut. -/
namespace NSSE.P0PeriodicPadding
open P0ProperWords P0PeriodicBlocks P0PeriodicInspectionDecision P0PeriodicSuffixGood
variable {A : Type*} {r : Nat}

def cycle (z : Nat → A) (a : Nat) (r : Nat) : Fin r → A := fun i => z (a+i.val)

theorem prefix_lasso (z : Nat → A) (a : Nat) (hr : 0 < r)
    (hp : Function.Periodic (fun k => z (a+k)) r) :
    lasso (prefixWord z a) hr (cycle z a r) = z := by
  funext k
  by_cases hk : k < (prefixWord z a).length
  · have he := spells_prefix z a k hk
    rw [List.getElem?_eq_getElem hk] at he
    rw [lasso,dif_pos hk]
    exact Option.some.inj he
  · have hak : a ≤ k := by simpa only [prefix_length] using Nat.le_of_not_gt hk
    rw [lasso,dif_neg hk,prefix_length]
    change z (a+(k-a)%r) = z k
    simpa only [Nat.add_sub_of_le hak] using hp.map_mod_nat (k-a)

def padded (Q : Type*) [Fintype Q] (z : Nat → A) (a : Nat) (hr : 0 < r) : List A :=
  prefixWord z a ++ pattern Q hr (cycle z a r)

theorem padded_suffix (Q : Type*) [Fintype Q] (z : Nat → A) (a : Nat) (hr : 0 < r) :
    (pattern Q hr (cycle z a r)).IsSuffix (padded Q z a hr) :=
  ⟨prefixWord z a,rfl⟩

theorem padded_lasso (Q : Type*) [Fintype Q] (z : Nat → A) (a : Nat) (hr : 0 < r)
    (hp : Function.Periodic (fun k => z (a+k)) r) :
    lasso (padded Q z a hr) hr (cycle z a r) = z := by
  unfold padded pattern
  rw [lasso_append,prefix_lasso z a hr hp]

theorem padded_spells (Q : Type*) [Fintype Q] (z : Nat → A) (a : Nat) (hr : 0 < r)
    (hp : Function.Periodic (fun k => z (a+k)) r) : Spells z (padded Q z a hr) := by
  have h := lasso_spells (padded Q z a hr) hr (cycle z a r)
  rwa [padded_lasso Q z a hr hp] at h

theorem padded_longer (Q : Type*) [Fintype Q] (z : Nat → A) (a : Nat) (hr : 0 < r) :
    a < (padded Q z a hr).length := by
  have hc : 0 < copies (Fintype.card Q) := by unfold copies; omega
  have hm := Nat.mul_pos hc hr
  simp only [padded,List.length_append,prefix_length,pattern,block_length]
  omega

end NSSE.P0PeriodicPadding
