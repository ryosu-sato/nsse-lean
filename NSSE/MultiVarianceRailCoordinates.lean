import NSSE.MultiVarianceRaySupport

/-! Original-variable aliases affect only level zero. Fresh rail levels
and roles are unique, and shared fill variables are never rail positions. -/
namespace NSSE.MultiVarianceRailCoordinates
open MultiConstructorConstraints (Query)
open MultiVarianceEncoding MultiVarianceGlobal MultiVarianceOriginalSpine
open MultiVarianceSpineSeparation MultiVarianceSpineRows MultiVarianceSpineTokens
open MultiVarianceTokenExact MultiVarianceRailBirths MultiVariancePositionLiterals
open MultiVariancePhysicalTrace MultiVarianceRaySupport
variable {H : Type*} {arity : H → Nat} {n : Nat}

theorem roleVariable_zero (Q : Query arity n) (s : Spine arity) (r : Bool) :
    roleVariable Q s 0 (Nat.zero_le _) r = old s.depth (if r then Q.right else Q.left) := by
  cases r <;> rfl

theorem roleVariable_pos_val (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (r : Bool) (hp : 0 < d) :
    (roleVariable Q s d hd r).val = n+(2*d+parity r-2) := by
  have h0 : 2*d+parity r ≠ 0 := by omega
  have h1 : 2*d+parity r ≠ 1 := by omega
  simp only [roleVariable,railSlot,slot,Fin.val_mk,h0,h1,if_false]

theorem roleVariable_level (Q : Query arity n) (s : Spine arity)
    (d e : Nat) (hd : d ≤ s.depth) (he : e ≤ s.depth) (r t : Bool)
    (hv : roleVariable Q s d hd r = roleVariable Q s e he t) : d = e := by
  have hp : parity r ≤ 1 := by cases r <;> decide
  have ht : parity t ≤ 1 := by cases t <;> decide
  have eqv := congrArg Fin.val hv
  by_cases dz : d = 0
  · subst d
    rw [roleVariable_zero] at eqv
    have hy := (if r then Q.right else Q.left).isLt
    by_cases ez : e = 0
    · exact ez.symm
    · rw [roleVariable_pos_val Q s e he t (by omega)] at eqv
      change (if r then Q.right else Q.left).val = _ at eqv
      omega
  · by_cases ez : e = 0
    · subst e
      rw [roleVariable_zero,roleVariable_pos_val Q s d hd r (by omega)] at eqv
      have hx := (if t then Q.right else Q.left).isLt
      change _ = (if t then Q.right else Q.left).val at eqv
      omega
    · rw [roleVariable_pos_val Q s d hd r (by omega),roleVariable_pos_val Q s e he t (by omega)] at eqv
      omega

theorem roleVariable_role (Q : Query arity n) (s : Spine arity)
    (d e : Nat) (hd : d ≤ s.depth) (he : e ≤ s.depth) (r t : Bool) (hp : 0 < d)
    (hv : roleVariable Q s d hd r = roleVariable Q s e he t) : r = t := by
  have hl := roleVariable_level Q s d e hd he r t hv
  subst e
  have eqv := congrArg Fin.val hv
  rw [roleVariable_pos_val Q s d hd r hp,roleVariable_pos_val Q s d hd t hp] at eqv
  cases r <;> cases t <;> simp only [parity,Bool.false_eq_true,if_false,if_true] at eqv ⊢ <;> omega

theorem fill_ne_role (Q : Query arity n) (s : Spine arity) (fill : Bool)
    (d : Nat) (hd : d ≤ s.depth) (r : Bool) :
    slot Q.left Q.right s.depth (if fill then topAt s.depth else bottomAt s.depth) ≠
      roleVariable Q s d hd r := by
  intro hv
  have eqv := congrArg Fin.val hv
  have hp : parity r ≤ 1 := by cases r <;> decide
  have fv : (slot Q.left Q.right s.depth
      (if fill then topAt s.depth else bottomAt s.depth)).val = n+2*s.depth+parity fill := by
    cases fill <;> simp [slot,topAt,bottomAt,parity,Nat.add_assoc]
  rw [fv] at eqv
  by_cases hz : d = 0
  · subst d
    rw [roleVariable_zero] at eqv
    have hx := (if r then Q.right else Q.left).isLt
    change _ = (if r then Q.right else Q.left).val at eqv
    omega
  · rw [roleVariable_pos_val Q s d hd r (by omega)] at eqv
    omega

theorem roleOf_involution (sign r : Bool) : roleOf sign (roleOf sign r) = r := by
  cases sign <;> cases r <;> rfl

variable [DecidableEq H] (pol : Polarity arity)

def rolePosition (Q : Query arity n) (s : Spine arity) (d : Nat) (hd : d ≤ s.depth) (r : Bool) :
    Position s := (⟨d,by omega⟩,roleOf (stateAt pol Q s d).sign r)

@[simp] theorem rolePosition_role (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (r : Bool) :
    roleAt pol Q s (rolePosition pol Q s d hd r) = r := roleOf_involution _ r

@[simp] theorem rolePosition_variable (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (r : Bool) :
    variableAt pol Q s (rolePosition pol Q s d hd r) = roleVariable Q s d hd r := by
  change roleVariable Q s d hd (roleAt pol Q s (rolePosition pol Q s d hd r)) = _
  rw [rolePosition_role]

theorem rolePosition_of_position (Q : Query arity n) (s : Spine arity) (p : Position s) :
    rolePosition pol Q s p.1.val (level_le s p) (roleAt pol Q s p) = p := by
  apply Prod.ext
  · rfl
  · exact roleOf_involution _ p.2

theorem advance_rolePosition (Q : Query arity n) (s : Spine arity)
    (d : Nat) (hd : d ≤ s.depth) (r : Bool) (a : Letter arity)
    (ha : (path s)[d]? = some a) (hn : d+1 ≤ s.depth) :
    advancePosition s (rolePosition pol Q s d hd r) 1 hn =
      rolePosition pol Q s (d+1) hn (nextRole r (pol a.1 a.2)) := by
  apply Prod.ext
  · rfl
  · change roleOf (stateAt pol Q s d).sign r =
      roleOf (stateAt pol Q s (d+1)).sign (nextRole r (pol a.1 a.2))
    rw [stateAt_step pol Q s d a ha]
    change roleOf (stateAt pol Q s d).sign r =
      roleOf (nextRole (stateAt pol Q s d).sign (pol a.1 a.2)) (nextRole r (pol a.1 a.2))
    cases (stateAt pol Q s d).sign <;> cases r <;> cases pol a.1 a.2 <;> rfl

end NSSE.MultiVarianceRailCoordinates
