import NSSE.P0DZFourChildCut
import NSSE.P0PositionProfiles
import NSSE.P0DZDecision
import Mathlib.Tactic.Ring

/-! Finite full four-rail profiles of actual ordered position sets. The
square matrices include diagonals and deliberately overcount realizable
profiles. Position shuffles retain their ordinary square Boolean code. -/
namespace NSSE.P0DZPositionProfiles
open P0PositionProfiles (position)
open P0DZBranch P0DZDecision
variable {Q Z A H : Type*}

abbrev Bits (s : Nat) := Bool → Bool → Fin s → Fin s → Bool
abbrev Profile (k s : Nat) := (Fin s → Fin k) × Bits s

def profile [DecidableEq A] [DecidableEq H] (J : Branch Q Z A H) (w : List A)
    (k s : Nat) (code : Nat → Fin k) (S : Finset Nat) : Profile k s :=
  (fun i => code (position S i),fun x y i j =>
    @decide (Compatible J w (position S i) x (position S j) y)
      (compatibleDecision J w _ x _ y))

theorem bits_card (s : Nat) : Fintype.card (Bits s) = 2^(4*s*s) := by
  simp only [Bits,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,← pow_mul]
  congr 1
  ring

theorem profile_card (k s : Nat) : Fintype.card (Profile k s) = k^s * 2^(4*s*s) := by
  rw [Fintype.card_prod,bits_card]
  simp only [Fintype.card_fun,Fintype.card_fin]

theorem profile_colors [DecidableEq A] [DecidableEq H] (J : Branch Q Z A H) (w : List A)
    (k s : Nat) (code : Nat → Fin k) (S T : Finset Nat)
    (he : profile J w k s code S = profile J w k s code T) (i : Fin s) :
    code (position S i) = code (position T i) := congrFun (congrArg Prod.fst he) i

theorem profile_matrix [DecidableEq A] [DecidableEq H] (J : Branch Q Z A H) (w : List A)
    (k s : Nat) (code : Nat → Fin k) (S T : Finset Nat)
    (he : profile J w k s code S = profile J w k s code T) (i j : Fin s) (x y : Bool) :
    Compatible J w (position S i) x (position S j) y ↔
      Compatible J w (position T i) x (position T j) y := by
  have hh := congrFun (congrFun (congrFun (congrFun (congrArg Prod.snd he) x) y) i) j
  exact decide_eq_decide.mp hh

end NSSE.P0DZPositionProfiles
