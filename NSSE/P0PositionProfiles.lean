import NSSE.P0FourChildCut
import NSSE.P0TypedSelection
import NSSE.P0CutDecision

/-! Finite encodings of actual ordered word-position sets. Full square
matrices deliberately give larger elementary bounds than the optimized
off-diagonal and binomial encodings of the paper. -/
namespace NSSE.P0PositionProfiles
open P0DDeadReader P0DDeadColor P0CutComparison
variable {Q A H : Type*}

def position (S : Finset Nat) (i : Nat) : Nat :=
  if hi : i < S.card then S.orderEmbOfFin rfl ⟨i,hi⟩ else 0

theorem position_mem (S : Finset Nat) (i : Nat) (hi : i < S.card) : position S i ∈ S := by
  rw [position,dif_pos hi]
  exact Finset.orderEmbOfFin_mem _ _ _

theorem position_increasing (S : Finset Nat) (i j : Nat) (hij : i < j) (hj : j < S.card) :
    position S i < position S j := by
  rw [position,dif_pos (show i < S.card by omega),position,dif_pos hj]
  exact (S.orderEmbOfFin rfl).strictMono hij

theorem position_surjective (S : Finset Nat) (p : Nat) (hp : p ∈ S) :
    ∃ i, i < S.card ∧ position S i = p := by
  have hr : p ∈ Set.range (S.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hp
  obtain ⟨i,hi⟩ := hr
  exact ⟨i.val,i.isLt,by rw [position,dif_pos i.isLt]; exact hi⟩

abbrev Bits (s : Nat) := Fin s → Fin s → Bool
abbrev Profile (k s : Nat) := (Fin s → Fin k) × Bits s

def shuffle (s : Nat) (S T : Finset Nat) : Bits s :=
  fun i j => decide (position S i < position T j)

def profile [DecidableEq A] [DecidableEq H] (J : Reader Q A H) (w : List A)
    (k s : Nat) (code : Nat → Fin k) (S : Finset Nat) : Profile k s :=
  (fun i => code (position S i),fun i j =>
    @decide (Compatible w (leftAt J w) (rightAt J w) (position S i) (position S j))
      (P0CutDecision.compatibleDecision w (leftAt J w) (rightAt J w) _ _))

theorem bits_card (s : Nat) : Fintype.card (Bits s) = 2^(s*s) := by
  simp only [Bits,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  exact (pow_mul 2 s s).symm

theorem profile_card (k s : Nat) : Fintype.card (Profile k s) = k^s * 2^(s*s) := by
  simp only [Profile,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
  rw [← pow_mul]

theorem profile_states [DecidableEq A] [DecidableEq H] (J : Reader Q A H) (w : List A)
    (k s : Nat) (code : Nat → Fin k) (S T : Finset Nat)
    (he : profile J w k s code S = profile J w k s code T) (i : Fin s) :
    code (position S i) = code (position T i) := congrFun (congrArg Prod.fst he) i

theorem profile_matrix [DecidableEq A] [DecidableEq H] (J : Reader Q A H) (w : List A)
    (k s : Nat) (code : Nat → Fin k) (S T : Finset Nat)
    (he : profile J w k s code S = profile J w k s code T) (i j : Fin s) :
    Compatible w (leftAt J w) (rightAt J w) (position S i) (position S j) ↔
      Compatible w (leftAt J w) (rightAt J w) (position T i) (position T j) := by
  have hh := congrFun (congrFun (congrArg Prod.snd he) i) j
  exact decide_eq_decide.mp hh

theorem shuffle_order (s : Nat) (S T U V : Finset Nat) (he : shuffle s S T = shuffle s U V)
    (i j : Fin s) : position S i < position T j ↔ position U i < position V j :=
  decide_eq_decide.mp (congrFun (congrFun he i) j)

end NSSE.P0PositionProfiles
