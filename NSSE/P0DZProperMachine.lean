import NSSE.P0DZFirstClash
import NSSE.P0ProperLiveness

/-! Exact all-D semantics of a full D/Z branch, with an explicit invalid
sink. Proper birth orientations are retained through symmetric erasure. -/
namespace NSSE.P0DZProperMachine
open P0DZBranch P0DZTrace P0DZVirtualTrace P0DZFirstClash P0ProperMachine P0ProperWords
variable {Q Z A H : Type*}

def machine (J : Branch Q Z A H) : Machine (Option Q) A H where
  initial := some J.initial
  step := advance J
  valid q := q.isSome = true
  head q := J.head (q.getD J.initial)
  birth q r := match q, r with
    | some q, some r => Born J q r
    | _, _ => False

instance validDecision (J : Branch Q Z A H) : DecidablePred (machine J).valid :=
  fun _ => inferInstanceAs (Decidable (_ = true))

theorem state_exact (J : Branch Q Z A H) (w : List A) (k : Nat) :
    state (machine J) w k = properAt J w k := rfl

theorem head_exact (J : Branch Q Z A H) (w : List A) (k : Nat) :
    (machine J).head (state (machine J) w k) = J.head (dState J w k) := rfl

theorem birth_exact (J : Branch Q Z A H) (w : List A) (hc : DComplete J w) (a b : Nat) :
    (machine J).birth (state (machine J) w a) (state (machine J) w b) ↔
      Born J (dState J w a) (dState J w b) := by
  rw [state_exact,state_exact,proper_eq_state J w hc a,proper_eq_state J w hc b]
  rfl

theorem good_iff (J : Branch Q Z A H) (w : List A) :
    GoodWord (machine J) w ↔ DComplete J w ∧ ∀ a b l, ¬Clash J w a b l := by
  constructor
  · intro hw
    have hc : DComplete J w := hw.1 w.length (by omega)
    refine ⟨hc,?_⟩
    intro a b l h
    have ha := h.left_bound
    have hb := h.right_bound
    have he := hw.2 a (by omega) b (by omega) l (by omega) ha hb
      ((birth_exact J w hc a b).mpr h.born) h.letters
    exact h.bad he
  · rintro ⟨hc,hn⟩
    constructor
    · intro k _
      change (properAt J w k).isSome = true
      rw [proper_eq_state J w hc k]
      rfl
    · intro a _ b _ l _ ha hb hborn hm
      change J.head (dState J w (a+l)) = J.head (dState J w (b+l))
      by_contra he
      exact hn a b l ⟨ha,hb,(birth_exact J w hc a b).mp hborn,hm,he⟩

def Live (J : Branch Q Z A H) (w : List A) : Prop :=
  P0ProperLiveness.Live (machine J) w

end NSSE.P0DZProperMachine
