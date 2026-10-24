import NSSE.SubtypePathBounds
import NSSE.ConstraintForwardTables

/-! # Supported nonempty path bounds construct actual forward-automaton runs

Empty-path Support is absorbed into the last letter edge, not replaced by
equality or by an invented epsilon transition. Both side tables are actual.
-/

namespace NSSE.PathBoundsToAutomaton

open SubtypeConstraints SubtypePathBounds ForwardTableAutomaton ConstraintForwardTables

variable {n d : Nat}

theorem upper_raw (Q : Query n d) (side : Side) {x y : Fin n} {word : List (Fin d)}
    (h : UpperPath Q.constraints x word y) (hne : word ≠ []) (v : Token n) :
    (rawNFA (tables Q) side).Runs (some (some x,v)) word (some (some y,none)) := by
  induction h generalizing v with
  | nil hs => exact False.elim (hne rfl)
  | @cons x z y i word hs ht ih =>
      by_cases hw : word = []
      · subst word
        have hu := (upper_correct Q x i y).mpr ((upper_one Q.constraints x y i).mp (.cons hs ht))
        exact .cons (show (rawNFA (tables Q) side).step (some (some x,v)) i
          (some (some y,none)) from Or.inl ⟨hu,rfl⟩) (.nil _)
      · have hu := (upper_correct Q x i z).mpr hs
        exact .cons (show (rawNFA (tables Q) side).step (some (some x,v)) i
          (some (some z,none)) from Or.inl ⟨hu,rfl⟩) (ih hw none)

theorem lower_raw (Q : Query n d) (side : Side) {x y : Fin n} {word : List (Fin d)}
    (h : LowerPath Q.constraints x word y) (hne : word ≠ []) (u : Token n) :
    (rawNFA (tables Q) side).Runs (some (u,some x)) word (some (none,some y)) := by
  induction h generalizing u with
  | nil hs => exact False.elim (hne rfl)
  | @cons x z y i word hs ht ih =>
      by_cases hw : word = []
      · subst word
        have hl := (lower_correct Q x i y).mpr ((lower_one Q.constraints x y i).mp (.cons hs ht))
        exact .cons (show (rawNFA (tables Q) side).step (some (u,some x)) i
          (some (none,some y)) from Or.inr (Or.inl ⟨rfl,hl⟩)) (.nil _)
      · have hl := (lower_correct Q x i z).mpr hs
        exact .cons (show (rawNFA (tables Q) side).step (some (u,some x)) i
          (some (none,some z)) from Or.inr (Or.inl ⟨rfl,hl⟩)) (ih hw none)

theorem pair_raw (Q : Query n d) (side : Side) {x x' y y' : Fin n} {word : List (Fin d)}
    (hu : UpperPath Q.constraints x word x') (hl : LowerPath Q.constraints y word y')
    (hne : word ≠ []) :
    (rawNFA (tables Q) side).Runs (some (some x,some y)) word (some (some x',some y')) := by
  induction hu generalizing y y' with
  | nil hs => exact False.elim (hne rfl)
  | @cons x z x' i word hs ht ih =>
      cases hl with
      | @cons _ z' _ _ _ hls hlt =>
          by_cases hw : word = []
          · subst word
            have hu := (upper_correct Q x i x').mpr ((upper_one Q.constraints x x' i).mp (.cons hs ht))
            have hl := (lower_correct Q y i y').mpr ((lower_one Q.constraints y y' i).mp (.cons hls hlt))
            exact .cons (show (rawNFA (tables Q) side).step (some (some x,some y)) i
              (some (some x',some y')) from Or.inr (Or.inr ⟨hu,hl⟩)) (.nil _)
          · have hu := (upper_correct Q x i z).mpr hs
            have hl := (lower_correct Q y i z').mpr hls
            exact .cons (show (rawNFA (tables Q) side).step (some (some x,some y)) i
              (some (some z,some z')) from Or.inr (Or.inr ⟨hu,hl⟩)) (ih hlt hw)

end NSSE.PathBoundsToAutomaton
