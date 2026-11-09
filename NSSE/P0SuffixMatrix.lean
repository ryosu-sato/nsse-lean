import NSSE.P0SuffixWords

/-! Executable decorated-word comparisons and the exact ordered suffix
matrix. Diagonal entries are retained here; a cotree graph uses only the
off-diagonal entries. -/
namespace NSSE.P0SuffixMatrix
open P0DDeadReader P0CutComparison P0SuffixWords P0DDeadColor
variable {Q A H : Type*}

def relDecision [DecidableEq A] [DecidableEq H] (endX endY : H) :
    (s t : List (H × A)) → Decidable (Rel endX endY s t)
  | [], [] => inferInstanceAs (Decidable (endX = endY))
  | [], (h,_)::_ => inferInstanceAs (Decidable (endX = h))
  | (h,_)::_, [] => inferInstanceAs (Decidable (h = endY))
  | (h,a)::s, (k,b)::t => by
    letI := relDecision endX endY s t
    change Decidable (h = k ∧ (a = b → Rel endX endY s t))
    infer_instance

def conflict [DecidableEq A] [DecidableEq H] (endX endY : H) (s t : List (H × A)) : Bool :=
  !(@decide (Rel endX endY s t) (relDecision endX endY s t))

theorem conflict_correct [DecidableEq A] [DecidableEq H] (endX endY : H) (s t : List (H × A)) :
    conflict endX endY s t = true ↔ ¬ Rel endX endY s t := by
  simp only [conflict,Bool.not_eq_true',decide_eq_false_iff_not]

def matrix [DecidableEq A] [DecidableEq H] (J : Reader Q A H) (w : List A)
    (a b : Fin (w.length+1)) : Bool :=
  conflict J.endX J.endY (tailWord J w a) (tailWord J w b)

theorem matrix_correct [DecidableEq A] [DecidableEq H] (J : Reader Q A H) (w : List A)
    (hc : Complete J w) (a b : Fin (w.length+1)) :
    matrix J w a b = true ↔ ¬ Compatible w (leftAt J w) (rightAt J w) a b := by
  rw [matrix,conflict_correct,← tailWord_exact J w hc a b]

theorem same_color_zero [DecidableEq A] [DecidableEq H] (J : Reader Q A H) (w : List A)
    (hc : Complete J w) (a b : Fin (w.length+1)) (hne : a ≠ b)
    (he : color J w a = color J w b) : matrix J w a b = false ∧ matrix J w b a = false := by
  have hn := proper_coloring J w hc a b (fun h => hne (Fin.ext h)) he
  have hh : Compatible w (leftAt J w) (rightAt J w) a b ∧
      Compatible w (leftAt J w) (rightAt J w) b a := by
    simpa only [Adjacent,not_or,not_not] using hn
  constructor
  · rw [Bool.eq_false_iff]
    intro h
    exact ((matrix_correct J w hc a b).mp h) hh.1
  · rw [Bool.eq_false_iff]
    intro h
    exact ((matrix_correct J w hc b a).mp h) hh.2

/-- Head-separated nonempty children have a join in both orientations. -/
theorem different_heads (endX endY h k : H) (a b : A) (s t : List (H × A)) (hne : h ≠ k) :
    ¬ Rel endX endY ((h,a)::s) ((k,b)::t) ∧ ¬ Rel endX endY ((k,b)::t) ((h,a)::s) := by
  exact ⟨fun h => hne h.1,fun h => hne h.1.symm⟩

/-- Equal-head children separated by literal letters form a union. -/
theorem different_letters (endX endY h : H) (a b : A) (s t : List (H × A)) (hne : a ≠ b) :
    Rel endX endY ((h,a)::s) ((h,b)::t) ∧ Rel endX endY ((h,b)::t) ((h,a)::s) := by
  exact ⟨⟨rfl,fun he => False.elim (hne he)⟩,⟨rfl,fun he => False.elim (hne he.symm)⟩⟩

theorem same_letter (endX endY h : H) (a : A) (s t : List (H × A)) :
    Rel endX endY ((h,a)::s) ((h,a)::t) ↔ Rel endX endY s t := by
  simp only [Rel,true_and,true_implies]

/-- Terminal against a proper head has at least one directed conflict,
including when that head equals one of the terminal labels. -/
theorem terminal_join (endX endY h : H) (a : A) (s : List (H × A)) (hne : endX ≠ endY) :
    ¬ Rel endX endY [] ((h,a)::s) ∨ ¬ Rel endX endY ((h,a)::s) [] := by
  by_cases he : endX = h
  · exact Or.inr (fun h' => hne (he.trans h'))
  · exact Or.inl he

end NSSE.P0SuffixMatrix
