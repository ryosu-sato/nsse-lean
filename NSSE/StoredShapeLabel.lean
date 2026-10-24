import NSSE.StoredShapeInitial

namespace NSSE.StoredShapeLabel
open StoredSubtypeInput SubtypeShapeGrammar FiniteTreeGrammar
variable {n d : Nat}

def label (I : Input n d) (L U : List (Fin n)) : Label × Nat :=
  let l := CountedShapeLabel.hits I.lower Bound.head L
  let u := CountedShapeLabel.hits I.upper Bound.head U
  let b := CountedShapeLabel.hits I.bot id U
  ((if l.1 then (if u.1 then .node else .top)
    else (if u.1 || b.1 then .bot else .top)),3+l.2+u.2+b.2)

theorem value (I : Input n d) (L U : List (Fin n)) :
    (label I L U).1 = (grammar I.denote).label (L.toFinset,U.toFinset) := by
  simp only [label, CountedShapeLabel.hits_value, grammar, LowF, HighF, HighBot, List.mem_toFinset,
    id_eq, Bool.or_eq_true, decide_eq_true_eq,Input.denote,List.mem_map,Bound.denote]
  simp

theorem bound (I : Input n d) (L U : List (Fin n))
    (hL : L.length ≤ n) (hU : U.length ≤ n) :
    (label I L U).2 ≤ 6+(I.lower.length+I.upper.length+I.bot.length)*(2+n*(1+n)) := by
  have hl := CountedShapeLabel.hits_bound I.lower Bound.head L
  have hu := CountedShapeLabel.hits_bound I.upper Bound.head U
  have hb := CountedShapeLabel.hits_bound I.bot id U
  have hmL := Nat.mul_le_mul_right (1+n) hL
  have hmU := Nat.mul_le_mul_right (1+n) hU
  have hl' := hl.trans (show 1+I.lower.length*(2+L.length*(1+n)) ≤
    1+I.lower.length*(2+n*(1+n)) by gcongr)
  have hu' := hu.trans (show 1+I.upper.length*(2+U.length*(1+n)) ≤
    1+I.upper.length*(2+n*(1+n)) by gcongr)
  have hb' := hb.trans (show 1+I.bot.length*(2+U.length*(1+n)) ≤
    1+I.bot.length*(2+n*(1+n)) by gcongr)
  simp only [label]
  nlinarith
end NSSE.StoredShapeLabel
