import NSSE.CountedForwardEvaluation
import NSSE.TermEntailmentDecision

/-! Original nested term-node size bounds the actual flattening variable count. -/

namespace NSSE.TermFlatteningSize

open SubtypeTerms SubtypeTermLayout

variable {n d : Nat}

def nodes : Term n d → Nat
  | .var _ => 1
  | .bot => 1
  | .top => 1
  | .node c => 1+((List.finRange d).map (fun i => nodes (c i))).sum

theorem subterms_length (t : Term n d) : (subterms t).length = nodes t := by
  induction t with
  | var _ => rfl
  | bot => rfl
  | top => rfl
  | node c ih =>
    simp [subterms, nodes, List.length_flatMap, List.map_map, Function.comp_def, ih, Nat.add_comm]

def literalNodes : Literal n d → Nat
  | .le a b => 1+nodes a+nodes b
  | .eq a b => 1+nodes a+nodes b

def size (Q : Query n d) := n+nodes Q.left+nodes Q.right+(Q.premises.map literalNodes).sum+1

theorem expanded_length (ps : List (Literal n d)) :
    (ps.flatMap inequalities).length ≤ 2*(ps.map literalNodes).sum := by
  induction ps with
  | nil => simp
  | cons a ps ih =>
    cases a <;> simp only [List.flatMap_cons, inequalities, List.length_append, List.length_cons,
      List.length_nil, List.map_cons, List.sum_cons, literalNodes] <;> omega

theorem expanded_terms (ps : List (Literal n d)) :
    ((ps.flatMap inequalities).flatMap (fun p => subterms p.1++subterms p.2)).length ≤
      2*(ps.map literalNodes).sum := by
  induction ps with
  | nil => simp
  | cons a ps ih =>
    cases a <;> simp only [List.flatMap_cons, inequalities, List.flatMap_append, List.flatMap_nil,
      List.append_nil, List.length_append, subterms_length, List.map_cons, List.sum_cons, literalNodes] <;> omega

theorem layout_count (Q : Query n d) : (layout Q).count ≤ 4*size Q := by
  have hp := expanded_length Q.premises
  have ht := expanded_terms Q.premises
  simp only [Layout.count, layout, terms, List.length_append, subterms_length, expanded, size]
  omega

def sideDecision (Q : Query n d) (hd : 0 < d) (side : ForwardTableAutomaton.Side) : Bool × Nat :=
  CountedForwardEvaluation.tableDecision (ConstraintForwardTables.tables (TermEntailmentDecision.flat Q hd)) side

theorem sideDecision_correct (Q : Query n d) (hd : 0 < d) (side : ForwardTableAutomaton.Side) :
    (sideDecision Q hd side).1 = true ↔
      ForwardCapAutomaton.Universal (ConstraintForwardTables.automaton (TermEntailmentDecision.flat Q hd) side) :=
  CountedForwardEvaluation.tableDecision_correct _ _

theorem sideDecision_bound (Q : Query n d) (hd : 0 < d) (side : ForwardTableAutomaton.Side) :
    (sideDecision Q hd side).2 ≤ DirectRankStateTower.tower 7 ((4*size Q+1)*(4*size Q+1)+d+102500) := by
  have h := CountedForwardEvaluation.tableDecision_bound
    (ConstraintForwardTables.tables (TermEntailmentDecision.flat Q hd)) side
  have hn := layout_count Q
  apply h.trans
  apply DirectRankFormulaTower.tower_mono 7
  have hp := Nat.mul_le_mul (Nat.add_le_add_right hn 1) (Nat.add_le_add_right hn 1)
  omega

def bothSides (Q : Query n d) (hd : 0 < d) : Bool × Nat :=
  let a := sideDecision Q hd .left
  let b := sideDecision Q hd .right
  (a.1 && b.1,1+a.2+b.2)

theorem bothSides_value (Q : Query n d) (hd : 0 < d) :
    (bothSides Q hd).1 = ConstraintForwardTables.decideBothSides (TermEntailmentDecision.flat Q hd) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bothSides, Bool.and_eq_true, sideDecision_correct, ConstraintForwardTables.decideBothSides_correct]

theorem bothSides_bound (Q : Query n d) (hd : 0 < d) :
    (bothSides Q hd).2 ≤ DirectRankStateTower.tower 7 ((4*size Q+1)*(4*size Q+1)+d+102503) := by
  let x := (4*size Q+1)*(4*size Q+1)+d+102500
  have ha := sideDecision_bound Q hd .left
  have hb := sideDecision_bound Q hd .right
  have hone : 1 ≤ DirectRankStateTower.tower 7 x := Nat.one_le_pow _ _ (by omega)
  have h : (bothSides Q hd).2 ≤ 3*DirectRankStateTower.tower 7 x := by
    change 1+(sideDecision Q hd .left).2+(sideDecision Q hd .right).2 ≤ _
    dsimp only [x] at hone ⊢
    omega
  exact h.trans (CountedCapEvaluation.mul_tower 6 x 3)

end NSSE.TermFlatteningSize
