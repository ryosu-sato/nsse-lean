import NSSE.RegularSatisfiabilityTower
import NSSE.CountedTermFiniteDecision
import NSSE.TermFlatteningLiteralSize

/-! Original regular/arbitrary-term SAT and entailment with certified evaluation counts.
These are structural counts, not yet complete machine-time bounds. -/
namespace NSSE.CountedTermRegularDecision
open SubtypeTerms SubtypeTermLayout DirectRankStateTower DirectRankFormulaTower
variable {n d : Nat}

def satisfiable (Q : Query n d) (hd : 0 < d) : Bool × Nat :=
  CountedRegularSatisfiability.decide (TermEntailmentDecision.flat Q hd).constraints

def entails (Q : Query n d) (hd : 0 < d) : Bool × Nat :=
  let s := satisfiable Q hd
  let b := TermFlatteningSize.bothSides Q hd
  (!s.1 || b.1, 2+s.2+b.2)

theorem satisfiable_value (Q : Query n d) (hd : 0 < d) :
    (satisfiable Q hd).1 = TermEntailmentDecision.decideAllSatisfiable Q hd :=
  CountedRegularSatisfiability.value _

theorem satisfiable_correct (Q : Query n d) (hd : 0 < d) :
    (satisfiable Q hd).1 = true ↔ Satisfiable (AbsorbingSubtypeTrees.constructor d) Q := by
  rw [satisfiable_value, TermEntailmentDecision.decideAllSatisfiable_correct]

theorem entails_value (Q : Query n d) (hd : 0 < d) :
    (entails Q hd).1 = TermEntailmentDecision.decideAll Q hd := by
  simp only [entails, satisfiable_value, TermFlatteningSize.bothSides_value]
  simp only [TermEntailmentDecision.decideAll, RegularEntailmentDecision.decideEntails,
    TermEntailmentDecision.decideAllSatisfiable, RegularSubtypeModel.decideSatisfiable, Bool.not_not]

theorem entails_correct (Q : Query n d) (hd : 0 < d) :
    (entails Q hd).1 = true ↔ Entails (AbsorbingSubtypeTrees.constructor d) Q := by
  rw [entails_value, TermEntailmentDecision.decideAll_correct]

theorem satisfiable_regular_correct (Q : Query n d) (hd : 0 < d) :
    (satisfiable Q hd).1 = true ↔ SubtypeTermSemantics.RegularSatisfiable Q := by
  rw [satisfiable_value, TermEntailmentDecision.decideRegularSatisfiable_correct]

theorem entails_regular_correct (Q : Query n d) (hd : 0 < d) :
    (entails Q hd).1 = true ↔ SubtypeTermSemantics.RegularEntails Q := by
  rw [entails_value, TermEntailmentDecision.decideRegular_correct]

theorem satisfiable_bound (Q : Query n d) (hd : 0 < d) :
    (satisfiable Q hd).2 ≤ tower 2 (d+12*TermFlatteningSize.size Q+70) := by
  have h := RegularSatisfiabilityTower.bound (TermEntailmentDecision.flat Q hd).constraints
  have hn := TermFlatteningSize.layout_count Q
  have hm := TermFlatteningLiteralSize.flatten_size Q ⟨0,hd⟩
  apply h.trans
  apply tower_mono 2
  change (layout Q).count+d+
    CountedFiniteSatisfiability.literals (SubtypeTermFlattening.flatten Q ⟨0,hd⟩).constraints+70 ≤ _
  omega

/-- Both SAT and both-side evaluation are charged on actual original terms.
Construction/serialization/bit costs remain outside this counter. -/
theorem entails_bound (Q : Query n d) (hd : 0 < d) :
    (entails Q hd).2 ≤ tower 7
      ((4*TermFlatteningSize.size Q+1)^2+2*d+16*TermFlatteningSize.size Q+102519) := by
  let N := TermFlatteningSize.size Q
  let x := (4*N+1)^2+2*d+16*N+102515
  have hs := satisfiable_bound Q hd
  have hb := TermFlatteningSize.bothSides_bound Q hd
  have hs' : (satisfiable Q hd).2 ≤ tower 7 x := by
    apply hs.trans
    apply (CountedTermFiniteDecision.tower_height 2 7 _ (by omega)).trans
    apply tower_mono 7
    dsimp only [x, N]; omega
  have hb' : (TermFlatteningSize.bothSides Q hd).2 ≤ tower 7 x := by
    apply hb.trans
    apply tower_mono 7
    dsimp only [x, N]
    simp only [pow_two]
    omega
  have hone : 1 ≤ tower 7 x := Nat.one_le_pow _ _ (by omega)
  have h : (entails Q hd).2 ≤ 4*tower 7 x := by
    change 2+(satisfiable Q hd).2+(TermFlatteningSize.bothSides Q hd).2 ≤ _
    omega
  have ht := h.trans (CountedCapEvaluation.mul_tower 6 x 4)
  rw [show x+4 = (4*TermFlatteningSize.size Q+1)^2+2*d+
    16*TermFlatteningSize.size Q+102519 by dsimp only [x, N]] at ht
  exact ht
end NSSE.CountedTermRegularDecision
