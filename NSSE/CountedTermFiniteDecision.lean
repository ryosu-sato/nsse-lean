import NSSE.FiniteSatisfiabilityTower
import NSSE.TermFlatteningLiteralSize

/-! Original finite-term SAT and entailment with certified evaluation counts.
These are structural counts, not yet complete machine-time bounds. -/
namespace NSSE.CountedTermFiniteDecision
open SubtypeTerms SubtypeTermLayout DirectRankStateTower DirectRankFormulaTower
variable {n d : Nat}

def satisfiable (Q : Query n d) (hd : 0 < d) : Bool × Nat :=
  CountedFiniteSatisfiability.decide (TermEntailmentDecision.flat Q hd).constraints

def entails (Q : Query n d) (hd : 0 < d) : Bool × Nat :=
  let s := satisfiable Q hd
  let b := TermFlatteningSize.bothSides Q hd
  (!s.1 || b.1, 2+s.2+b.2)

theorem satisfiable_value (Q : Query n d) (hd : 0 < d) :
    (satisfiable Q hd).1 = TermEntailmentDecision.decideFiniteSatisfiable Q hd :=
  CountedFiniteSatisfiability.value _

theorem satisfiable_correct (Q : Query n d) (hd : 0 < d) :
    (satisfiable Q hd).1 = true ↔ Satisfiable (FiniteSubtypeTrees.constructor d) Q := by
  rw [satisfiable_value, TermEntailmentDecision.decideFiniteSatisfiable_correct]

theorem entails_value (Q : Query n d) (hd : 0 < d) :
    (entails Q hd).1 = TermEntailmentDecision.decideFinite Q hd := by
  simp only [entails, satisfiable_value, TermFlatteningSize.bothSides_value]
  rfl

theorem entails_correct (Q : Query n d) (hd : 0 < d) :
    (entails Q hd).1 = true ↔ Entails (FiniteSubtypeTrees.constructor d) Q := by
  rw [entails_value, TermEntailmentDecision.decideFinite_correct]

theorem satisfiable_bound (Q : Query n d) (hd : 0 < d) :
    (satisfiable Q hd).2 ≤ tower 2 (2*d+16*TermFlatteningSize.size Q+12) := by
  have h := FiniteSatisfiabilityTower.bound (TermEntailmentDecision.flat Q hd).constraints
  have hn := TermFlatteningSize.layout_count Q
  have hm := TermFlatteningLiteralSize.flatten_size Q ⟨0,hd⟩
  apply h.trans
  apply tower_mono 2
  change 2*d+2*(layout Q).count+
    CountedFiniteSatisfiability.literals (SubtypeTermFlattening.flatten Q ⟨0,hd⟩).constraints+12 ≤ _
  omega

theorem tower_height (k l x : Nat) (h : k ≤ l) : tower k x ≤ tower l x := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction r with
  | zero => exact le_rfl
  | succ r ih => exact ih.trans (self_le_exp _)

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
    apply (tower_height 2 7 _ (by omega)).trans
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
end NSSE.CountedTermFiniteDecision
