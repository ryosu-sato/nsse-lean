import NSSE.ListFiniteSatisfiability

namespace NSSE.ListFiniteSATSize

def stepBudget (n d m : Nat) :=
  2+(n+1)^2+n*(3+m*(5+n*(1+n)+d+BinarySupportSize.solverBudget n d m))
def seedBudget (n d m : Nat) :=
  2+(n+1)^2+n*(2+BinarySupportSize.solverBudget n d m)
def localBudget (n d m : Nat) :=
  4+(6+3*m*(2+n*(1+n)))+(d+1)^2+d*(2+(1+2*stepBudget n d m))
def modelBudget (n d m : Nat) :=
  3+2*seedBudget n d m+CountedModelDepth.budget n+(localBudget n d m+d+1)^(2^n*2^n+1)
def budget (n d m : Nat) :=
  1+(3+(n+1)^2+n*(1+modelBudget n d m))+
    (7+4*m*(1+ListFiniteSatisfiability.literalBudget n d (ListShapeSize.modelBudget n d)))

theorem bound {n d : Nat} (I : StoredSubtypeInput.Input n d) (m : Nat)
    (hu : I.upper.length ≤ m) (hl : I.lower.length ≤ m) (hb : I.bot.length ≤ m) (ht : I.top.length ≤ m) :
    (ListFiniteSatisfiability.decide I).2 ≤ budget n d m := by
  have hq := BinarySupportSize.solver_bound I m hu hl
  have he : StoredShapeInitial.seedBudget I ≤ seedBudget n d m := by
    dsimp only [StoredShapeInitial.seedBudget,seedBudget]
    gcongr
  have hsl : StoredShapeTransition.stepBudget I I.lower.length ≤ stepBudget n d m := by
    dsimp only [StoredShapeTransition.stepBudget,stepBudget]
    gcongr
  have hsu : StoredShapeTransition.stepBudget I I.upper.length ≤ stepBudget n d m := by
    dsimp only [StoredShapeTransition.stepBudget,stepBudget]
    gcongr
  have hc : ListShapeExpansion.localBudget I ≤ localBudget n d m := by
    have hlen : I.lower.length+I.upper.length+I.bot.length ≤ 3*m := by omega
    dsimp only [ListShapeExpansion.localBudget,ListShapeExpansion.labelBudget,
      ListShapeExpansion.nextBudget,localBudget]
    have hn : 1+StoredShapeTransition.stepBudget I I.lower.length+
        StoredShapeTransition.stepBudget I I.upper.length ≤ 1+2*stepBudget n d m := by omega
    gcongr
  have hm : ListFiniteValuation.modelBudget I ≤ modelBudget n d m := by
    dsimp only [ListFiniteValuation.modelBudget,modelBudget]
    gcongr
  have hlen : I.upper.length+I.lower.length+I.bot.length+I.top.length ≤ 4*m := by omega
  apply (ListFiniteSatisfiability.bound I).trans
  dsimp only [ListFiniteValuation.budget,ListFiniteSatisfiability.checkBudget,budget]
  gcongr

theorem mono (n d m N D : Nat) (hn : n ≤ N) (hd : d ≤ D) : budget n d m ≤ budget N D m := by
  have hq := BinarySupportSize.solver_mono n d m N D hn hd
  have hk := CountedModelDepth.mono n N hn
  dsimp only [budget,modelBudget,seedBudget,localBudget,stepBudget,
    ListFiniteSatisfiability.literalBudget,ListShapeSize.modelBudget]
  gcongr <;> omega
end NSSE.ListFiniteSATSize
