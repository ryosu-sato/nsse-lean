import NSSE.StoredRankSizeTower

/-! The tower height of the cost recursion of the stored `solve`: the cost
envelope is a polynomial in level-3 quantities (the witness length, `2^E`,
`3^E`), and the remaining budgets of one step are polynomials of level-2
quantities and single exponentials of them; one rank adds a constant to the
argument of `tower 3`.  All expressions are transcriptions of Lean's own
unfolding of the budget definitions, each proved equal to the function it
transcribes. -/
namespace NSSE.StoredRankCostTower
open StoredRankHorizon StoredRankSolveBounds StoredRankSolveEnvelope StoredRankCostEnvelope StoredRankCostHorizon
open StoredRankHorizonTower StoredRankSizeTower DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope
open StoredRelationalFormula (weight)

/-! ### The block-cost polynomial -/

set_option maxHeartbeats 4000000 in
def blockBudgetExpr : Expr :=
  let X : Expr := .var 0
  12 + (7 + (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + (2 + (X + 1) ^ 2 + X * (1 + (5 + X)))))))) + (4 + (8 + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3))))) + (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * (X + 3))))))))) + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3))))))))) + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * (X + 3)) + (5 + (2 + (X + 1) ^ 2 + X * (3 + 11 * X)) + 6 * X + 2 * X * X) + (13 + 2 * X * X * (X + 3) + (7 + (4 + (2 + (2 * X * X + 1) ^ 2 + 2 * X * X * (1 + (3 + (7 + (7 + X * (2 * X * X + 2) + 2 * X * X) + (1 + (1 + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3))) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * (X + 3) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + (X + 13 + (3 + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (4 + X * (X + 2) + X)))) + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (8 + X * (X + 3) + X * (X + 2) + X + (X + 1) * X)))))) + (2 + (2 + (4 + 1) ^ 2 + 4 * (1 + (8 + (4 + (2 + (2 + 1) ^ 2 + 2 * (1 + 19)) + 6 * 2) + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3))) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * (X + 3) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + (3 + 2 * 14 + X * (2 + 14)) * (3 + (15 + 5 * (X + 3) + (29 + 4 * (X + 3) + (6 + (X + 3) + X * (4 + X * (24 + 4 * (X + 3)))))))))) + 4 * 4)) + (3 + 2 * 1 + X * (2 + 1)) * (109 + 4 * (3 + (15 + 5 * (X + 3) + (29 + 4 * (X + 3) + (6 + (X + 3) + X * (4 + X * (24 + 4 * (X + 3))))))))))))) + 6 * (2 * X * X)) + (4 + (2 + (X + 1) ^ 2 + X * (1 + (4 + (2 + (2 * X * X + 1) ^ 2 + 2 * X * X * (1 + (10 + (7 + X * (2 * X * X + 2) + 2 * X * X) + (2 + (2 + (2 * X * X + 1) ^ 2 + 2 * X * X * (1 + (7 + (7 + X * (2 * X * X + 2) + 2 * X * X) + (1 + (1 + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3))) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * (X + 3) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + (X + 13 + (3 + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (4 + X * (X + 2) + X)))) + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (8 + X * (X + 3) + X * (X + 2) + X + (X + 1) * X)))))) + (2 + (2 + (4 + 1) ^ 2 + 4 * (1 + (8 + (4 + (2 + (2 + 1) ^ 2 + 2 * (1 + 19)) + 6 * 2) + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3))) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * (X + 3) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + (3 + 2 * 14 + X * (2 + 14)) * (3 + (15 + 5 * (X + 3) + (29 + 4 * (X + 3) + (6 + (X + 3) + X * (4 + X * (24 + 4 * (X + 3)))))))))) + 4 * 4)) + (3 + 2 * 1 + X * (2 + 1)) * (109 + 4 * (3 + (15 + 5 * (X + 3) + (29 + 4 * (X + 3) + (6 + (X + 3) + X * (4 + X * (24 + 4 * (X + 3)))))))))))) + 4 * (2 * X * X))))) + 6 * (2 * X * X)))) + 6 * X)) + (2 + (2 + (2 * X * X + 1) ^ 2 + 2 * X * X * (1 + (7 + (7 + X * (2 * X * X + 2) + 2 * X * X) + (1 + (1 + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3))) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * (X + 3) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + (X + 13 + (3 + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (4 + X * (X + 2) + X)))) + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (8 + X * (X + 3) + X * (X + 2) + X + (X + 1) * X)))))) + (2 + (2 + (4 + 1) ^ 2 + 4 * (1 + (8 + (4 + (2 + (2 + 1) ^ 2 + 2 * (1 + 19)) + 6 * 2) + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3))) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * (X + 3)) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * (X + 3) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 3)))))) + (3 + 2 * 14 + X * (2 + 14)) * (3 + (15 + 5 * (X + 3) + (29 + 4 * (X + 3) + (6 + (X + 3) + X * (4 + X * (24 + 4 * (X + 3)))))))))) + 4 * 4)) + (3 + 2 * 1 + X * (2 + 1)) * (109 + 4 * (3 + (15 + 5 * (X + 3) + (29 + 4 * (X + 3) + (6 + (X + 3) + X * (4 + X * (24 + 4 * (X + 3)))))))))))) + 4 * (2 * X * X)))) + (4 + (8 + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))) + (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X)))))))) + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))))))) + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X) + (5 + (2 + (X + 1) ^ 2 + X * (3 + 11 * X)) + 6 * X + 2 * X * X) + (13 + 2 * X * X * (X + 3) + (7 + (4 + (2 + (2 * X * X + 1) ^ 2 + 2 * X * X * (1 + (3 + (7 + (7 + X * (2 * X * X + 2) + 2 * X * X) + (1 + (1 + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X)) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * X) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * X) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * X + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + (X + 13 + (3 + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (4 + X * (X + 2) + X)))) + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (8 + X * (X + 3) + X * (X + 2) + X + (X + 1) * X)))))) + (2 + (2 + (4 + 1) ^ 2 + 4 * (1 + (8 + (4 + (2 + (2 + 1) ^ 2 + 2 * (1 + 19)) + 6 * 2) + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X)) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * X) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * X) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * X + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + (3 + 2 * 14 + X * (2 + 14)) * (3 + (15 + 5 * X + (29 + 4 * X + (6 + X + X * (4 + X * (24 + 4 * X))))))))) + 4 * 4)) + (3 + 2 * 1 + X * (2 + 1)) * (109 + 4 * (3 + (15 + 5 * X + (29 + 4 * X + (6 + X + X * (4 + X * (24 + 4 * X)))))))))))) + 6 * (2 * X * X)) + (4 + (2 + (X + 1) ^ 2 + X * (1 + (4 + (2 + (2 * X * X + 1) ^ 2 + 2 * X * X * (1 + (10 + (7 + X * (2 * X * X + 2) + 2 * X * X) + (2 + (2 + (2 * X * X + 1) ^ 2 + 2 * X * X * (1 + (7 + (7 + X * (2 * X * X + 2) + 2 * X * X) + (1 + (1 + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X)) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * X) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * X) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * X + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + (X + 13 + (3 + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (4 + X * (X + 2) + X)))) + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (8 + X * (X + 3) + X * (X + 2) + X + (X + 1) * X)))))) + (2 + (2 + (4 + 1) ^ 2 + 4 * (1 + (8 + (4 + (2 + (2 + 1) ^ 2 + 2 * (1 + 19)) + 6 * 2) + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X)) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * X) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * X) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * X + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + (3 + 2 * 14 + X * (2 + 14)) * (3 + (15 + 5 * X + (29 + 4 * X + (6 + X + X * (4 + X * (24 + 4 * X))))))))) + 4 * 4)) + (3 + 2 * 1 + X * (2 + 1)) * (109 + 4 * (3 + (15 + 5 * X + (29 + 4 * X + (6 + X + X * (4 + X * (24 + 4 * X))))))))))) + 4 * (2 * X * X))))) + 6 * (2 * X * X)))) + 6 * X)) + (2 + (2 + (2 * X * X + 1) ^ 2 + 2 * X * X * (1 + (7 + (7 + X * (2 * X * X + 2) + 2 * X * X) + (1 + (1 + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X)) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * X) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * X) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * X + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + (X + 13 + (3 + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (4 + X * (X + 2) + X)))) + (2 + (2 + 1) ^ 2 + 2 * (1 + (3 + (8 + X * (X + 3) + X * (X + 2) + X + (X + 1) * X)))))) + (2 + (2 + (4 + 1) ^ 2 + 4 * (1 + (8 + (4 + (2 + (2 + 1) ^ 2 + 2 * (1 + 19)) + 6 * 2) + (31 + 2 * X * X + (4 + 4 * X * X + (7 + 2 * (2 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X)) + (23 + 4 * X + (3 + 2 * 2 + X * (2 + 2)) * X) + (3 + (44 + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))) + (7 + (42 + (3 + 2 * 2 + X * (2 + 2)) * X) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (19 + 4 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * X + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + 4 * X))) + 4 * X)) + (7 + 2 * (24 + 2 * X + (3 + 2 * 1 + X * (2 + 1)) * X))))) + (3 + 2 * 14 + X * (2 + 14)) * (3 + (15 + 5 * X + (29 + 4 * X + (6 + X + X * (4 + X * (24 + 4 * X))))))))) + 4 * 4)) + (3 + 2 * 1 + X * (2 + 1)) * (109 + 4 * (3 + (15 + 5 * X + (29 + 4 * X + (6 + X + X * (4 + X * (24 + 4 * X))))))))))) + 4 * (2 * X * X)))) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (9 + 3 * X + (3 + 2 * 1 + X * (2 + 1)) * X))) + 4 * X) + (5 + (3 + 2 * 1 + X * (2 + 1)) * (1 + X * (8 + 2 * X)) + (3 + 2 * 1 + X * (2 + 1)) * (1 + X * (8 + 2 * X) + 2)) + X + (5 + (3 + 2 * 1 + X * (2 + 1)) * X + (3 + 2 * 1 + X * (2 + 1)) * (X + 2))

set_option maxHeartbeats 4000000 in
theorem blockBudget_diag (z : Nat) : StoredBlockArrayPackage.budget z z z z z = eval ![z,0,0,0] blockBudgetExpr := by
  simp only [StoredBlockArrayPackage.budget, StoredIdentityMarkers.budget, StoredIdentityMarkers.matrixBudget,
    StoredGuardedArrayPackage.budget, StoredGuardedArrayPackage.labelCost, StoredGuardedArrayPackage.labelSize,
    StoredRowTransport.budget, StoredRowTransport.vectorBudget, StoredRowTransport.matrixBudget,
    StoredRawStates.budget, StoredRawStates.entriesBudget, StoredRawSkippedRun.nodeBudget, StoredRawSkippedRun.costBudget,
    StoredRawAutomaton.nodeBudget, StoredRawAutomaton.costBudget,
    StoredRawTransition.sizeBudget, StoredRawSwitchGuard.sizeBudget, StoredDynamicRun.labelSize, StoredDynamicRun.labelCost,
    StoredDynamicColumn.budget, StoredArrayColumns.budget, StoredArrayColumns.finiteBudget,
    StoredArrayParameterAtoms.initialBudget, StoredArrayParameterAtoms.termBudget, StoredArrayParameterAtoms.atomBudget,
    StoredArrayAbsence.packageBudget, StoredArrayAbsence.matrixBudget, StoredArrayAbsence.stepBudget,
    StoredArrayValidity.everyBudget, StoredArrayValidity.stepBudget, StoredArrayValidity.budget,
    StoredArrayEquality.matrixBudget, StoredRunTable.budget, StoredRunTable.matrixBudget, StoredRunTable.anyBudget,
    StoredRunTable.cellBudget, StoredRunTable.bitBudget, StoredRunTable.liftBudget, StoredRunTable.successorBudget,
    StoredArrayCoordinates.flagBudget, StoredArrayCoordinates.letterBudget, StoredDynamicColumn.cellBudget,
    StoredRawEndpoints.initialBudget, StoredRawEndpoints.finalBudget, StoredRawEndpoints.dataBudget,
    StoredRawTransition.budget, StoredRawBackGuards.sharedBudget, StoredRawBackGuards.pairBudget,
    StoredRawBackGuards.backBudget, StoredRawSwitchGuard.budget, StoredRawSwitchGuard.parameterBudget,
    StoredRawSwitchGuard.termBudget, StoredForwardTableBuild.tabBudget, StoredRelationalFormula.weight,
    blockBudgetExpr, eval, Matrix.cons_val_zero]

/-! ### The lowering cost with the exponential atoms abstracted -/

def costGT (k N c q F E e2 e3 T P Q B K : Nat) :=
  let A := 8+24*T+(P+StoredBlockArrayPackage.sizeBudget c T B+5+10*T)
  let S := 5+(3+T*(8+8*q))+(A+5)*F
  let m := (T+1)*q+(T+1)*q
  let signed := 30+StoredArraySignedAtoms.equalBudget q T+
    (4+k+(Q+StoredBlockArrayPackage.budget c q T B K)+StoredArrayAbsence.packageBudget q T)
  let vj := 5+StoredArrayValidity.budget q T+5*(3+T*(8+8*q))+
    (signed+4+StoredRelationalElimination.joinBudget ((A+5)*F) K)*F+StoredRelationalElimination.joinBudget S K
  let closure := 7+vj+StoredScalarArrayClosure.countBudget q T+m+weight K (m+4)*S+(5+3*K)*S+6*(m+S)
  let wl := 8+StoredWitnessExponent.budget k N+(E+1)*7*e3+q*(q+2)+q*q+e2*(q*q+3)
  let scalarSize := S+5*m
  let fresh := 4+StoredFamilyTransport.budget k N 1 B K+StoredRowTransport.budget c 1 B K+(1+wl+closure)+
    StoredFreshTags.budget scalarSize K
  7+11*F+fresh+weight K 6*(scalarSize+18)

theorem costG_eq (k N c q F E P Q B K : Nat) :
    costG k N c q F E P Q B K = costGT k N c q F E (2^E) (3^E) ((q*q+1)*2^E) P Q B K := by
  simp only [costG, costGT, CountedNaturalPower.budget]

theorem costGT_mono {k k' N N' c c' q q' F F' E E' e2 e2' e3 e3' T T' P P' Q Q' B B' K K' : Nat}
    (hk : k ≤ k') (hN : N ≤ N') (hc : c ≤ c') (hq : q ≤ q') (hF : F ≤ F') (hE : E ≤ E') (h2 : e2 ≤ e2')
    (h3 : e3 ≤ e3') (hT : T ≤ T') (hP : P ≤ P') (hQ : Q ≤ Q') (hB : B ≤ B') (hK' : K ≤ K') :
    costGT k N c q F E e2 e3 T P Q B K ≤ costGT k' N' c' q' F' E' e2' e3' T' P' Q' B' K' := by
  have h1 := familyTransportBudget_mono hk hN (le_refl 1) hB hK'
  have h2' := rowTransportBudget_mono hc (le_refl 1) hB hK'
  have h3' := weight_mono' hK' (le_refl 6)
  have hbs := blockSize_mono hc hT hB
  have hbb := blockBudget_mono hc hq hT hB hK'
  simp only [costGT]
  gcongr

set_option maxHeartbeats 4000000 in
def costExpr : Expr :=
  let X : Expr := .var 0
  7 + 11 * X + (4 + (2 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (8 + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))) + (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X)))))))) + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))))))) + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X))))) + (8 + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))) + (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X)))))))) + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))))))) + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X) + (1 + (8 + (9 + (8 + (6 + 1) * (X + 5) * (X + 1) ^ 6 + (8 + 1) * (X + 5) * (X + 1) ^ 8 + 6 * X ^ 6 + 10 * X ^ 8) + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (8 + (6 + 1) * (X + 5) * (X + 1) ^ 6 + (8 + 1) * (X + 5) * (X + 1) ^ 8 + 6 * X ^ 6 + 10 * X ^ 8)))) + 3 * X + (X + 1) * (2 * X ^ 6 + 8 * X ^ 8)) + (X + 1) * 7 * X + X * (X + 2) + X * X + X * (X * X + 3)) + (7 + (5 + (4 + (2 + (X + 1) ^ 2 + X * (1 + (4 + (2 + (X + 1) ^ 2 + X * (1 + (8 + 2 * (4 + X * (X + 2) + X)))) + 6 * X))) + 6 * X) + 5 * (3 + X * (8 + 8 * X)) + (30 + (10 + (4 + (2 + (X + 1) ^ 2 + X * (1 + (30 + 2 * (4 + X * (X + 2) + X) + 2 * (8 + X * (X + 3) + X * (X + 2) + X + (X + 1) * X)))) + 6 * X) + 5 * (5 + 24 * X)) + (4 + X + (X + blockBudgetExpr) + (5 + (4 + (2 + (X + 1) ^ 2 + X * (1 + (10 + (4 + X * (X + 2) + X) + (8 + X * (X + 3) + X * (X + 2) + X + (X + 1) * X)))) + 6 * X) + 5 * (5 + 10 * X))) + 4 + (X + 1) * (2 * ((8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X) ^ 2 + 26 * ((8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X) + 9)) * X + (X + 1) * (2 * (5 + (3 + X * (8 + 8 * X)) + (8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X) ^ 2 + 26 * (5 + (3 + X * (8 + 8 * X)) + (8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X) + 9)) + (6 + X + X * (X + 3) + (X + 1) * X) + ((X + 1) * X + (X + 1) * X) + (3 + 2 * ((X + 1) * X + (X + 1) * X + 4) + X * (2 + ((X + 1) * X + (X + 1) * X + 4))) * (5 + (3 + X * (8 + 8 * X)) + (8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X) + (5 + 3 * X) * (5 + (3 + X * (8 + 8 * X)) + (8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X) + 6 * ((X + 1) * X + (X + 1) * X + (5 + (3 + X * (8 + 8 * X)) + (8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X)))) + (26 + (X + 1) * (2 * (5 + (3 + X * (8 + 8 * X)) + (8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X + 5 * ((X + 1) * X + (X + 1) * X) + 3) ^ 2 + 26 * (5 + (3 + X * (8 + 8 * X)) + (8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X + 5 * ((X + 1) * X + (X + 1) * X) + 3) + 9) + (3 + 2 * 6 + X * (2 + 6)) * (5 + (3 + X * (8 + 8 * X)) + (8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X + 5 * ((X + 1) * X + (X + 1) * X) + 8))) + (3 + 2 * 6 + X * (2 + 6)) * (5 + (3 + X * (8 + 8 * X)) + (8 + 24 * X + (X + blockSizeExpr + 5 + 10 * X) + 5) * X + 5 * ((X + 1) * X + (X + 1) * X) + 18)

set_option maxHeartbeats 4000000 in
theorem costGT_diag (z : Nat) : costGT z z z z z z z z z z z z z = eval ![z,0,0,0] costExpr := by
  rw [costExpr]
  simp only [costGT, StoredArraySignedAtoms.equalBudget, StoredArrayEquality.matrixBudget, StoredArrayEquality.positionBudget,
    StoredArrayCoordinates.flagBudget, StoredArrayCoordinates.letterBudget, StoredArrayAbsence.packageBudget,
    StoredArrayAbsence.matrixBudget, StoredArrayAbsence.stepBudget, StoredArrayValidity.budget, StoredArrayValidity.everyBudget,
    StoredArrayValidity.stepBudget, StoredRelationalElimination.joinBudget, StoredScalarArrayClosure.countBudget,
    StoredWitnessExponent.budget, StoredWitnessExponent.rowBudget, CountedNaturalPower.budget,
    UnifiedBlockWitnessBound.rowExponent, StoredFamilyTransport.budget, StoredRowTransport.budget,
    StoredRowTransport.vectorBudget, StoredRowTransport.matrixBudget, StoredFreshTags.budget,
    StoredForwardTableBuild.tabBudget, StoredRelationalFormula.weight, blockSize_diag, blockBudget_diag,
    eval, Matrix.cons_val_zero]

/-! ### The other budgets of one step -/

def seedBudgetExpr : Expr :=
  let X : Expr := .var 0
  1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + (2 + (X + 1) ^ 2 + X * (1 + (9 + 2 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * X + (2 * X + 7 + (3 + 2 * 1 + X * (2 + 1) + (3 + 2 * 5 + X * (2 + 5))) * X) + 2 * ((X + 1) * (2 * (5 + (X + 5) + X) ^ 2 + 26 * (5 + (X + 5) + X) + 9))))) + (2 + X * (10 + (X + 5) + 2 * X + 8 + (3 + 2 * 2 + X * (2 + 2)) * (10 + (X + 5) + 2 * X) + (3 + 2 * (10 + (X + 5) + 2 * X + 3) + X * (2 + (10 + (X + 5) + 2 * X + 3))) * (1 + X * (3 + (10 + (X + 5) + 2 * X)))))))) + (2 + X * (1 + X * (3 + (10 + (X + 5) + 2 * X)) + 8 + (3 + 2 * 2 + X * (2 + 2)) * (1 + X * (3 + (10 + (X + 5) + 2 * X))) + (3 + 2 * (1 + X * (3 + (10 + (X + 5) + 2 * X)) + 3) + X * (2 + (1 + X * (3 + (10 + (X + 5) + 2 * X)) + 3))) * (1 + X * (3 + (1 + X * (3 + (10 + (X + 5) + 2 * X)))))))
theorem seedBudget_diag (z : Nat) : StoredRelationalNonempty.seedBudget z z z = eval ![z,0,0,0] seedBudgetExpr := by
  simp only [StoredRelationalNonempty.seedBudget, StoredRelationalNonempty.budget, StoredRelationalNonempty.innerBudget,
    StoredRelationalEndpoints.budget, StoredRelationalDisjunction.budget, StoredRelationalDisjunction.stepBudget,
    StoredRelationalRow.dataBudget, StoredRelationalElimination.joinBudget, StoredForwardTableBuild.tabBudget,
    StoredRelationalFormula.weight, seedBudgetExpr, eval, Matrix.cons_val_zero]

/-- `nonemptyBudget z z z` with `3^z` as `var 1` and `9^z` as `var 2`. -/
def nonemptyBudgetExpr : Expr :=
  let X : Expr := .var 0
  let Y : Expr := .var 1
  let W : Expr := .var 2
  1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + (2 + (X + 1) ^ 2 + X * (1 + (9 + 2 * X + 2 * (3 + 2 * 1 + X * (2 + 1)) * X + (1 + (X + 1) ^ 2 + (24 + X + (5 + (1 + (2 + (1 + 1) ^ 2 + 1 * (1 + (2 * X + 7 + (3 + 2 * 1 + X * (2 + 1) + (3 + 2 * 5 + X * (2 + 5))) * X))) + (2 + 1 * (1 + 8 + (3 + 2 * 2 + X * (2 + 2)) * X + (3 + 2 * (1 + 3) + X * (2 + (1 + 3))) * (1 + 1 * (3 + X))))) + (X + 1) * (2 * (X + 9) ^ 2 + 26 * (X + 9) + 9)) + (X + 1) * (2 * (X + 13 + 6) ^ 2 + 26 * (X + 13 + 6) + 9) + 100 * (X + 1) * (X + 13 + 6 + 4) ^ 2) * W) + 2 * ((X + 1) * (2 * (5 + (X + 23) * Y + X) ^ 2 + 26 * (5 + (X + 23) * Y + X) + 9))))) + (2 + X * (10 + (X + 23) * Y + 2 * X + 8 + (3 + 2 * 2 + X * (2 + 2)) * (10 + (X + 23) * Y + 2 * X) + (3 + 2 * (10 + (X + 23) * Y + 2 * X + 3) + X * (2 + (10 + (X + 23) * Y + 2 * X + 3))) * (1 + X * (3 + (10 + (X + 23) * Y + 2 * X)))))))) + (2 + X * (1 + X * (3 + (10 + (X + 23) * Y + 2 * X)) + 8 + (3 + 2 * 2 + X * (2 + 2)) * (1 + X * (3 + (10 + (X + 23) * Y + 2 * X))) + (3 + 2 * (1 + X * (3 + (10 + (X + 23) * Y + 2 * X)) + 3) + X * (2 + (1 + X * (3 + (10 + (X + 23) * Y + 2 * X)) + 3))) * (1 + X * (3 + (1 + X * (3 + (10 + (X + 23) * Y + 2 * X)))))))
theorem nonemptyBudget_diag (z : Nat) :
    StoredRelationalNonempty.nonemptyBudget z z z = eval ![z,3^z,9^z,0] nonemptyBudgetExpr := by
  simp only [StoredRelationalNonempty.nonemptyBudget, StoredRelationalNonempty.budget, StoredRelationalNonempty.innerBudget,
    StoredRelationalEndpoints.budget, StoredRelationalDisjunction.budget, StoredRelationalDisjunction.stepBudget,
    StoredRelationalReachability.budget, StoredRelationalReachability.edgeBudget, StoredRelationalElimination.budget,
    StoredRelationalRowEdges.edgeBudget, StoredRelationalRow.dataBudget,
    StoredRelationalElimination.joinBudget, StoredForwardTableBuild.tabBudget, StoredRelationalFormula.weight,
    nonemptyBudgetExpr, eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

/-- `StoredNextProblem.budget z⁶` with `2^(3z)` as `var 1` and `2^((3z+1)z)` as `var 2`. -/
def nextBudgetExpr : Expr :=
  let X : Expr := .var 0
  let Y : Expr := .var 1
  let W : Expr := .var 2
  7 + (8 + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))) + (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X)))))))) + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))))))) + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X) + (2 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (8 + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))) + (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X)))))))) + 2 * (1 + (2 + (X + 1) ^ 2 + X * (1 + (1 + X + (1 + (2 + (X + 1) ^ 2 + X * (1 + (2 + X + (3 + 2 * 1 + X * (2 + 1)) * X)))))))) + (3 + 2 * (1 + 1) + X * (2 + (1 + 1))) * X))))) + (4 + X * (2 + (4 + 1644 * (X + X + X + 1) ^ 5 + 953 * (3 * X + Y + (6 + X + X * (8 + 2 * X)) + X + 1) ^ 6 + 141 * (X * W + Y + 2) ^ 6)) + 604 * (X * W + 1) ^ 4) + (3 + (2 + (X + 1) ^ 2 + X * (2 + (2 + (1 + (X + 1) ^ 2 + (1 + X * (2 + (1 + X * (2 + (1 + X * (2 + (1 + X * 6) + X)) + X ^ 2)) + X ^ 3))) + 2 * X ^ 4 * 9) + 2 * X ^ 4)) + X * (2 * X ^ 4)) + (2 + (2 + (X * (2 * X ^ 4) + 1) ^ 2 + X * (2 * X ^ 4) * (1 + (2 + X * (2 * X ^ 4) + 614 * (X + 1) ^ 3))))
theorem nextBudget_diag (z : Nat) :
    StoredNextProblem.budget z z z z z z = eval ![z,2^(3*z),2^((3*z+1)*z),0] nextBudgetExpr := by
  simp only [StoredNextProblem.budget, StoredRowTransport.budget, StoredRowTransport.vectorBudget, StoredRowTransport.matrixBudget,
    StoredFamilyTransport.budget, StoredCleanupBound.stepUpper, StoredEmptyTailGuards.sizeBudget, StoredEmptyTailGuards.switchSize,
    StoredBranchEnumeration.branchBudget, StoredBranchEnumeration.branchOfBudget, StoredBranchEnumeration.endpointBudget,
    StoredBranchEnumeration.b4, StoredBranchEnumeration.b3, StoredBranchEnumeration.b2, StoredBranchEnumeration.b1,
    StoredNextProblem.familyBudget, StoredNextProblem.familyEntryCost, StoredForwardTableBuild.tabBudget,
    StoredRelationalFormula.weight, nextBudgetExpr, eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]

def disjBudgetExpr : Expr :=
  let K : Expr := .var 0
  let a : Expr := .var 1
  let b : Expr := .var 2
  a+7+(3+2*2+K*(2+2))*a+(3+2*(a+3)+K*(2+(a+3)))*b
theorem disjBudget_eval (K a b : Nat) : disjBudget K a b = eval ![K,a,b,0] disjBudgetExpr := by
  simp only [disjBudget, StoredRelationalFormula.weight, disjBudgetExpr, eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### Level-3 bounds of the pieces -/

theorem tower2_double (x : Nat) : 2*tower 2 x ≤ tower 2 (x+1) := TowerExpression.double_step 1 x
theorem tower2_square (x : Nat) : tower 2 x*tower 2 x ≤ tower 2 (x+1) := TowerExpression.square_step 2 x (by decide)

theorem tower3_mul_small (x n : Nat) (hn : n ≤ 16) : n*tower 3 x ≤ tower 3 (x+4) := by
  have h1 := tower3_quad x
  have h2 := tower3_quad (x+2)
  have e : x+2+2 = x+4 := rfl
  rw [e] at h2
  have := Nat.mul_le_mul_right (tower 3 x) hn
  omega

set_option maxHeartbeats 4000000 in
theorem blockBudget_tower (n q T B K y : Nat) (hn : n ≤ tower 3 y) (hq : q ≤ tower 3 y) (hT : T ≤ tower 3 y)
    (hB : B ≤ tower 3 y) (hK : K ≤ tower 3 y) :
    StoredBlockArrayPackage.budget n q T B K ≤ tower 3 (y+4+weight blockBudgetExpr) := by
  have e0 : n ≤ (n+q+T+B+K) := by omega
  have e1 : q ≤ (n+q+T+B+K) := by omega
  have e2 : T ≤ (n+q+T+B+K) := by omega
  have e3 : B ≤ (n+q+T+B+K) := by omega
  have e4 : K ≤ (n+q+T+B+K) := by omega
  have h := blockBudget_mono e0 e1 e2 e3 e4
  rw [blockBudget_diag] at h
  refine h.trans (envelope_three blockBudgetExpr ![(n+q+T+B+K),0,0,0] (y+4) ?_)
  intro i; fin_cases i
  · show (n+q+T+B+K) ≤ tower 3 (y+4)
    have := tower3_mul_small y 5 (by omega)
    omega
  all_goals exact Nat.zero_le _

set_option maxHeartbeats 4000000 in
theorem costGT_tower (k N c q F E e2 e3 T P Q B K y : Nat) (hk : k ≤ tower 3 y) (hN : N ≤ tower 3 y)
    (hc : c ≤ tower 3 y) (hq : q ≤ tower 3 y) (hF : F ≤ tower 3 y) (hE : E ≤ tower 3 y) (h2 : e2 ≤ tower 3 y)
    (h3 : e3 ≤ tower 3 y) (hT : T ≤ tower 3 y) (hP : P ≤ tower 3 y) (hQ : Q ≤ tower 3 y) (hB : B ≤ tower 3 y)
    (hK : K ≤ tower 3 y) :
    costGT k N c q F E e2 e3 T P Q B K ≤ tower 3 (y+4+weight costExpr) := by
  have hh0 : k ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh1 : N ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh2 : c ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh3 : q ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh4 : F ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh5 : E ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh6 : e2 ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh7 : e3 ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh8 : T ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh9 : P ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh10 : Q ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh11 : B ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have hh12 : K ≤ (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) := by omega
  have h := costGT_mono hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hh8 hh9 hh10 hh11 hh12
  rw [costGT_diag] at h
  refine h.trans (envelope_three costExpr ![(k+N+c+q+F+E+e2+e3+T+P+Q+B+K),0,0,0] (y+4) ?_)
  intro i; fin_cases i
  · show (k+N+c+q+F+E+e2+e3+T+P+Q+B+K) ≤ tower 3 (y+4)
    have := tower3_mul_small y 13 (by omega)
    omega
  all_goals exact Nat.zero_le _

theorem three_pow_tower' (E y : Nat) (hE : E ≤ tower 2 y) : 3^E ≤ tower 3 (y+1) := three_pow_tower E y hE
theorem nine_pow_tower (E y : Nat) (hE : E ≤ tower 2 y) : 9^E ≤ tower 3 (y+2) := by
  have h1 : 9^E ≤ 2^(4*E) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) E
  have h2 : 4*E ≤ tower 2 (y+2) := by
    have h1 : 2*tower 2 y ≤ tower 2 (y+1) := tower2_double y
    have h2 : 2*tower 2 (y+1) ≤ tower 2 (y+2) := tower2_double (y+1)
    omega
  exact h1.trans (exp_mono h2)

/-- The lowering cost of one step, with the recursive size `s ≤ tower 3 y`. -/
theorem costEnv_tower (k N cl s L K x y : Nat) (hx : x+weight exponentExpr+1 ≤ y)
    (hk : k ≤ tower 2 x) (hN : N ≤ tower 2 x) (hcl : cl ≤ tower 2 x) (hL : L ≤ tower 2 x) (hK : K ≤ tower 2 x)
    (hs : s ≤ tower 3 y) :
    costEnv k (N+cl) cl s s L K ≤
      tower 3 (y+3+max (weight blockSizeExpr) (weight blockBudgetExpr)+5+4+weight costExpr) := by
  have hxy : x ≤ y := by omega
  have l2 : ∀ a, a ≤ tower 2 x → a ≤ tower 3 y := fun a ha => tower3_of_tower2 (ha.trans (tower_mono 2 hxy))
  have hN' : N+cl ≤ tower 2 (x+1) := by
    have := tower2_double x; omega
  have hE : exponentEnv k (N+cl) cl ≤ tower 2 y :=
    (exponentEnv_tower k (N+cl) cl (x+1) (hk.trans (tower_mono 2 (Nat.le_succ x))) hN'
      (hcl.trans (tower_mono 2 (Nat.le_succ x)))).trans (tower_mono 2 (by omega))
  have hT := length_tower s _ y hs hE
  have hW1 : weight blockSizeExpr ≤ max (weight blockSizeExpr) (weight blockBudgetExpr) := le_max_left _ _
  have hW2 : weight blockBudgetExpr ≤ max (weight blockSizeExpr) (weight blockBudgetExpr) := le_max_right _ _
  have hy3 : ∀ a, a ≤ tower 3 y → a ≤ tower 3 (y+3) := fun a ha => ha.trans (tower3_mono (by omega))
  have hbs := blockSize_tower (N+cl) _ L (y+3) (hy3 _ (tower3_of_tower2 (hN'.trans (tower_mono 2 (by omega))))) hT
    (hy3 _ (l2 L hL))
  have hbb := blockBudget_tower (N+cl) s _ L K (y+3) (hy3 _ (tower3_of_tower2 (hN'.trans (tower_mono 2 (by omega)))))
    (hy3 _ hs) hT (hy3 _ (l2 L hL)) (hy3 _ (l2 K hK))
  have hP : k*StoredBlockArrayPackage.sizeBudget (N+cl) ((s*s+1)*2^exponentEnv k (N+cl) cl) L ≤
      tower 3 (y+3+(max (weight blockSizeExpr) (weight blockBudgetExpr))+5) := by
    have hk3 : k ≤ tower 3 (y+3+(max (weight blockSizeExpr) (weight blockBudgetExpr))+4) := (l2 k hk).trans (tower3_mono (by omega))
    exact (Nat.mul_le_mul hk3 (hbs.trans (tower3_mono (by omega)))).trans (tower3_square _)
  have hQ : k*StoredBlockArrayPackage.budget (N+cl) s ((s*s+1)*2^exponentEnv k (N+cl) cl) L K ≤
      tower 3 (y+3+(max (weight blockSizeExpr) (weight blockBudgetExpr))+5) := by
    have hk3 : k ≤ tower 3 (y+3+(max (weight blockSizeExpr) (weight blockBudgetExpr))+4) := (l2 k hk).trans (tower3_mono (by omega))
    exact (Nat.mul_le_mul hk3 (hbb.trans (tower3_mono (by omega)))).trans (tower3_square _)
  unfold costEnv
  simp only []
  rw [costG_eq]
  have up : ∀ a, a ≤ tower 3 y → a ≤ tower 3 (y+3+(max (weight blockSizeExpr) (weight blockBudgetExpr))+5) := fun a ha => ha.trans (tower3_mono (by omega))
  apply costGT_tower
  · exact up _ (l2 k hk)
  · exact up _ (tower3_of_tower2 (hN'.trans (tower_mono 2 (by omega))))
  · exact up _ (l2 cl hcl)
  · exact up _ hs
  · exact up _ hs
  · exact up _ (tower3_of_tower2 hE)
  · exact up _ (exp_tower2_le _ y hE)
  · exact (three_pow_tower' _ y hE).trans (tower3_mono (by omega))
  · exact hT.trans (tower3_mono (by omega))
  · exact hP
  · exact hQ
  · exact up _ (l2 L hL)
  · exact up _ (l2 K hK)

theorem seedBudget_tower (c F K x : Nat) (hc : c ≤ tower 2 x) (hF : F ≤ tower 2 x) (hK : K ≤ tower 2 x) :
    StoredRelationalNonempty.seedBudget c F K ≤ tower 2 (x+2+weight seedBudgetExpr) := by
  have e0 : c ≤ (c+F+K) := by omega
  have e1 : F ≤ (c+F+K) := by omega
  have e2 : K ≤ (c+F+K) := by omega
  have h := seedBudget_mono e0 e1 e2
  rw [seedBudget_diag] at h
  refine h.trans (eval_tower seedBudgetExpr ![(c+F+K),0,0,0] (x+2) ?_)
  intro i; fin_cases i
  · show (c+F+K) ≤ tower 2 (x+2)
    have h1 : 2*tower 2 x ≤ tower 2 (x+1) := tower2_double x
    have h2 : 2*tower 2 (x+1) ≤ tower 2 (x+2) := tower2_double (x+1)
    omega
  all_goals exact Nat.zero_le _

theorem nonemptyBudget_tower (c F K x : Nat) (hc : c ≤ tower 2 x) (hF : F ≤ tower 2 x) (hK : K ≤ tower 2 x) :
    StoredRelationalNonempty.nonemptyBudget c F K ≤ tower 3 (x+4+weight nonemptyBudgetExpr) := by
  have e0 : c ≤ (c+F+K) := by omega
  have e1 : F ≤ (c+F+K) := by omega
  have e2 : K ≤ (c+F+K) := by omega
  have h := nonemptyBudget_mono e0 e1 e2
  rw [nonemptyBudget_diag] at h
  have hZ : (c+F+K) ≤ tower 2 (x+2) := by
    have h1 : 2*tower 2 x ≤ tower 2 (x+1) := tower2_double x
    have h2 : 2*tower 2 (x+1) ≤ tower 2 (x+2) := tower2_double (x+1)
    omega
  refine h.trans (envelope_three nonemptyBudgetExpr ![(c+F+K),3^(c+F+K),9^(c+F+K),0] (x+4) ?_)
  intro i; fin_cases i
  · exact tower3_of_tower2 (hZ.trans (tower_mono 2 (by omega)))
  · exact (three_pow_tower' (c+F+K) (x+2) hZ).trans (tower3_mono (by omega))
  · exact nine_pow_tower (c+F+K) (x+2) hZ
  · exact Nat.zero_le _

theorem nextBudget_tower (k N c F B K x : Nat) (hk : k ≤ tower 2 x) (hN : N ≤ tower 2 x) (hc : c ≤ tower 2 x)
    (hF : F ≤ tower 2 x) (hB : B ≤ tower 2 x) (hK : K ≤ tower 2 x) :
    StoredNextProblem.budget k N c F B K ≤ tower 3 (x+6+weight nextBudgetExpr) := by
  have e0 : k ≤ (k+N+c+F+B+K) := by omega
  have e1 : N ≤ (k+N+c+F+B+K) := by omega
  have e2 : c ≤ (k+N+c+F+B+K) := by omega
  have e3 : F ≤ (k+N+c+F+B+K) := by omega
  have e4 : B ≤ (k+N+c+F+B+K) := by omega
  have e5 : K ≤ (k+N+c+F+B+K) := by omega
  have h := nextBudget_mono e0 e1 e2 e3 e4 e5
  rw [nextBudget_diag] at h
  have hZ : (k+N+c+F+B+K) ≤ tower 2 (x+3) := by
    have h1 : 2*tower 2 x ≤ tower 2 (x+1) := tower2_double x
    have h2 : 2*tower 2 (x+1) ≤ tower 2 (x+2) := tower2_double (x+1)
    have h3 : 2*tower 2 (x+2) ≤ tower 2 (x+3) := tower2_double (x+2)
    omega
  have h3Z : 3*(k+N+c+F+B+K) ≤ tower 2 (x+5) := by
    have h1 : 2*tower 2 (x+3) ≤ tower 2 (x+4) := tower2_double (x+3)
    have h2 : 2*tower 2 (x+4) ≤ tower 2 (x+5) := tower2_double (x+4)
    have := tower_mono 2 (show x+3 ≤ x+5 by omega)
    omega
  have hZZ : (3*(k+N+c+F+B+K)+1)*(k+N+c+F+B+K) ≤ tower 2 (x+6) := by
    have hsq : (k+N+c+F+B+K)*(k+N+c+F+B+K) ≤ tower 2 (x+4) := (Nat.mul_le_mul hZ hZ).trans (tower2_square (x+3))
    have h1 : 2*tower 2 (x+4) ≤ tower 2 (x+5) := tower2_double (x+4)
    have h2 : 2*tower 2 (x+5) ≤ tower 2 (x+6) := tower2_double (x+5)
    have hZ1 : (k+N+c+F+B+K) ≤ tower 2 (x+4) := hZ.trans (tower_mono 2 (by omega))
    have : (3*(k+N+c+F+B+K)+1)*(k+N+c+F+B+K) = 3*((k+N+c+F+B+K)*(k+N+c+F+B+K))+(k+N+c+F+B+K) := by ring
    omega
  refine h.trans (envelope_three nextBudgetExpr ![(k+N+c+F+B+K),2^(3*(k+N+c+F+B+K)),2^((3*(k+N+c+F+B+K)+1)*(k+N+c+F+B+K)),0] (x+6) ?_)
  intro i; fin_cases i
  · exact tower3_of_tower2 (hZ.trans (tower_mono 2 (by omega)))
  · exact (exp_tower2_le _ _ h3Z).trans (tower3_mono (by omega))
  · exact exp_tower2_le _ _ hZZ
  · exact Nat.zero_le _

theorem disjBudget_tower (K a b y : Nat) (hK : K ≤ tower 3 y) (ha : a ≤ tower 3 y) (hb : b ≤ tower 3 y) :
    disjBudget K a b ≤ tower 3 (y+weight disjBudgetExpr) := by
  rw [disjBudget_eval]
  apply envelope_three
  intro i; fin_cases i
  · exact hK
  · exact ha
  · exact hb
  · exact Nat.zero_le _

/-! ### The size envelope, standalone (as used inside `sizeStep_tower`) -/

theorem sizeEnv_tower (k N cl s L x y : Nat) (hx : x+weight exponentExpr ≤ y)
    (hk : k ≤ tower 2 x) (hN : N ≤ tower 2 x) (hcl : cl ≤ tower 2 x) (hL : L ≤ tower 2 x) (hs : s ≤ tower 3 y) :
    sizeEnv k N cl s L s ≤ tower 3 (y+3+weight blockSizeExpr+1+weight sizeExpr) := by
  have hxy : x ≤ y := by omega
  have l2 : ∀ a, a ≤ tower 2 x → a ≤ tower 3 y := fun a ha => tower3_of_tower2 (ha.trans (tower_mono 2 hxy))
  have hE : exponentEnv k N cl ≤ tower 2 y := (exponentEnv_tower k N cl x hk hN hcl).trans (tower_mono 2 hx)
  have hT := length_tower s _ y hs hE
  have hb := blockSize_tower N _ L (y+3) ((l2 N hN).trans (tower3_mono (by omega))) hT
    ((l2 L hL).trans (tower3_mono (by omega)))
  have hP : k*StoredBlockArrayPackage.sizeBudget N ((s*s+1)*2^exponentEnv k N cl) L ≤
      tower 3 (y+3+weight blockSizeExpr+1) := by
    have hk3 : k ≤ tower 3 (y+3+weight blockSizeExpr) := (l2 k hk).trans (tower3_mono (by omega))
    exact (Nat.mul_le_mul hk3 hb).trans (tower3_square _)
  unfold sizeEnv
  rw [sizeG_eq]
  apply sizeGT_tower
  · exact hs.trans (tower3_mono (by omega))
  · exact hs.trans (tower3_mono (by omega))
  · exact hT.trans (tower3_mono (by omega))
  · exact hP
  · exact (l2 L hL).trans (tower3_mono (by omega))
  · exact (l2 cl hcl).trans (tower3_mono (by omega))

/-! ### One step of the cost recursion -/

def costStepArg := max (3+max (weight blockSizeExpr) (weight blockBudgetExpr)+5+4+weight costExpr)
  (3+weight blockSizeExpr+1+weight sizeExpr+weight disjBudgetExpr)
def costStepWeight := costStepArg+3
/-- What the tower argument must exceed the level-2 argument `x` by. -/
def costGap := max (max (2+weight seedBudgetExpr) (6+weight nextBudgetExpr))
  (max (max (weight seedExpr) (weight exponentExpr+1)) (max (4+weight nonemptyBudgetExpr) (1+weight nonemptyExpr)))

theorem tower3_eight (x : Nat) : 8*tower 3 x ≤ tower 3 (x+3) := by
  have h1 := tower3_quad x
  have h2 := tower3_double (x+2)
  have e : x+2+1 = x+3 := rfl
  rw [e] at h2
  omega

theorem costStep_tower (k N c cl F Bn L K x y s : Nat) (hx : x+costGap ≤ y)
    (hk : k ≤ tower 2 x) (hN : N ≤ tower 2 x) (hc : c ≤ tower 2 x) (hcl : cl ≤ tower 2 x)
    (hF : F ≤ tower 2 x) (hBn : Bn ≤ tower 2 x) (hL : L ≤ tower 2 x) (hK : K ≤ tower 2 x) (hs : s ≤ tower 3 y) :
    stepEnv k N c cl F Bn L K s ≤ tower 3 (y+costStepWeight) := by
  have hg : x+max (max (2+weight seedBudgetExpr) (6+weight nextBudgetExpr))
      (max (max (weight seedExpr) (weight exponentExpr+1)) (max (4+weight nonemptyBudgetExpr) (1+weight nonemptyExpr))) ≤ y := hx
  have g1 : x+2+weight seedBudgetExpr ≤ y := by omega
  have g2 : x+6+weight nextBudgetExpr ≤ y := by omega
  have g3 : x+weight seedExpr ≤ y := by omega
  have g4 : x+weight exponentExpr+1 ≤ y := by omega
  have hxy : x ≤ y := by omega
  have l2 : ∀ a, a ≤ tower 2 x → a ≤ tower 3 y := fun a ha => tower3_of_tower2 (ha.trans (tower_mono 2 hxy))
  set A := costStepArg with hA
  have hA1 : 3+max (weight blockSizeExpr) (weight blockBudgetExpr)+5+4+weight costExpr ≤ A := le_max_left _ _
  have hA2 : 3+weight blockSizeExpr+1+weight sizeExpr+weight disjBudgetExpr ≤ A := le_max_right _ _
  -- the five terms
  have t1 : StoredRelationalNonempty.seedBudget c F K ≤ tower 3 (y+A) :=
    (tower3_of_tower2 ((seedBudget_tower c F K x hc hF hK).trans (tower_mono 2 g1))).trans (tower3_mono (by omega))
  have t2 : StoredNextProblem.budget k N c F Bn K ≤ tower 3 (y+A) :=
    (nextBudget_tower k N c F Bn K x hk hN hc hF hBn hK).trans (tower3_mono (by omega))
  have t3 : costEnv k (N+cl) cl s s L K ≤ tower 3 (y+A) :=
    (costEnv_tower k N cl s L K x y g4 hk hN hcl hL hK hs).trans (tower3_mono (by omega))
  have hseed : seedSize c F ≤ tower 3 y := by
    rw [seedSize_eval]
    refine tower3_of_tower2 ((eval_tower _ ![c,F,0,0] x ?_).trans (tower_mono 2 g3))
    intro i; fin_cases i
    · exact hc
    · exact hF
    all_goals exact Nat.zero_le _
  have hsz := sizeEnv_tower k N cl s L x y (by omega) hk hN hcl hL hs
  have t4 : disjBudget K (seedSize c F) (sizeEnv k N cl s L s) ≤ tower 3 (y+A) := by
    refine (disjBudget_tower K _ _ (y+3+weight blockSizeExpr+1+weight sizeExpr)
      ((l2 K hK).trans (tower3_mono (by omega))) (hseed.trans (tower3_mono (by omega))) hsz).trans
      (tower3_mono (by omega))
  have t0 : 4 ≤ tower 3 (y+A) := (show 4 ≤ tower 3 0 by decide).trans (tower3_mono (by omega))
  have h8 := tower3_eight (y+A)
  have hm : tower 3 (y+A+3) ≤ tower 3 (y+costStepWeight) := tower3_mono (by unfold costStepWeight; omega)
  unfold stepEnv
  omega

/-! ### The recursion -/

def costBase (x : Nat) := x+max (baseGap+1+weight nonemptyExpr) costGap

theorem costRec_tower (k N c cl F Bn L K x : Nat) (sz : Nat → Nat) (hk : k ≤ tower 2 x) (hN : N ≤ tower 2 x)
    (hc : c ≤ tower 2 x) (hcl : cl ≤ tower 2 x) (hF : F ≤ tower 2 x) (hBn : Bn ≤ tower 2 x) (hL : L ≤ tower 2 x)
    (hK : K ≤ tower 2 x) (hsz : ∀ h, sz h ≤ tower 3 (baseArg x+stepWeight*(h+1))) :
    ∀ h, costRec k N c cl F Bn L K sz h ≤ tower 3 (costBase x+stepWeight*(h+1)+costStepWeight+1+h) := by
  intro h
  have hgap : x+costGap ≤ costBase x := by unfold costBase; omega
  have hgap' : x+baseGap+1+weight nonemptyExpr ≤ costBase x := by unfold costBase; omega
  induction h with
  | zero =>
    have hb : nonemptySize c F ≤ tower 3 (costBase x+stepWeight*(0+1)) :=
      (nonemptySize_tower c F x hc hF).trans (tower3_mono (by omega))
    have hs := costStep_tower k N c cl F Bn L K x (costBase x+stepWeight*(0+1)) (nonemptySize c F)
      (by omega) hk hN hc hcl hF hBn hL hK hb
    have hne : StoredRelationalNonempty.nonemptyBudget c F K ≤ tower 3 (costBase x+stepWeight*(0+1)+costStepWeight) := by
      refine (nonemptyBudget_tower c F K x hc hF hK).trans (tower3_mono ?_)
      have : 4+weight nonemptyBudgetExpr ≤ costGap := by
        unfold costGap; omega
      omega
    have hd := tower3_double (costBase x+stepWeight*(0+1)+costStepWeight)
    simp only [costRec, Nat.add_zero]
    omega
  | succ h ih =>
    have hy : baseArg x+stepWeight*(h+1) ≤ costBase x+stepWeight*(h+1) := by unfold costBase baseArg; omega
    have hs := costStep_tower k N c cl F Bn L K x (costBase x+stepWeight*(h+1)) (sz h)
      (by omega) hk hN hc hcl hF hBn hL hK ((hsz h).trans (tower3_mono hy))
    have hm1 : tower 3 (costBase x+stepWeight*(h+1)+costStepWeight) ≤
        tower 3 (costBase x+stepWeight*(h+1)+costStepWeight+1+h) := tower3_mono (by omega)
    have hd := tower3_double (costBase x+stepWeight*(h+1)+costStepWeight+1+h)
    have hm2 : tower 3 (costBase x+stepWeight*(h+1)+costStepWeight+1+h+1) ≤
        tower 3 (costBase x+stepWeight*(h+1+1)+costStepWeight+1+(h+1)) := tower3_mono (by ring_nf; omega)
    simp only [costRec]
    omega

theorem costAt_tower (M k N c F B K H : Nat) (hk : k ≤ M) (hN : N ≤ M) (hc : c ≤ M) (hF : F ≤ M)
    (hB : B ≤ M) (hK : K ≤ M) (hH : H ≤ M) (h : Nat) :
    costAt k N c F B K H h ≤
      tower 3 (costBase (liftedExp M)+stepWeight*(h+1)+costStepWeight+1+h) := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := horizon_le M k N c F B H hk hN hc hF hB hH
  have hB9 : max B 9 ≤ tower 2 (liftedExp M) := by
    apply max_le
    · exact hB.trans (le_tower2 M _ (by unfold liftedExp liftedBase; omega))
    · exact le_tower2 9 _ (by unfold liftedExp liftedBase; omega)
  have hK2 : max K 2 ≤ tower 2 (liftedExp M) := by
    apply max_le
    · exact hK.trans (le_tower2 M _ (by unfold liftedExp liftedBase; omega))
    · exact le_tower2 2 _ (by unfold liftedExp liftedBase; omega)
  exact costRec_tower _ _ _ _ _ _ _ _ (liftedExp M) _ h1 h2 h3 h4 h5 hB9 h6 hK2
    (fun r => sizeRec_tower _ _ _ _ _ _ (liftedExp M) h1 h2 h3 h4 h5 h6 r) h

/-- The counted cost of the stored recursion at rank `H`, from a stored
problem with all parameters and `H+1` at most `M`: a triple exponential in
`M` with an explicit argument polynomial in `M` and linear in `H`. -/
theorem solve_cost_tower (X : Packed) (k N c F B K M : Nat) (hb : Bounds X k N c F B K) (H : Nat)
    (hk : k ≤ M) (hN : N ≤ M) (hc : c ≤ M) (hF : F ≤ M) (hB : B ≤ M) (hK : K ≤ M) (hH : H+1 ≤ M) :
    (StoredRankSolve.solve H X.2.2).2 ≤
      tower 3 (costBase (liftedExp M)+stepWeight*(H+1)+costStepWeight+1+H) :=
  (solve_cost_initial X k N c F B K hb H).trans (costAt_tower M k N c F B K (H+1) hk hN hc hF hB hK hH H)

end NSSE.StoredRankCostTower
