import NSSE.StoredRankHorizonTower

/-! The tower height of the size recursion of the stored `solve`: the size
envelope is a polynomial in level-3 quantities (the witness length
`T = (q²+1)·2^E` with `E` at level 2), so one rank adds a constant to the
argument of `tower 3`; the whole recursion is `tower 3 (poly(M) + W·h)`.
This is the stored counterpart of `DirectRankFormulaTower`. -/
namespace NSSE.StoredRankSizeTower
open StoredRankHorizon StoredRankSolveBounds StoredRankSolveEnvelope StoredRankCostEnvelope
open StoredRankHorizonTower DirectRankStateTower DirectRankFormulaTower PolynomialTowerEnvelope

/-! ### Level bookkeeping -/

theorem tower3_of_tower2 {a x : Nat} (h : a ≤ tower 2 x) : a ≤ tower 3 x :=
  h.trans (TowerExpression.height_mono 2 3 x (by decide))
theorem tower3_mono {x y : Nat} (h : x ≤ y) : tower 3 x ≤ tower 3 y := tower_mono 3 h
theorem tower3_pos (x : Nat) : 1 ≤ tower 3 x := Nat.one_le_pow _ _ (by decide)
theorem tower3_double (x : Nat) : 2*tower 3 x ≤ tower 3 (x+1) := TowerExpression.double_step 2 x
theorem tower3_square (x : Nat) : tower 3 x*tower 3 x ≤ tower 3 (x+1) := TowerExpression.square_step 3 x (by decide)
theorem tower3_quad (x : Nat) : 4*tower 3 x ≤ tower 3 (x+2) := by
  have h1 := tower3_double x
  have h2 := tower3_double (x+1)
  have h3 : x+1+1 = x+2 := rfl
  rw [h3] at h2
  omega
theorem exp_tower2_le (E x : Nat) (h : E ≤ tower 2 x) : 2^E ≤ tower 3 x := exp_mono h

/-! ### The block-size polynomial as an expression -/

def blockSizeExpr : Expr :=
  let X : Expr := .var 0
  19 + 2 * X * X * (14 + 2 * (109 + 4 * (3 + (15 + 5 * (X + 3) + (29 + 4 * (X + 3) + (6 + (X + 3) + X * (4 + X * (24 + 4 * (X + 3))))))))) + X * (8 + 2 * X * X * (16 + 2 * (2 * X * X) * (9 + (109 + 4 * (3 + (15 + 5 * (X + 3) + (29 + 4 * (X + 3) + (6 + (X + 3) + X * (4 + X * (24 + 4 * (X + 3))))))))))) + 2 * X * X * (9 + (109 + 4 * (3 + (15 + 5 * (X + 3) + (29 + 4 * (X + 3) + (6 + (X + 3) + X * (4 + X * (24 + 4 * (X + 3))))))))) + 5 * ((X + 1) * (2 * X * X)) + (19 + 2 * X * X * (14 + 2 * (109 + 4 * (3 + (15 + 5 * X + (29 + 4 * X + (6 + X + X * (4 + X * (24 + 4 * X)))))))) + X * (8 + 2 * X * X * (16 + 2 * (2 * X * X) * (9 + (109 + 4 * (3 + (15 + 5 * X + (29 + 4 * X + (6 + X + X * (4 + X * (24 + 4 * X)))))))))) + 2 * X * X * (9 + (109 + 4 * (3 + (15 + 5 * X + (29 + 4 * X + (6 + X + X * (4 + X * (24 + 4 * X)))))))) + 5 * ((X + 1) * (2 * X * X))) + 5 + X + X * (8 + 2 * X)

set_option maxHeartbeats 4000000 in
theorem blockSize_diag (z : Nat) : StoredBlockArrayPackage.sizeBudget z z z = eval ![z,0,0,0] blockSizeExpr := by
  unfold StoredBlockArrayPackage.sizeBudget StoredGuardedArrayShape.sizeBudget StoredDynamicRun.labelSize
    StoredRawSkippedRun.nodeBudget StoredRunTable.sizeBudget StoredRawAutomaton.nodeBudget
    StoredRawTransition.sizeBudget StoredRawSwitchGuard.sizeBudget blockSizeExpr
  rfl

theorem blockSize_tower (n T B y : Nat) (hn : n ≤ tower 3 y) (hT : T ≤ tower 3 y) (hB : B ≤ tower 3 y) :
    StoredBlockArrayPackage.sizeBudget n T B ≤ tower 3 (y+weight blockSizeExpr) := by
  have hn' : n ≤ max n (max T B) := le_max_left _ _
  have hT' : T ≤ max n (max T B) := (le_max_left _ _).trans (le_max_right _ _)
  have hB' : B ≤ max n (max T B) := (le_max_right _ _).trans (le_max_right _ _)
  have h := blockSize_mono hn' hT' hB'
  rw [blockSize_diag] at h
  refine h.trans (envelope_three blockSizeExpr ![max n (max T B),0,0,0] y ?_)
  intro i; fin_cases i
  · exact max_le hn (max_le hT hB)
  all_goals exact Nat.zero_le _

/-! ### The lowering size with the witness length abstracted -/

def sizeGT (q F T P B c : Nat) :=
  5+(3+T*(8+8*q))+((8+24*T+(P+StoredBlockArrayPackage.sizeBudget c T B+5+10*T))+5)*F+
    5*((T+1)*q+(T+1)*q)+28

theorem sizeG_eq (q F E P B c : Nat) : sizeG q F E P B c = sizeGT q F ((q*q+1)*2^E) P B c := rfl

theorem sizeGT_mono {q q' F F' T T' P P' B B' c c' : Nat} (hq : q ≤ q') (hF : F ≤ F') (hT : T ≤ T')
    (hP : P ≤ P') (hB : B ≤ B') (hc : c ≤ c') : sizeGT q F T P B c ≤ sizeGT q' F' T' P' B' c' := by
  unfold sizeGT
  have := blockSize_mono hc hT hB
  gcongr

def sizeExpr : Expr :=
  let X : Expr := .var 0
  5+(3+X*(8+8*X))+((8+24*X+(X+blockSizeExpr+5+10*X))+5)*X+5*((X+1)*X+(X+1)*X)+28

theorem sizeGT_diag (z : Nat) : sizeGT z z z z z z = eval ![z,0,0,0] sizeExpr := by
  unfold sizeGT sizeExpr
  rw [blockSize_diag]
  simp only [eval, Matrix.cons_val_zero]

theorem sizeGT_tower (q F T P B c y : Nat) (hq : q ≤ tower 3 y) (hF : F ≤ tower 3 y) (hT : T ≤ tower 3 y)
    (hP : P ≤ tower 3 y) (hB : B ≤ tower 3 y) (hc : c ≤ tower 3 y) :
    sizeGT q F T P B c ≤ tower 3 (y+weight sizeExpr) := by
  let Z := max q (max F (max T (max P (max B c))))
  have hq' : q ≤ Z := le_max_left _ _
  have hF' : F ≤ Z := (le_max_left _ _).trans (le_max_right _ _)
  have hT' : T ≤ Z := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hP' : P ≤ Z := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hB' : B ≤ Z := ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hc' : c ≤ Z := ((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have h := sizeGT_mono hq' hF' hT' hP' hB' hc'
  rw [sizeGT_diag] at h
  refine h.trans (envelope_three sizeExpr ![Z,0,0,0] y ?_)
  intro i; fin_cases i
  · exact max_le hq (max_le hF (max_le hT (max_le hP (max_le hB hc))))
  all_goals exact Nat.zero_le _

/-! ### Level-2 quantities of one step -/

def rowExpExpr (v : Fin 4) : Expr := 2*(Expr.var v)^6+8*(Expr.var v)^8
def exponentExpr : Expr := 1+rowExpExpr 2+(Expr.var 0)*rowExpExpr 1

theorem exponentEnv_eval (k N cl : Nat) : exponentEnv k N cl = eval ![k,N,cl,0] exponentExpr := by
  unfold exponentEnv exponentExpr rowExpExpr UnifiedBlockWitnessBound.rowExponent
  simp only [eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

theorem exponentEnv_tower (k N cl x : Nat) (hk : k ≤ tower 2 x) (hN : N ≤ tower 2 x) (hcl : cl ≤ tower 2 x) :
    exponentEnv k N cl ≤ tower 2 (x+weight exponentExpr) := by
  rw [exponentEnv_eval]
  apply eval_tower
  intro i; fin_cases i
  · exact hk
  · exact hN
  · exact hcl
  · exact Nat.zero_le _

/-- The witness length at level 3. -/
theorem length_tower (q E y : Nat) (hq : q ≤ tower 3 y) (hE : E ≤ tower 2 y) :
    (q*q+1)*2^E ≤ tower 3 (y+3) := by
  have h2 := exp_tower2_le E y hE
  have hsq : q*q ≤ tower 3 (y+1) := (Nat.mul_le_mul hq hq).trans (tower3_square y)
  have hpos := tower3_pos (y+1)
  have h3 : q*q+1 ≤ tower 3 (y+2) := by
    have := tower3_double (y+1)
    have e : y+1+1 = y+2 := rfl
    rw [e] at this
    omega
  have h4 : tower 3 y ≤ tower 3 (y+2) := tower3_mono (by omega)
  calc (q*q+1)*2^E ≤ tower 3 (y+2)*tower 3 (y+2) := Nat.mul_le_mul h3 (h2.trans h4)
    _ ≤ tower 3 (y+3) := tower3_square (y+2)

/-! ### One step of the size recursion -/

def stepWeight := 3+weight blockSizeExpr+1+weight sizeExpr+2

def seedExpr : Expr := 1+(Expr.var 0)*(3+(1+(Expr.var 0)*(3+(10+((Expr.var 1)+5)+2*(Expr.var 1)))))
theorem seedSize_eval (c F : Nat) : seedSize c F = eval ![c,F,0,0] seedExpr := by
  unfold seedSize seedExpr
  simp only [eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The gap the tower argument must keep above the level-2 argument `x`. -/
def baseGap := weight exponentExpr+weight seedExpr

/-- If the recursive size is `≤ tower 3 y` and all level-2 constants are
`≤ tower 2 x` with `x + baseGap ≤ y`, one step stays within
`tower 3 (y + stepWeight)`. -/
theorem sizeStep_tower (k N c cl F L x y s : Nat) (hx : x+baseGap ≤ y)
    (hk : k ≤ tower 2 x) (hN : N ≤ tower 2 x) (hc : c ≤ tower 2 x) (hcl : cl ≤ tower 2 x)
    (hF : F ≤ tower 2 x) (hL : L ≤ tower 2 x) (hs : s ≤ tower 3 y) :
    3+seedSize c F+sizeEnv k N cl s L s ≤ tower 3 (y+stepWeight) := by
  have hxy : x ≤ y := by unfold baseGap at hx; omega
  have l2 : ∀ a, a ≤ tower 2 x → a ≤ tower 3 y := fun a ha =>
    tower3_of_tower2 (ha.trans (tower_mono 2 hxy))
  -- the exponent and the witness length
  have hE : exponentEnv k N cl ≤ tower 2 y :=
    (exponentEnv_tower k N cl x hk hN hcl).trans (tower_mono 2 (by unfold baseGap at hx; omega))
  have hT := length_tower s _ y hs hE
  -- the block-size sum
  have hb := blockSize_tower N _ L (y+3) ((l2 N hN).trans (tower3_mono (by omega))) hT
    ((l2 L hL).trans (tower3_mono (by omega)))
  have hP : k*StoredBlockArrayPackage.sizeBudget N ((s*s+1)*2^exponentEnv k N cl) L ≤
      tower 3 (y+3+weight blockSizeExpr+1) := by
    have hk3 : k ≤ tower 3 (y+3+weight blockSizeExpr) := (l2 k hk).trans (tower3_mono (by omega))
    exact (Nat.mul_le_mul hk3 hb).trans (tower3_square _)
  -- the lowering size
  have hsz : sizeEnv k N cl s L s ≤ tower 3 (y+3+weight blockSizeExpr+1+weight sizeExpr) := by
    unfold sizeEnv
    rw [sizeG_eq]
    apply sizeGT_tower
    · exact hs.trans (tower3_mono (by omega))
    · exact hs.trans (tower3_mono (by omega))
    · exact hT.trans (tower3_mono (by omega))
    · exact hP
    · exact (l2 L hL).trans (tower3_mono (by omega))
    · exact (l2 cl hcl).trans (tower3_mono (by omega))
  -- the seed size: a polynomial of level-2 quantities
  have hseed : seedSize c F ≤ tower 3 (y+3+weight blockSizeExpr+1+weight sizeExpr) := by
    rw [seedSize_eval]
    refine (eval_tower _ ![c,F,0,0] x ?_).trans ?_
    · intro i; fin_cases i
      · exact hc
      · exact hF
      all_goals exact Nat.zero_le _
    · exact tower3_of_tower2 (tower_mono 2 (by unfold baseGap at hx; omega))
  have h3 : 3 ≤ tower 3 (y+3+weight blockSizeExpr+1+weight sizeExpr) :=
    (show 3 ≤ tower 3 3 by decide).trans (tower3_mono (by omega))
  have hq := tower3_quad (y+3+weight blockSizeExpr+1+weight sizeExpr)
  have hm := tower3_mono (show y+3+weight blockSizeExpr+1+weight sizeExpr+2 ≤ y+stepWeight by unfold stepWeight; omega)
  omega

/-! ### The rank-0 package -/

def nonemptyExpr : Expr :=
  1+(Expr.var 0)*(3+(1+(Expr.var 0)*(3+(10+((Expr.var 1)+23)*(Expr.var 2)+2*(Expr.var 1)))))
theorem nonemptySize_eval (c F : Nat) : nonemptySize c F = eval ![c,F,3^c,0] nonemptyExpr := by
  unfold nonemptySize nonemptyExpr
  simp only [eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]

theorem three_pow_tower (c x : Nat) (hc : c ≤ tower 2 x) : 3^c ≤ tower 3 (x+1) := by
  have h1 : 3^c ≤ 2^(2*c) := by rw [pow_mul]; exact Nat.pow_le_pow_left (by decide) c
  have h2 : 2*c ≤ tower 2 (x+1) := (Nat.mul_le_mul_left 2 hc).trans (TowerExpression.double_step 1 x)
  exact h1.trans (exp_mono h2)

theorem nonemptySize_tower (c F x : Nat) (hc : c ≤ tower 2 x) (hF : F ≤ tower 2 x) :
    nonemptySize c F ≤ tower 3 (x+1+weight nonemptyExpr) := by
  rw [nonemptySize_eval]
  apply envelope_three
  intro i; fin_cases i
  · exact tower3_of_tower2 (hc.trans (tower_mono 2 (Nat.le_succ x)))
  · exact tower3_of_tower2 (hF.trans (tower_mono 2 (Nat.le_succ x)))
  · exact three_pow_tower c x hc
  · exact Nat.zero_le _

/-! ### The recursion -/

def baseArg (x : Nat) := x+baseGap+1+weight nonemptyExpr

theorem sizeRec_tower (k N c cl F L x : Nat) (hk : k ≤ tower 2 x) (hN : N ≤ tower 2 x) (hc : c ≤ tower 2 x)
    (hcl : cl ≤ tower 2 x) (hF : F ≤ tower 2 x) (hL : L ≤ tower 2 x) :
    ∀ h, sizeRec k N c cl F L h ≤ tower 3 (baseArg x+stepWeight*(h+1)) := by
  intro h
  induction h with
  | zero =>
    have hb := nonemptySize_tower c F x hc hF
    have := sizeStep_tower k N c cl F L x (baseArg x) (nonemptySize c F) (by unfold baseArg; omega)
      hk hN hc hcl hF hL (hb.trans (tower3_mono (by unfold baseArg; omega)))
    simpa only [sizeRec, Nat.zero_add, Nat.mul_one] using this
  | succ h ih =>
    have := sizeStep_tower k N c cl F L x (baseArg x+stepWeight*(h+1)) _ (by unfold baseArg; omega)
      hk hN hc hcl hF hL ih
    refine le_trans ?_ (this.trans (tower3_mono (by ring_nf; omega)))
    simp only [sizeRec]
    exact le_rfl

/-- All horizon envelopes of v1601 lie below `tower 2 (liftedExp M)`. -/
theorem horizon_le (M k N c F B H : Nat) (hk : k ≤ M) (hN : N ≤ M) (hc : c ≤ M) (hF : F ≤ M)
    (hB : B ≤ M) (hH : H ≤ M) :
    rowCount k N H ≤ tower 2 (liftedExp M) ∧ rowLimit N H ≤ tower 2 (liftedExp M) ∧
    candBound k N c H ≤ tower 2 (liftedExp M) ∧ cleanedBound k N c H ≤ tower 2 (liftedExp M) ∧
    candNodes k N c F H ≤ tower 2 (liftedExp M) ∧ liftedEnv k N c F B H ≤ tower 2 (liftedExp M) := by
  have e1 : countExp M ≤ liftedExp M := by
    simp only [liftedExp, liftedBase, nodesExp, candExp, stepExpExp, cleanedExp, countExp]; omega
  have e2 : 3*M+1 ≤ liftedExp M := by
    simp only [liftedExp, liftedBase, nodesExp, candExp, stepExpExp, cleanedExp, countExp]; omega
  have e3 : candExp M ≤ liftedExp M := by
    simp only [liftedExp, liftedBase, nodesExp, candExp, stepExpExp, cleanedExp, countExp]; omega
  have e4 : cleanedExp M ≤ liftedExp M := by
    simp only [liftedExp, liftedBase, nodesExp, candExp, stepExpExp, cleanedExp, countExp]; omega
  have e5 : nodesExp M ≤ liftedExp M := by
    simp only [liftedExp, liftedBase, nodesExp, candExp, stepExpExp, cleanedExp, countExp]; omega
  refine ⟨(rowCount_le M k N H hk hN hH).trans (exp_le_tower2 _ _ e1),
    (rowLimit_le M N H hN hH).trans (exp_le_tower2 _ _ e2),
    (candBound_le M k N c H hk hN hc hH).trans (tower_mono 2 e3),
    (cleanedBound_le M k N c H hk hN hc hH).trans (tower_mono 2 e4),
    (candNodes_le M k N c F H hk hN hc hF hH).trans (tower_mono 2 e5),
    liftedEnv_le M k N c F B H hk hN hc hF hB hH⟩

theorem sizeAt_tower (M k N c F B H : Nat) (hk : k ≤ M) (hN : N ≤ M) (hc : c ≤ M) (hF : F ≤ M)
    (hB : B ≤ M) (hH : H ≤ M) (h : Nat) :
    sizeAt k N c F B H h ≤ tower 3 (baseArg (liftedExp M)+stepWeight*(h+1)) := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := horizon_le M k N c F B H hk hN hc hF hB hH
  exact sizeRec_tower _ _ _ _ _ _ (liftedExp M) h1 h2 h3 h4 h5 h6 h

/-- The size of the stored recursion's output at rank `H`, from a stored
problem whose parameters are all at most `M ≥ H+1`: a triple exponential in
`M` with an explicit polynomial argument, linear in `H`. -/
theorem solve_size_tower (X : Packed) (k N c F B K M : Nat) (hb : Bounds X k N c F B K) (H : Nat)
    (hk : k ≤ M) (hN : N ≤ M) (hc : c ≤ M) (hF : F ≤ M) (hB : B ≤ M) (hH : H+1 ≤ M) :
    StoredRelationalElimination.size (StoredRankSolve.solve H X.2.2).1 ≤
      tower 3 (baseArg (liftedExp M)+stepWeight*(H+1)) :=
  (solve_size_initial X k N c F B K hb H).trans (sizeAt_tower M k N c F B (H+1) hk hN hc hF hB hH H)

end NSSE.StoredRankSizeTower
