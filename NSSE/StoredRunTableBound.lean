import NSSE.StoredRunTable

/-! Explicit bounds for the actual stored exact-run certificate constructor. -/
namespace NSSE.StoredRunTable
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
variable {R : Nat → Type} {P : Type} {n T : Nat}

structure LabelBound (f : QF R P × Nat) (c B K : Nat) : Prop where
  cost : f.2 ≤ c
  nodes : nodes f.1.formula ≤ B
  arity : arity f.1.formula ≤ K
structure Bounds (I F : Vertex R P n) (S : Step R P n) (T c B K : Nat) : Prop where
  initial : ∀ q, LabelBound (I q) c B K
  final : ∀ q, LabelBound (F q) c B K
  step : ∀ t < T, ∀ r q, LabelBound (S t r q) c B K

def anyBudget (m c : Nat) := 2+StoredForwardTableBuild.tabBudget m c+4*m
theorem any_bound (m : Nat) (f : Fin m → Data R P 0 × Nat) (c : Nat) (h : ∀ i, (f i).2 ≤ c) :
    (any m f).2 ≤ anyBudget m c := by
  have ht := CountedFinEnumeration.tabulate_bound m f c h
  simp only [any,StoredArrayParameterAtoms.fold_cost,CountedFinEnumeration.tabulate_value,List.length_ofFn,
    anyBudget,StoredForwardTableBuild.tabBudget] at *
  omega

def bitBudget (n T : Nat) := 7+T*(n+2)+n
theorem bit_bound (one : P) (t : Fin (T+1)) (q : Fin n) : (bit (R := R) one t q).2 ≤ bitBudget n T := by
  have ht : t.val ≤ T := by omega
  have h := Nat.mul_le_mul_right (n+2) ht
  have hq := q.isLt
  simp only [bit,StoredArrayCoordinates.offset_cost,bitBudget]; omega
def liftBudget (c B K : Nat) := 1+c+weight K 1*B
theorem lift_bound (f : QF R P × Nat) (c B K : Nat) (h : LabelBound f c B K) :
    (lift f n T).2 ≤ liftBudget c B K := by
  have hr := rename_bound (fun p => ((Sum.inl p : Params P n T),1)) 1 K (fun _ => le_rfl) f.1.formula h.arity
  have hc := h.cost; have hn := h.nodes
  simp only [lift,liftBudget]; nlinarith

def cellBudget (n T c B K : Nat) := 7+bitBudget n T+liftBudget c B K
theorem initialCell_bound (I : Vertex R P n) (one : P) (q : Fin n) (c B K : Nat)
    (h : LabelBound (I q) c B K) :
    (initialCell I one T q).2 ≤ 3+cellBudget n T c B K := by
  have ha := bit_bound (R := R) one (0 : Fin (T+1)) q
  have hb := lift_bound (n := n) (T := T) (I q) c B K h
  simp only [initialCell,cellBudget]; omega
theorem incoming_bound (S : Step R P n) (one : P) (t : Fin T) (r q : Fin n) (c B K : Nat)
    (h : LabelBound (S t.val r q) c B K) :
    (incoming S one t r q).2 ≤ cellBudget n T c B K := by
  have ha := bit_bound (R := R) one t.castSucc r
  have hb := lift_bound (n := n) (T := T) (S t.val r q) c B K h
  simp only [incoming,cellBudget]; omega
def successorBudget (n T c B K : Nat) := 10+bitBudget n T+anyBudget n (cellBudget n T c B K)
theorem successor_bound (S : Step R P n) (one : P) (t : Fin T) (q : Fin n) (c B K : Nat)
    (h : ∀ r, LabelBound (S t.val r q) c B K) :
    (successor S one t q).2 ≤ successorBudget n T c B K := by
  have ha := bit_bound (R := R) one t.succ q
  have hb := any_bound n (fun r => incoming S one t r q) _ (fun r => incoming_bound S one t r q c B K (h r))
  simp only [successor,successorBudget]; omega
def matrixBudget (n T c B K : Nat) :=
  7+StoredArrayValidity.everyBudget n (3+cellBudget n T c B K)+
    StoredArrayValidity.everyBudget T (StoredArrayValidity.everyBudget n (successorBudget n T c B K))
theorem matrix_bound (I F : Vertex R P n) (S : Step R P n) (one : P) (c B K : Nat) (h : Bounds I F S T c B K) :
    (matrix I S one T).2 ≤ matrixBudget n T c B K := by
  have ha := StoredArrayValidity.every_bound n (initialCell I one T) _
    (fun q => initialCell_bound I one q c B K (h.initial q))
  have hb := StoredArrayValidity.every_bound T (fun t => StoredArrayValidity.every n (successor S one t)) _
    (fun t => StoredArrayValidity.every_bound n (successor S one t) _
      (fun q => successor_bound S one t q c B K (fun r => h.step t.val t.isLt r q)))
  simp only [matrix,matrixBudget]; omega

theorem finalCell_bound (F : Vertex R P n) (one : P) (q : Fin n) (c B K : Nat)
    (h : LabelBound (F q) c B K) : (finalCell F one T q).2 ≤ cellBudget n T c B K := by
  have ha := bit_bound (R := R) one (Fin.last T) q
  have hb := lift_bound (n := n) (T := T) (F q) c B K h
  simp only [finalCell,cellBudget]; omega
theorem output_bound (F : Vertex R P n) (one : P) (c B K : Nat) (h : ∀ q, LabelBound (F q) c B K) :
    (output F one T).2 ≤ anyBudget n (cellBudget n T c B K) :=
  any_bound n _ _ (fun q => finalCell_bound F one q c B K (h q))
def budget (n T c B K : Nat) := 13+n*(T+3)+matrixBudget n T c B K+anyBudget n (cellBudget n T c B K)
theorem package_bound (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) (c B K : Nat)
    (h : Bounds I F S T c B K) : (package I F S one T positive).2 ≤ budget n T c B K := by
  have hm := matrix_bound I F S one c B K h
  have ho := output_bound (T := T) F one c B K h.final
  simp only [package,body,CountedSupportRule.mul_cost,budget]
  nlinarith

def sizeBudget (n T B : Nat) :=
  19+n*(14+2*B)+T*(8+n*(16+2*n*(9+B)))+n*(9+B)+5*((T+1)*n)
theorem package_size (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) (c B K : Nat)
    (h : Bounds I F S T c B K) : StoredRelationalElimination.size (package I F S one T positive).1 ≤ sizeBudget n T B := by
  rw [StoredRelationalElimination.size_value,package_formula]
  apply ExactReachabilitySize.nodes_compile_le
  · intro q; rw [denote_nodes]; exact (h.initial q).nodes
  · intro q; rw [denote_nodes]; exact (h.final q).nodes
  · intro t ht r q; rw [denote_nodes]; exact (h.step t ht r q).nodes

theorem conj_arity_le (a b : Data R P 0) (K : Nat) (ha : arity a ≤ K) (hb : arity b ≤ K) :
    arity (StoredArrayEquality.conj a b) ≤ K := by
  simpa only [StoredArrayEquality.conj,arity,Nat.max_zero] using max_le ha hb
theorem iff_arity_le (a b : Data R P 0) (K : Nat) (ha : arity a ≤ K) (hb : arity b ≤ K) :
    arity (StoredArrayEquality.iff a b) ≤ K :=
  conj_arity_le _ _ K (max_le ha hb) (max_le hb ha)
theorem every_arity_le (m : Nat) (f : Fin m → Data R P 0 × Nat) (K : Nat) (h : ∀ i, arity (f i).1 ≤ K) :
    arity (StoredArrayValidity.every m f).1 ≤ K := by
  have hf (as : List (Data R P 0)) (hh : ∀ a ∈ as, arity a ≤ K) : arity (StoredArrayEquality.fold as).1 ≤ K := by
    induction as with
    | nil => exact Nat.zero_le K
    | cons a as ih => exact conj_arity_le _ _ K (hh a (by simp)) (ih (fun a ha => hh a (by simp [ha])))
  apply hf
  intro a ha
  rw [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at ha
  obtain ⟨i,rfl⟩ := ha
  exact h i
theorem any_arity_le (m : Nat) (f : Fin m → Data R P 0 × Nat) (K : Nat) (h : ∀ i, arity (f i).1 ≤ K) :
    arity (any m f).1 ≤ K := by
  have hf (as : List (Data R P 0)) (hh : ∀ a ∈ as, arity a ≤ K) : arity (StoredArrayParameterAtoms.fold as).1 ≤ K := by
    induction as with
    | nil => exact Nat.zero_le K
    | cons a as ih =>
      have ha := hh a (by simp)
      have ht := ih (fun a ha => hh a (by simp [ha]))
      simpa only [StoredArrayParameterAtoms.fold,arity,Nat.max_zero] using max_le ha ht
  apply hf
  intro a ha
  rw [CountedFinEnumeration.tabulate_value,List.mem_ofFn] at ha
  obtain ⟨i,rfl⟩ := ha
  exact h i

theorem lift_arity (f : QF R P × Nat) : arity (lift f n T).1 = arity f.1.formula := by
  simp only [lift,rename_arity]
theorem package_arity (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) (c B K : Nat)
    (h : Bounds I F S T c B K) : arity (package I F S one T positive).1.body ≤ K := by
  have hi (q : Fin n) : arity (initialCell I one T q).1 ≤ K :=
    iff_arity_le _ _ K (Nat.zero_le K) (by rw [lift_arity]; exact (h.initial q).arity)
  have hs (t : Fin T) (q : Fin n) : arity (successor S one t q).1 ≤ K := by
    apply iff_arity_le
    · exact Nat.zero_le K
    · apply any_arity_le
      intro r
      apply conj_arity_le
      · exact Nat.zero_le K
      · rw [lift_arity]
        exact (h.step t.val t.isLt r q).arity
  have hm : arity (matrix I S one T).1 ≤ K :=
    conj_arity_le _ _ K (every_arity_le n _ K hi) (every_arity_le T _ K (fun t => every_arity_le n _ K (hs t)))
  have ho : arity (output F one T).1 ≤ K := by
    apply any_arity_le
    intro q
    apply conj_arity_le
    · exact Nat.zero_le K
    · rw [lift_arity]
      exact (h.final q).arity
  dsimp only [package]
  rw [StoredRelationalPackages.assemble_value]
  dsimp only
  apply conj_arity_le _ _ K hm
  cases positive <;> simp only [Bool.false_eq_true,↓reduceIte,arity,Nat.max_zero]
  all_goals exact ho
theorem package_vars (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) :
    (package I F S one T positive).1.vars = (T+1)*n := by
  dsimp only [package]
  rw [StoredRelationalPackages.assemble_value]

def closed (I F : Vertex R P n) (S : Step R P n) (one : P) (T : Nat) (positive : Bool) : Data R P 0 × Nat :=
  let a := package I F S one T positive
  let b := StoredRelationalClosure.build a.1
  (b.1,1+a.2+b.2)
theorem closed_value (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) :
    denote (closed I F S one T positive).1 =
      ExactReachabilityTable.compile (fun q => denote (I q).1.formula) (fun q => denote (F q).1.formula)
        (fun t r q => denote (S t r q).1.formula) one T positive := by
  simp only [closed,StoredRelationalClosure.build_value,package_formula]
def closedBudget (n T c B K : Nat) := 3+budget n T c B K+(5+3*K)*sizeBudget n T B+6*((T+1)*n)
theorem closed_bound (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) (c B K : Nat)
    (h : Bounds I F S T c B K) : (closed I F S one T positive).2 ≤ closedBudget n T c B K := by
  have hp := package_bound I F S one positive c B K h
  have hs := package_size I F S one positive c B K h
  have hc := StoredRelationalClosure.build_bound (package I F S one T positive).1 K
    (package_arity I F S one positive c B K h)
  have hv := package_vars (T := T) I F S one positive
  unfold StoredRelationalElimination.size at hs
  simp only [closed,closedBudget]; nlinarith
theorem closed_nodes (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) (c B K : Nat)
    (h : Bounds I F S T c B K) : nodes (closed I F S one T positive).1 ≤ sizeBudget n T B := by
  simp only [closed,StoredRelationalClosure.build_nodes]
  exact package_size I F S one positive c B K h
theorem closedBudget_diagonal (u : Nat) :
    closedBudget u u u u u = 137+311*u+287*u^2+196*u^3+75*u^4+10*u^5 := by
  unfold closedBudget budget matrixBudget successorBudget cellBudget bitBudget liftBudget anyBudget
    sizeBudget StoredArrayValidity.everyBudget StoredForwardTableBuild.tabBudget weight
  ring
theorem closedBudget_polynomial (n T c B K : Nat) :
    closedBudget n T c B K ≤ 1016*(n+T+c+B+K+1)^5 := by
  let u := n+T+c+B+K+1
  have hn : n ≤ u := by dsimp [u]; omega
  have ht : T ≤ u := by dsimp [u]; omega
  have hc : c ≤ u := by dsimp [u]; omega
  have hb : B ≤ u := by dsimp [u]; omega
  have hk : K ≤ u := by dsimp [u]; omega
  have hu : 1 ≤ u := by dsimp [u]; omega
  have hm : closedBudget n T c B K ≤ closedBudget u u u u u := by
    unfold closedBudget budget matrixBudget successorBudget cellBudget bitBudget liftBudget anyBudget
      sizeBudget StoredArrayValidity.everyBudget StoredForwardTableBuild.tabBudget weight
    gcongr
  have hp (j : Nat) : u^j ≤ u^(j+1) := by
    simpa only [pow_succ,Nat.one_mul,Nat.mul_comm] using Nat.mul_le_mul_right (u^j) hu
  rw [closedBudget_diagonal] at hm
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  change closedBudget n T c B K ≤ 1016*u^5
  norm_num at h0 h1 h2 h3 h4
  linarith only [hm,h0,h1,h2,h3,h4]

theorem closed_polynomial (I F : Vertex R P n) (S : Step R P n) (one : P) (positive : Bool) (c B K : Nat)
    (h : Bounds I F S T c B K) : (closed I F S one T positive).2 ≤ 1016*(n+T+c+B+K+1)^5 :=
  (closed_bound I F S one positive c B K h).trans (closedBudget_polynomial n T c B K)
end NSSE.StoredRunTable
