import NSSE.StoredRankCostTower
import NSSE.StoredTerminalInput
import NSSE.StoredRelationalEvaluation

/-! The initial adapter and the closing evaluation.

The stored original rows of the cap front end (`StoredRankInput.Data`,
closed/unary table labels denoting formulas of `AlphabetTableRows.language
(Fin d)`) become a stored problem of the rank recursion over the *stored*
unary-table relation family `ExplicitUnaryTableLanguage.Rel` (one `List Bool`
per relation symbol, so relation evaluation is a counted lookup).  The
language homomorphism `toTab` interprets each table as the Boolean function
of the original language; it is an expansion of the original structure, so
avoidance transfers, and the packed-view argument connects the adapted
problem to `FiniteSOARankDecision.problem`.  Finally the stored recursion's
output package is closed, renamed and evaluated by the counted evaluator
`StoredRelationalEvaluation.decideFormula`. -/
namespace NSSE.StoredRankAdapter
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow
open StoredNextProblem StoredRankSolve StoredRankHorizon
open StoredEmptyTailCompiler (matrix matrix_read matrix_bound matrixBudget vectorBudget)
variable {d : Nat}

/-- The relation family of the original-input language. -/
abbrev Tab (d : Nat) : Nat → Type := fun n => (Fin n → Fin d) → Bool
/-- The stored unary-table family. -/
abbrev U : Nat → Type := ExplicitUnaryTableLanguage.Rel

theorem language_eq (d : Nat) :
    AlphabetTableRows.language (Fin d) = UniformWordLowering.wordLanguage (Tab d) := rfl
theorem unaryLanguage_eq : ExplicitUnaryTableLanguage.language = UniformWordLowering.wordLanguage U := rfl

/-- The original-input structure, seen through the relation family `Tab d`. -/
instance tabModel (d : Nat) : (UniformWordLowering.wordLanguage (Tab d)).Structure (Fin d) :=
  AlphabetTableRows.model (Fin d)
/-- The stored-table structure: each table is looked up. -/
instance uModel (d : Nat) : (UniformWordLowering.wordLanguage U).Structure (Fin d) :=
  ExplicitUnaryTableLanguage.model d

/-- Tables as Boolean functions. -/
def toTab (d : Nat) : UniformWordLowering.wordLanguage U →ᴸ UniformWordLowering.wordLanguage (Tab d) where
  onFunction := fun {_} f => nomatch f
  onRelation := fun {_} r => match r with
    | .unary bs => fun v => (StoredForwardLookup.get false bs (v 0).val).1

theorem get_eq_lookup (bs : List Bool) (i : Nat) :
    (StoredForwardLookup.get false bs i).1 = (ExplicitUnaryTableLanguage.lookup bs i).1 := by
  rw [StoredForwardLookup.get_value, ExplicitUnaryTableLanguage.lookup_value]

instance toTab_expansion (d : Nat) : (toTab d).IsExpansionOn (Fin d) where
  map_onFunction := fun {_} f _ => nomatch f
  map_onRelation := fun {_} r xs => by
    cases r with
    | unary bs =>
      show ((StoredForwardLookup.get false bs (xs 0).val).1 = true) = ((ExplicitUnaryTableLanguage.lookup bs (xs 0).val).1 = true)
      rw [get_eq_lookup]

/-! ### Label atoms -/

def truthData (P : Type) (b : Bool) : Data U P 0 := if b then .imp .falsum .falsum else .falsum

theorem truthData_map (P : Type) (b : Bool) :
    (toTab d).onFormula (denote (truthData P b)) = AlphabetTableRows.truth (α := Fin d) (P := P) b := by
  cases b <;> rfl
theorem truthData_qf (P : Type) (b : Bool) : (denote (truthData P b)).IsQF := by
  cases b
  · exact BoundedFormula.isQF_bot
  · exact BoundedFormula.IsQF.top
theorem truthData_nodes (P : Type) (b : Bool) : nodes (truthData P b) ≤ 3 := by
  cases b <;> simp [truthData, nodes]
theorem truthData_arity (P : Type) (b : Bool) : arity (truthData P b) = 0 := by
  cases b <;> simp [truthData, arity]

def closed (P : Type) (a : StoredClosedLabel.Atom) : QF U P × Nat :=
  match a with
  | .constant b => (⟨truthData P b,truthData_qf P b⟩,2)

theorem closed_map (P : Type) (a : StoredClosedLabel.Atom) :
    (toTab d).onFormula (denote (closed P a).1.formula) = StoredClosedLabel.denote (d := d) (P := P) a := by
  cases a; exact truthData_map _ _
theorem closed_bound (P : Type) (a : StoredClosedLabel.Atom) : (closed P a).2 ≤ 2 := by cases a; rfl
theorem closed_shape (P : Type) (a : StoredClosedLabel.Atom) :
    nodes (closed P a).1.formula ≤ 3 ∧ arity (closed P a).1.formula ≤ 1 := by
  cases a with
  | constant b =>
    refine ⟨truthData_nodes _ _,?_⟩
    simp only [closed]
    have := truthData_arity P b
    omega

def unary (a : StoredUnaryLabel.Atom) : QF U (Empty ⊕ Fin 1) × Nat :=
  match a with
  | .constant b => (⟨truthData (Empty ⊕ Fin 1) b,truthData_qf _ b⟩,2)
  | .unary xs => (⟨.rel (.unary xs) ⟨[.inl (.inr 0)],rfl⟩,BoundedFormula.IsAtomic.isQF (.rel _ _)⟩,3)

theorem unary_map (a : StoredUnaryLabel.Atom) :
    (toTab d).onFormula (denote (unary a).1.formula) = StoredUnaryLabel.denote (d := d) a := by
  cases a with
  | constant b => exact truthData_map _ _
  | unary xs =>
    change BoundedFormula.rel _ _ = BoundedFormula.rel _ _
    congr 1
    all_goals first | rfl | (funext i; fin_cases i; rfl)
theorem unary_bound (a : StoredUnaryLabel.Atom) : (unary a).2 ≤ 3 := by cases a <;> simp [unary]
theorem unary_shape (a : StoredUnaryLabel.Atom) :
    nodes (unary a).1.formula ≤ 3 ∧ arity (unary a).1.formula ≤ 1 := by
  cases a with
  | constant b =>
    refine ⟨truthData_nodes _ _,?_⟩
    simp only [unary]
    have := truthData_arity (Empty ⊕ Fin 1) b
    omega
  | unary xs => exact ⟨by simp [unary, nodes],by simp [unary, arity]⟩

/-! ### One row -/

def initial (A : StoredSymbolicRow.Data) (q : Fin A.count) : QF U Empty × Nat :=
  let g := StoredForwardLookup.get (.constant false) A.initial q.val
  let a := closed Empty g.1
  (a.1,1+g.2+a.2)
def final (A : StoredSymbolicRow.Data) (q : Fin A.count) : QF U Empty × Nat :=
  let g := StoredForwardLookup.get (.constant false) A.final q.val
  let a := closed Empty g.1
  (a.1,1+g.2+a.2)
def data (A : StoredSymbolicRow.Data) (q r : Fin A.count) : QF U (Empty ⊕ Fin 1) × Nat :=
  let g := StoredForwardLookup.get [] A.data q.val
  let h := StoredForwardLookup.get (.constant false) g.1 r.val
  let a := unary h.1
  (a.1,2+g.2+h.2+a.2)
def left (A : StoredSymbolicRow.Data) (q r : Fin A.count) : QF U Empty × Nat :=
  let g := StoredForwardLookup.get [] A.left q.val
  let h := StoredForwardLookup.get (.constant false) g.1 r.val
  let a := closed Empty h.1
  (a.1,2+g.2+h.2+a.2)
def right (A : StoredSymbolicRow.Data) (q r : Fin A.count) : QF U Empty × Nat :=
  let g := StoredForwardLookup.get [] A.right q.val
  let h := StoredForwardLookup.get (.constant false) g.1 r.val
  let a := closed Empty h.1
  (a.1,2+g.2+h.2+a.2)

def row (A : StoredSymbolicRow.Data) : Row U Empty A.count × Nat :=
  let i := StoredRelationTuple.tabulate (initial A)
  let f := StoredRelationTuple.tabulate (final A)
  let dd := matrix A.count (data A)
  let l := matrix A.count (left A)
  let r := matrix A.count (right A)
  let g := closed (Empty ⊕ Fin 2) A.guard
  (⟨i.1,f.1,dd.1,l.1,r.1,g.1⟩,7+i.2+f.2+dd.2+l.2+r.2+g.2)

/-- Interpreted through `toTab`, the adapted row is exactly the denoted stored row. -/
theorem row_map (A : StoredSymbolicRow.Data) :
    RowLanguageTransport.mapRow (toTab d) (row A).1.original = StoredSymbolicRow.denote (d := d) A := by
  unfold RowLanguageTransport.mapRow Row.original row StoredSymbolicRow.denote
  simp only [StoredRelationTuple.tabulate_read,matrix_read,initial,final,data,left,right,
    closed_map,unary_map]

theorem row_shape (A : StoredSymbolicRow.Data) : StoredRowTransport.Bounds (row A).1 3 1 := by
  constructor
  · constructor
    · intro q r; simpa only [row,matrix_read,data] using (unary_shape _).1
    · intro q r; simpa only [row,matrix_read,left] using (closed_shape Empty _).1
    · intro q r; simpa only [row,matrix_read,right] using (closed_shape Empty _).1
    · exact (closed_shape _ A.guard).1
    · intro q r; simpa only [row,matrix_read,data] using (unary_shape _).2
    · intro q r; simpa only [row,matrix_read,left] using (closed_shape Empty _).2
    · intro q r; simpa only [row,matrix_read,right] using (closed_shape Empty _).2
    · exact (closed_shape _ A.guard).2
  · intro q; simpa only [row,StoredRelationTuple.tabulate_read,initial] using (closed_shape Empty _).1
  · intro q; simpa only [row,StoredRelationTuple.tabulate_read,final] using (closed_shape Empty _).1
  · intro q; simpa only [row,StoredRelationTuple.tabulate_read,initial] using (closed_shape Empty _).2
  · intro q; simpa only [row,StoredRelationTuple.tabulate_read,final] using (closed_shape Empty _).2

def rowBudget (n : Nat) := 9+2*vectorBudget n (n+4)+3*matrixBudget n (2*n+7)
theorem row_bound (A : StoredSymbolicRow.Data) : (row A).2 ≤ rowBudget A.count := by
  have hi (q : Fin A.count) : (initial A q).2 ≤ A.count+4 := by
    have := StoredForwardLookup.get_bound (StoredClosedLabel.Atom.constant false) A.initial q.val
    have := closed_bound Empty (StoredForwardLookup.get (.constant false) A.initial q.val).1
    have := q.isLt; simp only [initial]; omega
  have hf (q : Fin A.count) : (final A q).2 ≤ A.count+4 := by
    have := StoredForwardLookup.get_bound (StoredClosedLabel.Atom.constant false) A.final q.val
    have := closed_bound Empty (StoredForwardLookup.get (.constant false) A.final q.val).1
    have := q.isLt; simp only [final]; omega
  have hd (q r : Fin A.count) : (data A q r).2 ≤ 2*A.count+7 := by
    have := StoredForwardLookup.get_bound ([] : List StoredUnaryLabel.Atom) A.data q.val
    have := StoredForwardLookup.get_bound (StoredUnaryLabel.Atom.constant false)
      (StoredForwardLookup.get [] A.data q.val).1 r.val
    have := unary_bound (StoredForwardLookup.get (.constant false)
      (StoredForwardLookup.get [] A.data q.val).1 r.val).1
    have := q.isLt; have := r.isLt; simp only [data]; omega
  have hl (q r : Fin A.count) : (left A q r).2 ≤ 2*A.count+7 := by
    have := StoredForwardLookup.get_bound ([] : List StoredClosedLabel.Atom) A.left q.val
    have := StoredForwardLookup.get_bound (StoredClosedLabel.Atom.constant false)
      (StoredForwardLookup.get [] A.left q.val).1 r.val
    have := closed_bound Empty (StoredForwardLookup.get (.constant false)
      (StoredForwardLookup.get [] A.left q.val).1 r.val).1
    have := q.isLt; have := r.isLt; simp only [left]; omega
  have hr (q r : Fin A.count) : (right A q r).2 ≤ 2*A.count+7 := by
    have := StoredForwardLookup.get_bound ([] : List StoredClosedLabel.Atom) A.right q.val
    have := StoredForwardLookup.get_bound (StoredClosedLabel.Atom.constant false)
      (StoredForwardLookup.get [] A.right q.val).1 r.val
    have := closed_bound Empty (StoredForwardLookup.get (.constant false)
      (StoredForwardLookup.get [] A.right q.val).1 r.val).1
    have := q.isLt; have := r.isLt; simp only [right]; omega
  have ha := StoredRelationTuple.tabulate_bound _ _ hi
  have hb := StoredRelationTuple.tabulate_bound _ _ hf
  have hc := matrix_bound A.count (data A) _ hd
  have hm := matrix_bound A.count (left A) _ hl
  have hn := matrix_bound A.count (right A) _ hr
  have hg := closed_bound (Empty ⊕ Fin 2) A.guard
  simp only [row,rowBudget,vectorBudget] at *; omega

/-! ### The family and the problem -/

abbrev rowDims (rows : List StoredSymbolicRow.Data) : Fin rows.length → Nat := fun i => (rows.get i).count

def familyEntries (rows : List StoredSymbolicRow.Data) :
    List (Sigma (Row U Empty)) × Nat :=
  CountedListConstruction.map (fun A => ((⟨A.count,(row A).1⟩ : Sigma (Row U Empty)),1+(row A).2)) rows

theorem familyEntries_value (rows : List StoredSymbolicRow.Data) :
    (familyEntries rows).1 = rows.map (fun A => (⟨A.count,(row A).1⟩ : Sigma (Row U Empty))) :=
  CountedListConstruction.map_value _ _

def family (rows : List StoredSymbolicRow.Data) :
    StoredRelationArrayPackage.Family U Empty (rowDims rows) × Nat :=
  (⟨⟨(familyEntries rows).1,by rw [familyEntries_value,List.length_map]⟩,by
      intro i
      simp only [StoredRelationTuple.read_value,familyEntries_value,List.getElem_map,rowDims,List.get_eq_getElem]⟩,
    1+(familyEntries rows).2)

theorem family_read (rows : List StoredSymbolicRow.Data) (i : Fin rows.length) :
    (StoredRelationArrayPackage.read (family rows).1 i).1 = (row (rows.get i)).1 := by
  have he := StoredFamilyTransport.entry_cast (R := U) (Q := Empty)
    (StoredRelationTuple.read (family rows).1.entries i).1 ((family rows).1.dimensions i)
    (row (rows.get i)).1
    (by simp only [family,StoredRelationTuple.read_value,familyEntries_value,List.getElem_map,List.get_eq_getElem])
    rfl
  simp only [StoredRelationArrayPackage.read]
  rw [he]
  rfl

theorem family_map (rows : List StoredSymbolicRow.Data) (i : Fin rows.length) :
    RowLanguageTransport.mapRow (toTab d) ((family rows).1.original i) =
      StoredSymbolicRow.denote (d := d) (rows.get i) := by
  unfold StoredRelationArrayPackage.Family.original
  rw [family_read,row_map]

theorem family_shape (rows : List StoredSymbolicRow.Data) (i : Fin rows.length) :
    StoredRowTransport.Bounds (StoredRelationArrayPackage.read (family rows).1 i).1 3 1 := by
  rw [family_read]; exact row_shape _

def familyBudget (k N : Nat) := 2+k*(1+(1+rowBudget N))
theorem family_bound (rows : List StoredSymbolicRow.Data) (N : Nat) (hN : ∀ A ∈ rows, A.count ≤ N) :
    (family rows).2 ≤ familyBudget rows.length N := by
  have hmono : ∀ n, n ≤ N → rowBudget n ≤ rowBudget N := by
    intro n hn
    simp only [rowBudget, StoredEmptyTailCompiler.matrixBudget, StoredEmptyTailCompiler.vectorBudget,
      StoredForwardTableBuild.tabBudget]
    gcongr
  have h := CountedListConstruction.map_bound
    (fun A => ((⟨A.count,(row A).1⟩ : Sigma (Row U Empty)),1+(row A).2)) rows
    (1+rowBudget N) (fun A hA => by
      have := (row_bound A).trans (hmono _ (hN A hA)); simp only; omega)
  simp only [family,familyEntries,familyBudget]; omega

/-- The stored rank problem of a stored rank input. -/
def problem (D : StoredRankInput.Data) : Problem U Empty × Nat :=
  let c := row D.candidate
  let f := family D.rows
  (⟨D.rows.length,rowDims D.rows,D.candidate.count,c.1,f.1⟩,1+c.2+f.2)

theorem problem_bound (D : StoredRankInput.Data) (N : Nat) (hN : ∀ A ∈ D.rows, A.count ≤ N) :
    (problem D).2 ≤ 1+rowBudget D.candidate.count+familyBudget D.rows.length N := by
  have := row_bound D.candidate
  have := family_bound D.rows N hN
  simp only [problem]; omega

theorem problem_bounds (D : StoredRankInput.Data) (N : Nat) (hN : ∀ A ∈ D.rows, A.count ≤ N) :
    Bounds ⟨U,Empty,(problem D).1⟩ D.rows.length N D.candidate.count 3 3 1 where
  rows := le_rfl
  ns := fun i => hN _ (List.get_mem _ _)
  cand := le_rfl
  candidate := row_shape _
  family := fun i => family_shape _ i

/-! ### Avoidance depends only on the packed view -/

open RankAvoidanceCompiler (Avoid RankBound)

theorem sigma_row_eq {L : FirstOrder.Language} {P : Type} {n n' : Nat} {C : SymbolicGuardedBlocks.Row L P n}
    {C' : SymbolicGuardedBlocks.Row L P n'}
    (h : (⟨n,C⟩ : Σ m, SymbolicGuardedBlocks.Row L P m) = ⟨n',C'⟩) : ∃ e : n = n', e ▸ C = C' := by
  cases h; exact ⟨rfl,rfl⟩

theorem avoid_fields (L : FirstOrder.Language) (P : Type) {n n' : Nat}
    (C : SymbolicGuardedBlocks.Row L P n) (C' : SymbolicGuardedBlocks.Row L P n')
    (hC : (⟨n,C⟩ : Σ m, SymbolicGuardedBlocks.Row L P m) = ⟨n',C'⟩) {k k' : Nat}
    (ns : Fin k → Nat) (ns' : Fin k' → Nat)
    (rows : (i : Fin k) → SymbolicGuardedBlocks.Row L P (ns i))
    (rows' : (i : Fin k') → SymbolicGuardedBlocks.Row L P (ns' i))
    (hR : List.ofFn (fun i => (⟨ns i,rows i⟩ : Σ m, SymbolicGuardedBlocks.Row L P m)) =
      List.ofFn (fun i => (⟨ns' i,rows' i⟩ : Σ m, SymbolicGuardedBlocks.Row L P m)))
    {D : Type} [L.Structure D] (p : P → D) :
    (∃ s : D, ∃ body : List D, (C.dataNFA p).Accepts (s :: body) ∧
        ∀ i, ¬ GuardedRowFiring.Fires (rows i) p s body) ↔
      (∃ s : D, ∃ body : List D, (C'.dataNFA p).Accepts (s :: body) ∧
        ∀ i, ¬ GuardedRowFiring.Fires (rows' i) p s body) := by
  cases hC
  have hk : k = k' := by
    have := congrArg List.length hR
    simpa only [List.length_ofFn] using this
  subst hk
  have hf := List.ofFn_injective hR
  have hns : ns = ns' := by
    funext i
    exact congrArg Sigma.fst (congrFun hf i)
  subst hns
  have hrows : rows = rows' := by
    funext i
    exact eq_of_heq (Sigma.mk.inj_iff.mp (congrFun hf i)).2
  subst hrows
  exact Iff.rfl

theorem rankBound_fields (L : FirstOrder.Language) (P : Type) {n n' : Nat}
    (C : SymbolicGuardedBlocks.Row L P n) (C' : SymbolicGuardedBlocks.Row L P n')
    (hC : (⟨n,C⟩ : Σ m, SymbolicGuardedBlocks.Row L P m) = ⟨n',C'⟩)
    {D : Type} [L.Structure D] [DecidableEq D] (p : P → D) (h : Nat) :
    (∀ s body, (C.dataNFA p).Accepts (s :: body) → TerminalBorderRank.suffixBorderRank body ≤ h) ↔
      (∀ s body, (C'.dataNFA p).Accepts (s :: body) → TerminalBorderRank.suffixBorderRank body ≤ h) := by
  cases hC
  exact Iff.rfl

/-! ### The adapted problem of an actual front-end input decides the mathematical problem -/

/-- The stored input built from actual front-end snapshots. -/
abbrev inputOf (C : FiniteSOARankDecision.InputDFA (Fin d)) (rs : List (FiniteSOARankDecision.Component (Fin d))) :
    StoredRankInput.Data :=
  (StoredRankInput.build (d := d) (StoredOrdinaryDFABuild.snapshot C) (rs.map StoredNormalizationRows.snapshot)).1

theorem original_avoid_iff (C : FiniteSOARankDecision.InputDFA (Fin d))
    (rs : List (FiniteSOARankDecision.Component (Fin d))) (p : Empty → Fin d) :
    Avoid (Problem.original (problem (inputOf C rs)).1) p ↔ Avoid (FiniteSOARankDecision.problem C rs) p := by
  have hv := StoredRankInput.value (d := d) C rs
  unfold StoredRankInput.view StoredRankInput.problemView at hv
  have hc := congrArg StoredRankInput.View.candidate hv
  have hr := congrArg StoredRankInput.View.rows hv
  simp only at hc hr
  unfold Avoid
  simp only [Problem.original, problem]
  have e1 : ((row (inputOf C rs).candidate).1.original.dataNFA p) =
      (StoredSymbolicRow.denote (d := d) (inputOf C rs).candidate).dataNFA p := by
    rw [← row_map, RowLanguageTransport.dataNFA_map]
  have e2 : ∀ i s body, GuardedRowFiring.Fires ((family (inputOf C rs).rows).1.original i) p s body ↔
      GuardedRowFiring.Fires (StoredSymbolicRow.denote (d := d) ((inputOf C rs).rows.get i)) p s body := by
    intro i s body
    rw [← family_map, RowLanguageTransport.fires_map]
  simp only [e1, e2]
  apply avoid_fields
  · exact hc
  · rw [← hr]
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [StoredRankInput.pack]

theorem original_rankBound_iff (C : FiniteSOARankDecision.InputDFA (Fin d))
    (rs : List (FiniteSOARankDecision.Component (Fin d))) (p : Empty → Fin d) (h : Nat) :
    RankBound (Problem.original (problem (inputOf C rs)).1) p h ↔
      RankBound (FiniteSOARankDecision.problem C rs) p h := by
  have hv := StoredRankInput.value (d := d) C rs
  unfold StoredRankInput.view StoredRankInput.problemView at hv
  have hc := congrArg StoredRankInput.View.candidate hv
  simp only at hc
  unfold RankBound
  simp only [Problem.original, problem]
  have e1 : ((row (inputOf C rs).candidate).1.original.dataNFA p) =
      (StoredSymbolicRow.denote (d := d) (inputOf C rs).candidate).dataNFA p := by
    rw [← row_map, RowLanguageTransport.dataNFA_map]
  simp only [e1]
  exact rankBound_fields _ _ _ _ hc p h

theorem decision_correct (C : FiniteSOARankDecision.InputDFA (Fin d))
    (rs : List (FiniteSOARankDecision.Component (Fin d))) [Nontrivial (Fin d)] (H : Nat)
    (hb : RankBound (FiniteSOARankDecision.problem C rs) (Empty.elim : Empty → Fin d) H) :
    Formula.Realize (solve H (problem (inputOf C rs)).1).1.original.toFormula (Empty.elim : Empty → Fin d) ↔
      Avoid (FiniteSOARankDecision.problem C rs) (Empty.elim : Empty → Fin d) := by
  rw [← original_avoid_iff]
  exact solve_correct H (problem (inputOf C rs)).1 Empty.elim ((original_rankBound_iff C rs _ H).mpr hb)

/-! ### The towers, from the stored input's own dimensions -/

open StoredRankSizeTower StoredRankCostTower StoredRankHorizonTower in
theorem solve_size_of_input (D : StoredRankInput.Data) (N M H : Nat) (hN : ∀ A ∈ D.rows, A.count ≤ N)
    (hk : D.rows.length ≤ M) (hNM : N ≤ M) (hc : D.candidate.count ≤ M) (h3 : 3 ≤ M) (hH : H+1 ≤ M) :
    StoredRelationalElimination.size (solve H (problem D).1).1 ≤
      DirectRankStateTower.tower 3 (baseArg (liftedExp M)+stepWeight*(H+1)) :=
  StoredRankSizeTower.solve_size_tower ⟨U,Empty,(problem D).1⟩ _ _ _ _ _ _ M
    (problem_bounds D N hN) H hk hNM hc h3 h3 hH

open StoredRankSizeTower StoredRankCostTower StoredRankHorizonTower in
theorem solve_cost_of_input (D : StoredRankInput.Data) (N M H : Nat) (hN : ∀ A ∈ D.rows, A.count ≤ N)
    (hk : D.rows.length ≤ M) (hNM : N ≤ M) (hc : D.candidate.count ≤ M) (h3 : 3 ≤ M) (hH : H+1 ≤ M) :
    (solve H (problem D).1).2 ≤
      DirectRankStateTower.tower 3 (costBase (liftedExp M)+stepWeight*(H+1)+costStepWeight+1+H) :=
  StoredRankCostTower.solve_cost_tower ⟨U,Empty,(problem D).1⟩ _ _ _ _ _ _ M
    (problem_bounds D N hN) H hk hNM hc h3 h3 (by omega) hH

/-! ### The closing evaluation -/

/-- The counted interpreter of stored unary tables: one tuple read and one lookup. -/
def interp (d : Nat) : StoredRelationalEvaluation.Interpreter U d := fun _ r xs =>
  match r with
  | .unary bs =>
    let x := StoredRelationTuple.read xs 0
    let l := ExplicitUnaryTableLanguage.lookup bs x.1.val
    (l.1,1+x.2+l.2)

theorem interp_correct (d : Nat) : ∀ k (r : U k) xs, (interp d k r xs).1 = true ↔
    Structure.RelMap (L := UniformWordLowering.wordLanguage U) r (fun i => (StoredRelationTuple.read xs i).1) := by
  intro k r xs
  cases r
  rfl

theorem interp_bound (d : Nat) : ∀ k, k ≤ 2 → ∀ (r : U k) xs, (interp d k r xs).2 ≤ d+3 := by
  intro k _ r xs
  cases r with
  | unary bs =>
    have h1 := StoredRelationTuple.read_bound xs 0
    have h2 := ExplicitUnaryTableLanguage.lookup_bound (d := d) bs (StoredRelationTuple.read xs 0).1
    simp only [interp]; omega

/-- Close the package, rename the (empty) parameter type to `Fin 0`, evaluate. -/
def decide (D : StoredRankInput.Data) (H : Nat) : Bool × Nat :=
  let a := problem D
  let s := solve H a.1
  let c := StoredRelationalClosure.build s.1
  let r := StoredRelationalFormula.rename (fun e : Empty => ((Empty.elim e : Fin 0),1)) c.1
  let e := StoredRelationalEvaluation.decideFormula (interp d) r.1 FiniteValuationLookup.Values.nil
  (e.1,3+a.2+s.2+c.2+r.2+e.2)

theorem decide_realize (D : StoredRankInput.Data) (H : Nat) :
    (decide (d := d) D H).1 = true ↔
      Formula.Realize (solve H (problem D).1).1.original.toFormula (Empty.elim : Empty → Fin d) := by
  simp only [decide]
  rw [StoredRelationalEvaluation.decide_correct (interp d) (interp_correct d), formula_value,
    Formula.realize_relabel, StoredRelationalClosure.build_value]
  exact iff_of_eq (congrArg _ (funext (fun e => e.elim)))

theorem decide_correct (C : FiniteSOARankDecision.InputDFA (Fin d))
    (rs : List (FiniteSOARankDecision.Component (Fin d))) [Nontrivial (Fin d)] (H : Nat)
    (hb : RankBound (FiniteSOARankDecision.problem C rs) (Empty.elim : Empty → Fin d) H) :
    (decide (d := d) (inputOf C rs) H).1 = true ↔
      Avoid (FiniteSOARankDecision.problem C rs) (Empty.elim : Empty → Fin d) := by
  rw [decide_realize]
  exact decision_correct C rs H hb

/-! ### Cost of the closing evaluation -/

theorem matrix_arity {R : Nat → Type} {P : Type} {k : Nat} :
    (φ : Data R (P ⊕ Fin k) 0) → (h : (denote φ).IsQF) →
      arity (StoredRelationalClosure.matrix φ h).1 = arity φ
  | .falsum, _ => by simp only [StoredRelationalClosure.matrix, arity]
  | .equal _ _, _ => by simp only [StoredRelationalClosure.matrix, arity]
  | .rel _ _, _ => by simp only [StoredRelationalClosure.matrix, arity]
  | .imp φ ψ, h => by
    simp only [StoredRelationalClosure.matrix, arity]
    rw [matrix_arity φ, matrix_arity ψ]
  | .all φ, h => (BoundedFormula.not_all_isQF (denote φ) h).elim

theorem bindAll_arity {R : Nat → Type} {P : Type} : {k : Nat} → (φ : Data R P k) →
    arity (StoredRelationalClosure.bindAll φ).1 = arity φ
  | 0, _ => rfl
  | k+1, φ => by
    simp only [StoredRelationalClosure.bindAll]
    rw [bindAll_arity]
    simp only [arity]; omega

theorem close_arity {R : Nat → Type} {P : Type} {k : Nat} (φ : Data R (P ⊕ Fin k) 0) (h : (denote φ).IsQF) :
    arity (StoredRelationalClosure.close φ h).1 = arity φ := by
  simp only [StoredRelationalClosure.close]
  rw [bindAll_arity, matrix_arity]

/-- Every relation in the stored base signature is unary, independently
of the formula's construction history. -/
theorem unary_arity {P : Type} {n : Nat} (φ : Data U P n) : arity φ ≤ 1 := by
  induction φ with
  | falsum => simp [arity]
  | equal _ _ => simp [arity]
  | rel r args => cases r; exact le_rfl
  | imp φ ψ ihφ ihψ => exact max_le ihφ ihψ
  | all φ ih => exact ih

/-- The final package returns to the unary base signature after lowering. -/
theorem solve_arity (D : StoredRankInput.Data) (N H : Nat) (_hN : ∀ A ∈ D.rows, A.count ≤ N) :
    arity (solve H (problem D).1).1.body ≤ 2 :=
  (unary_arity _).trans (by decide)

/-- Counted cost of the closing evaluation for a closed formula of at most `S` nodes. -/
def evalBudget (d S : Nat) := 1+(d+1)^2+StoredRelationalEvaluation.weight d 0 S 2 d (d+3)*(S*(d+1)^S)

theorem evalBudget_mono (d : Nat) {S S' : Nat} (h : S ≤ S') : evalBudget d S ≤ evalBudget d S' := by
  unfold evalBudget StoredRelationalEvaluation.weight
  gcongr; omega

theorem decide_bound (D : StoredRankInput.Data) (N H S : Nat) (hN : ∀ A ∈ D.rows, A.count ≤ N)
    (hS : StoredRelationalElimination.size (solve H (problem D).1).1 ≤ S) :
    (decide (d := d) D H).2 ≤ 3+(problem D).2+(solve H (problem D).1).2+(2+11*S+6*S)+weight 2 1*S+evalBudget d S := by
  have hk := solve_arity D N H hN
  have hsz := hS
  unfold StoredRelationalElimination.size at hsz
  have hcl := StoredRelationalClosure.build_bound (solve H (problem D).1).1 2 hk
  have hcn := StoredRelationalClosure.build_nodes (solve H (problem D).1).1
  have hca : arity (StoredRelationalClosure.build (solve H (problem D).1).1).1 ≤ 2 := by
    unfold StoredRelationalClosure.build; rw [close_arity]; exact hk
  have hrn := rename_bound (fun e : Empty => ((Empty.elim e : Fin 0),1)) 1 2 (fun _ => le_rfl)
    (StoredRelationalClosure.build (solve H (problem D).1).1).1 hca
  have hrnodes := rename_nodes (fun e : Empty => ((Empty.elim e : Fin 0),1))
    (StoredRelationalClosure.build (solve H (problem D).1).1).1
  have hra := rename_arity (fun e : Empty => ((Empty.elim e : Fin 0),1))
    (StoredRelationalClosure.build (solve H (problem D).1).1).1
  have hev := StoredRelationalEvaluation.decide_bound (interp d)
    (StoredRelationalFormula.rename (fun e : Empty => ((Empty.elim e : Fin 0),1))
      (StoredRelationalClosure.build (solve H (problem D).1).1).1).1
    FiniteValuationLookup.Values.nil 2 (d+3) (interp_bound d) (by rw [hra]; exact hca)
  have hnS : nodes (StoredRelationalFormula.rename (fun e : Empty => ((Empty.elim e : Fin 0),1))
      (StoredRelationalClosure.build (solve H (problem D).1).1).1).1 ≤ S := by
    rw [hrnodes, hcn]; omega
  have hev' := hev.trans (evalBudget_mono d hnS)
  have hcl' : (StoredRelationalClosure.build (solve H (problem D).1).1).2 ≤ 2+11*S+6*S := by
    have : (5+3*2)*nodes (solve H (problem D).1).1.body ≤ 11*S := by omega
    omega
  have hrn' : (StoredRelationalFormula.rename (fun e : Empty => ((Empty.elim e : Fin 0),1))
      (StoredRelationalClosure.build (solve H (problem D).1).1).1).2 ≤ weight 2 1*S := by
    have : weight 2 1*nodes (StoredRelationalClosure.build (solve H (problem D).1).1).1 ≤ weight 2 1*S :=
      Nat.mul_le_mul_left _ (by rw [hcn]; omega)
    omega
  simp only [decide]
  omega

end NSSE.StoredRankAdapter
