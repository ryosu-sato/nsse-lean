import NSSE.StoredRankSolve

/-! Size, arity and cost recurrence of the stored rank recursion, one step at a
time: bounds on the next problem's parameters, on the seed/nonempty packages,
on the lowering of an arbitrary package of the next problem, and on `solve`
at rank `0` and at a successor in terms of the recursive package's actual
shape.  No closed tower is derived here. -/
namespace NSSE.StoredRankSolveBounds
open FirstOrder FirstOrder.Language StoredRelationalRow StoredRelationalClosure StoredRelationalFormula
open StoredNextProblem StoredRankSolve
open StoredRelationalElimination (size)
variable {R : Nat → Type} {P : Type} {n : Nat}

/-! ### Generalities -/

theorem bounds_mono {A : Row R P n} {B K B' K' : Nat} (h : StoredRowTransport.Bounds A B K)
    (hB : B ≤ B') (hK : K ≤ K') : StoredRowTransport.Bounds A B' K' := by
  obtain ⟨⟨hd,hl,hr,hg,hda,hla,hra,hga⟩,hi,hz,hia,hza⟩ := h
  exact ⟨⟨fun q r => (hd q r).trans hB,fun q r => (hl q r).trans hB,fun q r => (hr q r).trans hB,
    hg.trans hB,fun q r => (hda q r).trans hK,fun q r => (hla q r).trans hK,
    fun q r => (hra q r).trans hK,hga.trans hK⟩,
    fun i => (hi i).trans hB,fun i => (hz i).trans hB,fun i => (hia i).trans hK,fun i => (hza i).trans hK⟩

theorem bounds_cast {m : Nat} (h : m = n) (A : Row R P m) {B K : Nat}
    (hb : StoredRowTransport.Bounds A B K) :
    StoredRowTransport.Bounds (cast (congrArg (Row R P) h) A) B K := by
  subst h; exact hb

def toEndpoints {A : Row R P n} {B K : Nat} (h : StoredRowTransport.Bounds A B K) :
    StoredRelationalEndpoints.Bounds A B K :=
  ⟨h.initial,h.final,h.initial_arity,h.final_arity⟩

theorem vars_le_size (A : Package R P) : A.vars ≤ size A := by
  unfold StoredRelationalElimination.size; omega
theorem nodes_le_size (A : Package R P) : nodes A.body ≤ size A := by
  unfold StoredRelationalElimination.size; omega

/-! ### Seed-only and nonempty packages -/

def seedSize (n F : Nat) := 1+n*(3+(1+n*(3+(10+(F+5)+2*F))))
def nonemptySize (n F : Nat) := 1+n*(3+(1+n*(3+(10+(F+23)*3^n+2*F))))

theorem seed_size (A : Row R P n) (F K : Nat) (h : StoredRowTransport.Bounds A F K) :
    size (StoredRelationalNonempty.seed A).1 ≤ seedSize n F := by
  unfold StoredRelationalNonempty.seed StoredRelationalNonempty.collect seedSize
  apply StoredRelationalNonempty.any_size; intro q
  apply StoredRelationalNonempty.any_size; intro r
  exact StoredRelationalEndpoints.size_bound A F K (F+5) (toEndpoints h) _ (fun q r => data_size A F h.data q r) q r

theorem nonempty_size (A : Row R P n) (F K : Nat) (h : StoredRowTransport.Bounds A F K) :
    size (StoredRelationalNonempty.nonempty A).1 ≤ nonemptySize n F := by
  unfold StoredRelationalNonempty.nonempty StoredRelationalNonempty.collect nonemptySize
  apply StoredRelationalNonempty.any_size; intro q
  apply StoredRelationalNonempty.any_size; intro r
  exact StoredRelationalEndpoints.size_bound A F K ((F+23)*3^n) (toEndpoints h) _
    (fun q r => by have := StoredRelationalRowEdges.reach_size A F K h.data h.data_arity q r; omega) q r

theorem collect_arity (A : Row R P n) (F K : Nat) (h : StoredRowTransport.Bounds A F K)
    (W : Fin n → Fin n → Package R P × Nat) (S : Nat)
    (hs : ∀ q r, size (W q r).1 ≤ S) (hk : ∀ q r, arity (W q r).1.body ≤ K) :
    arity (StoredRelationalNonempty.collect A W).1.body ≤ K := by
  unfold StoredRelationalNonempty.collect
  have hin (q : Fin n) := StoredRelationalDisjunction.any_shape n
    (fun r => StoredRelationalEndpoints.endpoints A W q r) (10+S+2*F) (10+S+2*F) K
    (fun r => (vars_le_size _).trans (StoredRelationalEndpoints.size_bound A F K S (toEndpoints h) W hs q r))
    (fun r => (nodes_le_size _).trans (StoredRelationalEndpoints.size_bound A F K S (toEndpoints h) W hs q r))
    (fun r => StoredRelationalEndpoints.arity_bound A F K (toEndpoints h) W hk q r)
  exact (StoredRelationalDisjunction.any_shape n _ (n*(10+S+2*F)) (1+n*(3+(10+S+2*F))) K
    (fun q => (hin q).1) (fun q => (hin q).2.1) (fun q => (hin q).2.2)).2.2

theorem seed_arity (A : Row R P n) (F K : Nat) (h : StoredRowTransport.Bounds A F K) :
    arity (StoredRelationalNonempty.seed A).1.body ≤ K :=
  collect_arity A F K h _ (F+5) (fun q r => data_size A F h.data q r)
    (fun q r => (data_shape A q r).2.2 ▸ h.data_arity q r)

theorem nonempty_arity (A : Row R P n) (F K : Nat) (h : StoredRowTransport.Bounds A F K) :
    arity (StoredRelationalNonempty.nonempty A).1.body ≤ K :=
  collect_arity A F K h _ ((F+23)*3^n)
    (fun q r => by have := StoredRelationalRowEdges.reach_size A F K h.data h.data_arity q r; omega)
    (StoredRelationalRowEdges.reach_arity A F K h.data h.data_arity)

theorem seed_cost (A : Row R P n) (F K : Nat) (h : StoredRowTransport.Bounds A F K) :
    (StoredRelationalNonempty.seed A).2 ≤ StoredRelationalNonempty.seedBudget n F K :=
  StoredRelationalNonempty.seed_bound A F K (toEndpoints h) h.data h.data_arity
theorem nonempty_cost (A : Row R P n) (F K : Nat) (h : StoredRowTransport.Bounds A F K) :
    (StoredRelationalNonempty.nonempty A).2 ≤ StoredRelationalNonempty.nonemptyBudget n F K :=
  StoredRelationalNonempty.nonempty_bound A F K (toEndpoints h) h.data h.data_arity

/-! ### Parameters of the next problem -/

def cleanedStates (S : Problem R P) := S.c*StoredCleanupList.stateFactor (List.ofFn S.ns)

theorem step_cleaned_states (S : Problem R P) : (step S).1.cleaned.cleaned.1 = cleanedStates S :=
  StoredCleanupFamily.states _ _ _

theorem next_ns_le (S : Problem R P) (N : Nat) (hn : ∀ i, S.ns i ≤ N) (j : Fin (next S).1.2.k) :
    (next S).1.2.ns j ≤ 4*N+2 := by
  rw [next_rowStates]; have := hn (UnifiedBlockPresentation.branchAt S.ns (Fin.cast (next_rowCount S) j)).1; omega
theorem next_k_le (S : Problem R P) (N : Nat) (hn : ∀ i, S.ns i ≤ N) :
    (next S).1.2.k ≤ S.k*(2*N^4) := by
  rw [next_rowCount]; exact branches_length_le S.ns N hn
theorem cleanedStates_le (S : Problem R P) (N : Nat) (hn : ∀ i, S.ns i ≤ N) :
    cleanedStates S ≤ S.c*2^((3*N+1)*S.k) := by
  have := StoredCleanupBound.family_exponential_states (liftRows S).1 (liftCandidate S).1 last N hn
  rwa [StoredCleanupFamily.states] at this
theorem next_c_le (S : Problem R P) (N : Nat) (hn : ∀ i, S.ns i ≤ N) :
    (next S).1.2.c ≤ S.c*2^((3*N+1)*S.k)+1 := by
  rw [next_states]; have := cleanedStates_le S N hn; unfold cleanedStates at this; omega

theorem next_candidate_bounds (S : Problem R P) :
    StoredRowTransport.Bounds (next S).1.2.candidate (7+10*cleanedStates S) 1 :=
  StoredCleanedNextCandidate.shape (liftRows S).1 (liftCandidate S).1 last

theorem family_bounds {k : Nat} (ns : Fin k → Nat) (c : Nat) (T : StoredBranchEnumeration.Table ns)
    (j : Fin T.count) :
    StoredRowTransport.Bounds (StoredRelationArrayPackage.read (family ns c T).1 j).1 9 2 := by
  have he := StoredFamilyTransport.entry_cast (R := UnifiedBlockPresentation.Rel ns c) (Q := Empty)
    (StoredRelationTuple.read (family ns c T).1.entries j).1 ((family ns c T).1.dimensions j)
    (StoredBranchEnumeration.rowOf ns c (StoredBranchEnumeration.read T j).1).1.row
    (by simp only [family,familyEntries,StoredRelationTuple.tabulate_read,familyEntry])
    (familyEntry_dim ns c T j)
  simp only [StoredRelationArrayPackage.read]
  rw [he]
  exact bounds_cast (familyEntry_dim ns c T j) _ (StoredOutsideController.shape ns _ _ _)

theorem next_rows_bounds (S : Problem R P) (j : Fin (next S).1.2.k) :
    StoredRowTransport.Bounds (StoredRelationArrayPackage.read (next S).1.2.rows j).1 9 2 :=
  family_bounds S.ns _ _ j

/-- A common node/arity bound for the next problem's candidate and rows. -/
theorem next_bounds (S : Problem R P) :
    StoredRowTransport.Bounds (next S).1.2.candidate (16+10*cleanedStates S) 2 ∧
    ∀ j, StoredRowTransport.Bounds (StoredRelationArrayPackage.read (next S).1.2.rows j).1
      (16+10*cleanedStates S) 2 :=
  ⟨bounds_mono (next_candidate_bounds S) (by omega) (by omega),
    fun j => bounds_mono (next_rows_bounds S j) (by omega) (by omega)⟩

/-! ### The lowering on the retained step -/

/-- The common node bound of the lifted rows and the cleaned candidate. -/
def liftedNodes (S : Problem R P) (F B : Nat) :=
  F+StoredCleanupList.fieldIncrease (List.ofFn S.ns) B+B

theorem step_rows_bounds (S : Problem R P) (B K : Nat)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read S.rows i).1 B K) (i : Fin S.k) :
    StoredRowTransport.Bounds (StoredRelationArrayPackage.read (step S).1.rows i).1 B K :=
  StoredFamilyTransport.preserves inject S.rows B K hr i

theorem step_cleaned_bounds (S : Problem R P) (F B K : Nat)
    (hC : StoredRowTransport.Bounds S.candidate F K)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read S.rows i).1 B K) :
    StoredRowTransport.Bounds (step S).1.cleaned.cleaned.2
      (F+StoredCleanupList.fieldIncrease (List.ofFn S.ns) B) K :=
  StoredCleanupFamily.shape (liftRows S).1 (liftCandidate S).1 last F B K
    (StoredRowTransport.preserves inject S.candidate F K hC)
    (fun i => StoredFamilyTransport.preserves inject S.rows B K hr i)

def lowerSize (S : Problem R P) (F B V Fr : Nat) :=
  StoredPreparedRankStep.sizeBudget S.ns (cleanedStates S) V (liftedNodes S F B) Fr
def lowerBudget (S : Problem R P) (N F B K V Fr : Nat) :=
  StoredPreparedRankStep.budget S.ns (cleanedStates S) V (N+cleanedStates S) (liftedNodes S F B) K Fr

theorem lower_shape (S : Problem R P) (F B K : Nat)
    (hC : StoredRowTransport.Bounds S.candidate F K)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read S.rows i).1 B K)
    (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel S.ns (step S).1.cleaned.cleaned.1) Empty) :
    size (lower S (step S).1 A).1 ≤ lowerSize S F B A.vars (nodes A.body) ∧
      arity (lower S (step S).1 A).1.body ≤ K := by
  have h := StoredPreparedRankStep.shape (step S).1.rows (step S).1.cleaned.cleaned.2 A (liftedNodes S F B) K
    (fun i => bounds_mono (step_rows_bounds S B K hr i) (by unfold liftedNodes; omega) le_rfl)
    (bounds_mono (step_cleaned_bounds S F B K hC hr) (by unfold liftedNodes; omega) le_rfl)
  unfold lowerSize
  rw [← step_cleaned_states]
  exact h

theorem lower_cost (S : Problem R P) (N F B K : Nat) (hn : ∀ i, S.ns i ≤ N)
    (hC : StoredRowTransport.Bounds S.candidate F K)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read S.rows i).1 B K)
    (A : StoredRelationalClosure.Package (UnifiedBlockPresentation.Rel S.ns (step S).1.cleaned.cleaned.1) Empty) :
    (lower S (step S).1 A).2 ≤ lowerBudget S N F B K A.vars (nodes A.body) := by
  have h := StoredPreparedRankStep.bound (step S).1.rows (step S).1.cleaned.cleaned.2 A
    (N+(step S).1.cleaned.cleaned.1) (liftedNodes S F B) K
    (fun i => (hn i).trans (Nat.le_add_right _ _))
    (Nat.le_add_left _ _)
    (fun i => bounds_mono (step_rows_bounds S B K hr i) (by unfold liftedNodes; omega) le_rfl)
    (bounds_mono (step_cleaned_bounds S F B K hC hr) (by unfold liftedNodes; omega) le_rfl)
  unfold lowerBudget
  rw [← step_cleaned_states]
  exact h

/-! ### The disjunction -/

def disjBudget (K sA sB : Nat) := sA+7+weight K 2*sA+weight K (sA+3)*sB

theorem weight_mono (K : Nat) {a b : Nat} (h : a ≤ b) : weight K a ≤ weight K b := by
  unfold weight; nlinarith

theorem disj_cost (A B : Package R P) (K sA sB : Nat) (ha : arity A.body ≤ K) (hb : arity B.body ≤ K)
    (hsa : size A ≤ sA) (hsb : size B ≤ sB) :
    (StoredRelationalPackages.disj A B).2 ≤ disjBudget K sA sB := by
  have h := StoredRelationalPackages.disj_bound A B K ha hb
  have hv := vars_le_size A
  have hn := nodes_le_size A
  have hm := nodes_le_size B
  have hw := weight_mono K (show A.vars+3 ≤ sA+3 by omega)
  unfold disjBudget
  have h1 : weight K 2*nodes A.body ≤ weight K 2*sA := Nat.mul_le_mul_left _ (by omega)
  have h2 : weight K (A.vars+3)*nodes B.body ≤ weight K (sA+3)*sB := Nat.mul_le_mul hw (by omega)
  omega

theorem disj_size (A B : Package R P) :
    size (StoredRelationalPackages.disj A B).1 = 3+size A+size B := by
  have h1 := (StoredRelationalPackages.disj_shape A B).1
  have h2 := (StoredRelationalPackages.disj_shape A B).2.1
  unfold StoredRelationalElimination.size
  omega
theorem disj_arity (A B : Package R P) (K : Nat) (ha : arity A.body ≤ K) (hb : arity B.body ≤ K) :
    arity (StoredRelationalPackages.disj A B).1.body ≤ K := by
  rw [(StoredRelationalPackages.disj_shape A B).2.2]; exact max_le ha hb

/-! ### `solve` at rank zero and at a successor -/

/-- The recursive package at a successor rank, as it appears inside `solve`. -/
def inner (h : Nat) (S : Problem R P) := solve h (step S).1.problem
/-- The nonemptiness package at rank zero. -/
def base (S : Problem R P) := StoredRelationalNonempty.nonempty (step S).1.problem.candidate

theorem base_shape (S : Problem R P) :
    size (base S).1 ≤ nonemptySize (next S).1.2.c (7+10*cleanedStates S) ∧
      arity (base S).1.body ≤ 1 :=
  ⟨nonempty_size _ _ 1 (next_candidate_bounds S),nonempty_arity _ _ 1 (next_candidate_bounds S)⟩
theorem base_cost (S : Problem R P) :
    (base S).2 ≤ StoredRelationalNonempty.nonemptyBudget (next S).1.2.c (7+10*cleanedStates S) 1 :=
  nonempty_cost _ _ 1 (next_candidate_bounds S)

theorem solve_zero_shape (S : Problem R P) (F B K : Nat)
    (hC : StoredRowTransport.Bounds S.candidate F K)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read S.rows i).1 B K) :
    size (solve 0 S).1 ≤ 3+seedSize S.c F+lowerSize S F B (base S).1.vars (nodes (base S).1.body) ∧
      arity (solve 0 S).1.body ≤ K := by
  have hs := seed_size S.candidate F K hC
  have hl := lower_shape S F B K hC hr (base S).1
  simp only [solve,base] at *
  constructor
  · rw [disj_size]; omega
  · exact disj_arity _ _ K (seed_arity S.candidate F K hC) hl.2

theorem solve_succ_shape (h : Nat) (S : Problem R P) (F B K : Nat)
    (hC : StoredRowTransport.Bounds S.candidate F K)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read S.rows i).1 B K) :
    size (solve (h+1) S).1 ≤ 3+seedSize S.c F+lowerSize S F B (inner h S).1.vars (nodes (inner h S).1.body) ∧
      arity (solve (h+1) S).1.body ≤ K := by
  have hs := seed_size S.candidate F K hC
  have hl := lower_shape S F B K hC hr (inner h S).1
  simp only [solve,inner] at *
  constructor
  · rw [disj_size]; omega
  · exact disj_arity _ _ K (seed_arity S.candidate F K hC) hl.2

def stepBudget (S : Problem R P) (N F B K V Fr : Nat) :=
  4+StoredRelationalNonempty.seedBudget S.c F K+StoredNextProblem.budget S.k N S.c F B K+
    lowerBudget S N F B K V Fr+disjBudget K (seedSize S.c F) (lowerSize S F B V Fr)

theorem solve_zero_cost (S : Problem R P) (N F B K : Nat) (hn : ∀ i, S.ns i ≤ N)
    (hC : StoredRowTransport.Bounds S.candidate F K)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read S.rows i).1 B K) :
    (solve 0 S).2 ≤ stepBudget S N F B K (base S).1.vars (nodes (base S).1.body)+(base S).2 := by
  have ha := seed_cost S.candidate F K hC
  have hst : (step S).2 ≤ StoredNextProblem.budget S.k N S.c F B K := next_bound S N F B K hn hC hr
  have hl := lower_cost S N F B K hn hC hr (base S).1
  have hd := disj_cost _ _ K _ _ (seed_arity S.candidate F K hC) (lower_shape S F B K hC hr (base S).1).2
    (seed_size S.candidate F K hC) (lower_shape S F B K hC hr (base S).1).1
  have hb := (base S).2
  simp only [solve,base,stepBudget] at *
  omega

theorem solve_succ_cost (h : Nat) (S : Problem R P) (N F B K : Nat) (hn : ∀ i, S.ns i ≤ N)
    (hC : StoredRowTransport.Bounds S.candidate F K)
    (hr : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read S.rows i).1 B K) :
    (solve (h+1) S).2 ≤ stepBudget S N F B K (inner h S).1.vars (nodes (inner h S).1.body)+(inner h S).2 := by
  have ha := seed_cost S.candidate F K hC
  have hst : (step S).2 ≤ StoredNextProblem.budget S.k N S.c F B K := next_bound S N F B K hn hC hr
  have hl := lower_cost S N F B K hn hC hr (inner h S).1
  have hd := disj_cost _ _ K _ _ (seed_arity S.candidate F K hC) (lower_shape S F B K hC hr (inner h S).1).2
    (seed_size S.candidate F K hC) (lower_shape S F B K hC hr (inner h S).1).1
  simp only [solve,inner,stepBudget] at *
  omega

end NSSE.StoredRankSolveBounds
