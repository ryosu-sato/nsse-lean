import NSSE.StoredBranchEnumeration
import NSSE.StoredCleanedNextCandidate
import NSSE.StoredFamilyTransport

/-! The stored next-rank problem: fresh-parameter lifting, actual empty-tail
cleanup, next-candidate construction, branch enumeration and the enumerated
row family, all produced by counted construction from stored input, and the
slice theorem `slice_iff_next` connecting the stored next problem to the
original avoidance question on one terminal slice.  This is the stored
analogue of `RankAvoidanceCompiler.next` / `slice_iff_next` /
`next_rank_bound`. -/
namespace NSSE.StoredNextProblem
open FirstOrder FirstOrder.Language StoredRelationalRow GuardedRowFiring
variable {R : Nat → Type} {P : Type}

structure Problem (R : Nat → Type) (P : Type) where
  k : Nat
  ns : Fin k → Nat
  c : Nat
  candidate : Row R P c
  rows : StoredRelationArrayPackage.Family R P ns

abbrev Fresh (P : Type) := P ⊕ Fin 2
def seed : Fresh P := .inr 0
def last : Fresh P := .inr 1
def inject (p : P) : Fresh P × Nat := (.inl p,1)

/-! ### Parameter lifting -/

def liftCandidate (S : Problem R P) : Row R (Fresh P) S.c × Nat :=
  StoredRowTransport.build inject S.candidate
def liftRows (S : Problem R P) : StoredRelationArrayPackage.Family R (Fresh P) S.ns × Nat :=
  StoredFamilyTransport.build inject S.rows

theorem liftCandidate_dataNFA (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (s a : D) :
    (liftCandidate S).1.original.dataNFA (Sum.elim p ![s,a]) = S.candidate.original.dataNFA p := by
  rw [liftCandidate,StoredRowTransport.value,RowParameterTransport.dataNFA_map]; rfl
theorem liftRows_fires (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (s a : D) (i : Fin S.k) (x : D) (body : List D) :
    Fires ((liftRows S).1.original i) (Sum.elim p ![s,a]) x body ↔ Fires (S.rows.original i) p x body := by
  rw [liftRows,StoredFamilyTransport.original,RowParameterTransport.fires_map]; rfl
theorem liftRows_emptyTail (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (s a : D) (i : Fin S.k) (x : D) (body : List D) :
    EmptyTailFires ((liftRows S).1.original i) (Sum.elim p ![s,a]) x body ↔
      EmptyTailFires (S.rows.original i) p x body := by
  rw [liftRows,StoredFamilyTransport.original]
  simp only [EmptyTailFires,RowParameterTransport.firesAt_map]; rfl
theorem liftRows_positive (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (s a : D) (i : Fin S.k) (x : D) (body : List D) :
    PositiveFires ((liftRows S).1.original i) (Sum.elim p ![s,a]) x body ↔
      PositiveFires (S.rows.original i) p x body := by
  rw [liftRows,StoredFamilyTransport.original]
  simp only [PositiveFires,RowParameterTransport.firesAt_map]; rfl

/-! ### Cleanup and candidate -/

def cleanedCandidate (S : Problem R P) : StoredCleanedNextCandidate.Result R (Fresh P) S.ns × Nat :=
  StoredCleanedNextCandidate.build (liftRows S).1 (liftCandidate S).1 last

/-- The presented structure of the step, over the actual lifted rows and the
actual cleaned candidate. -/
def stepModel (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (s a : D) :
    (UnifiedBlockPresentation.language S.ns (cleanedCandidate S).1.cleaned.1).Structure (List D) :=
  UnifiedBlockPresentation.model (liftRows S).1.original (cleanedCandidate S).1.cleaned.2.original
    seed last (Sum.elim p ![s,a])

/-! ### The enumerated row family -/

variable {k : Nat}

def familyDims (ns : Fin k → Nat) (T : StoredBranchEnumeration.Table ns) (j : Fin T.count) : Nat :=
  UnifiedBlockPresentation.familyStates ns (Fin.cast T.count_eq j)

def familyEntry (ns : Fin k → Nat) (c : Nat) (T : StoredBranchEnumeration.Table ns) (j : Fin T.count) :
    Sigma (Row (UnifiedBlockPresentation.Rel ns c) Empty) × Nat :=
  let b := StoredBranchEnumeration.read T j
  let r := StoredBranchEnumeration.rowOf ns c b.1
  (⟨r.1.states.count,r.1.row⟩,2+b.2+r.2)

def familyEntries (ns : Fin k → Nat) (c : Nat) (T : StoredBranchEnumeration.Table ns) :=
  StoredRelationTuple.tabulate (familyEntry ns c T)

theorem familyEntry_dim (ns : Fin k → Nat) (c : Nat) (T : StoredBranchEnumeration.Table ns) (j : Fin T.count) :
    (familyEntry ns c T j).1.1 = familyDims ns T j := by
  simp only [familyEntry,StoredBranchEnumeration.rowOf_states,familyDims,
    UnifiedBlockPresentation.familyStates,SymbolicOutsideController.length_states,
    StoredBranchEnumeration.read_value]

def family (ns : Fin k → Nat) (c : Nat) (T : StoredBranchEnumeration.Table ns) :
    StoredRelationArrayPackage.Family (UnifiedBlockPresentation.Rel ns c) Empty (familyDims ns T) × Nat :=
  (⟨(familyEntries ns c T).1,fun j => by
      show (StoredRelationTuple.read (familyEntries ns c T).1 j).1.1 = _
      rw [familyEntries,StoredRelationTuple.tabulate_read]
      exact familyEntry_dim ns c T j⟩,1+(familyEntries ns c T).2)

theorem fires_cast {m n : Nat} (h : m = n) (A : Row R P m) {D : Type}
    [(UniformWordLowering.wordLanguage R).Structure D] (v : P → D) (s : D) (body : List D) :
    Fires (cast (congrArg (Row R P) h) A).original v s body ↔ Fires A.original v s body := by
  subst h; rfl

theorem family_fires (ns : Fin k → Nat) (c : Nat) (T : StoredBranchEnumeration.Table ns) (j : Fin T.count)
    {D : Type} [(UnifiedBlockPresentation.language ns c).Structure D] (v : Empty → D) (s : D) (body : List D) :
    Fires ((family ns c T).1.original j) v s body ↔
      Fires (UnifiedBlockPresentation.familyRows ns c (Fin.cast T.count_eq j)) v s body := by
  have he := StoredFamilyTransport.entry_cast (R := UnifiedBlockPresentation.Rel ns c) (Q := Empty)
    (StoredRelationTuple.read (family ns c T).1.entries j).1 ((family ns c T).1.dimensions j)
    (StoredBranchEnumeration.rowOf ns c (StoredBranchEnumeration.read T j).1).1.row
    (by simp only [family,familyEntries,StoredRelationTuple.tabulate_read,familyEntry])
    (familyEntry_dim ns c T j)
  change Fires (StoredRelationArrayPackage.read (family ns c T).1 j).1.original v s body ↔ _
  simp only [StoredRelationArrayPackage.read]
  rw [he,fires_cast (familyEntry_dim ns c T j),← StoredBranchEnumeration.rowOf_fires]
  have key : ∀ b b' : UnifiedBlockPresentation.Branch ns, b = b' →
      (Fires (StoredBranchEnumeration.rowOf ns c b).1.row.original v s body ↔
        Fires (StoredBranchEnumeration.rowOf ns c b').1.row.original v s body) := by
    rintro b _ rfl; exact Iff.rfl
  exact key _ _ (StoredBranchEnumeration.read_value T j)

/-! ### The stored next problem -/

def next (S : Problem R P) :
    ((c' : Nat) × Problem (UnifiedBlockPresentation.Rel S.ns c') Empty) × Nat :=
  let a := cleanedCandidate S
  let t := StoredBranchEnumeration.build S.ns
  let f := family S.ns a.1.cleaned.1 t.1
  (⟨a.1.cleaned.1,⟨t.1.count,familyDims S.ns t.1,a.1.candidate.states.count,a.1.candidate.row,f.1⟩⟩,
    5+(liftRows S).2+(liftCandidate S).2+a.2+t.2+f.2)

theorem next_states (S : Problem R P) :
    (next S).1.2.c = S.c*StoredCleanupList.stateFactor (List.ofFn S.ns)+1 :=
  StoredCleanedNextCandidate.states _ _ _
theorem next_rowCount (S : Problem R P) :
    (next S).1.2.k = (UnifiedBlockPresentation.branches S.ns).length :=
  (StoredBranchEnumeration.build S.ns).1.count_eq

/-- Every generated row has `4n+2` states for the source row's `n`. -/
theorem next_rowStates (S : Problem R P) (j : Fin (next S).1.2.k) :
    (next S).1.2.ns j =
      4*S.ns (UnifiedBlockPresentation.branchAt S.ns (Fin.cast (next_rowCount S) j)).1+2 := by
  change UnifiedBlockPresentation.familyStates S.ns _ = _
  rw [UnifiedBlockPresentation.familyStates,SymbolicOutsideController.length_states]

/-! ### The slice theorem -/

theorem cleaned_avoidance (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (s a : D) (w : List D) :
    (((cleanedCandidate S).1.cleaned.2.original.dataNFA (Sum.elim p ![s,a])).Accepts (s :: (w ++ [a])) ∧
      ∀ i, ¬ PositiveFires ((liftRows S).1.original i) (Sum.elim p ![s,a]) s (w ++ [a])) ↔
    ((S.candidate.original.dataNFA p).Accepts (s :: (w ++ [a])) ∧
      ∀ i, ¬ Fires (S.rows.original i) p s (w ++ [a])) := by
  have hw (i : Fin S.k) :
      EmptyTailFiring.Witness ((liftRows S).1.original i) last (Sum.elim p ![s,a]) (s :: (w ++ [a])) ↔
        EmptyTailFires (S.rows.original i) p s (w ++ [a]) := by
    rw [EmptyTailFiring.witness_iff_emptyTail _ _ _ s (w ++ [a]) (by
      change lastOr s (s :: (w ++ [a])) = a
      rw [lastOr_seed_cons,lastOr_append_singleton])]
    exact liftRows_emptyTail S p s a i s (w ++ [a])
  change ((StoredCleanedNextCandidate.build (liftRows S).1 (liftCandidate S).1 last).1.cleaned.2.original.dataNFA
    (Sum.elim p ![s,a])).Accepts _ ∧ _ ↔ _
  simp only [StoredCleanedNextCandidate.build,StoredCleanupFamily.accepts,liftCandidate_dataNFA,hw,
    liftRows_positive,fires_iff_positive_or_empty,not_or,forall_and]
  tauto

/-- The original slice question is equivalent to plain avoidance of the
stored next problem, in the step's presented structure. -/
theorem slice_iff_next (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    (p : P → D) (s a : D) :
    (∃ w : List D, (S.candidate.original.dataNFA p).Accepts (s :: (w ++ [a])) ∧
      ∀ i, ¬ Fires (S.rows.original i) p s (w ++ [a])) ↔
      letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
      ∃ bs : List (List D),
        ((next S).1.2.candidate.original.dataNFA (Empty.elim : Empty → List D)).Accepts bs ∧
        ∀ j, ¬ Fires ((next S).1.2.rows.original j) (Empty.elim : Empty → List D)
          (bs.head?.getD []) bs.tail := by
  letI := stepModel S p s a
  have h := BlockCandidateTransport.exists_avoider_iff (liftRows S).1.original
    (cleanedCandidate S).1.cleaned.2.original seed last (Sum.elim p ![s,a])
  change (∃ w : List D, ((cleanedCandidate S).1.cleaned.2.original.dataNFA (Sum.elim p ![s,a])).Accepts
      (s :: (w ++ [a])) ∧
      ∀ i, ¬ PositiveFires ((liftRows S).1.original i) (Sum.elim p ![s,a]) s (w ++ [a])) ↔ _ at h
  refine Iff.trans (exists_congr (fun w => (cleaned_avoidance S p s a w).symm)) (h.trans ?_)
  apply exists_congr
  intro bs
  apply and_congr
  · change _ ↔ ((StoredNextCandidate.build S.ns (cleanedCandidate S).1.cleaned.1).1.row.original.dataNFA
      (Empty.elim : Empty → List D)).Accepts bs
    exact (StoredNextCandidate.original_accepts S.ns _ _ bs).symm
  · let T := (StoredBranchEnumeration.build S.ns).1
    change _ ↔ ∀ j : Fin T.count, ¬ Fires ((family S.ns (cleanedCandidate S).1.cleaned.1 T).1.original j) _ _ _
    simp only [family_fires]
    constructor
    · intro H j; exact H _
    · intro H i
      have := H (Fin.cast T.count_eq.symm i)
      exact this

/-- The original rank promise transfers to the stored next candidate with the
rank lowered by one, for every accepted block word. -/
theorem next_rank_bound (S : Problem R P) {D : Type} [(UniformWordLowering.wordLanguage R).Structure D]
    [DecidableEq D] (p : P → D) (s a : D) (h : Nat)
    (hb : ∀ x body, (S.candidate.original.dataNFA p).Accepts (x :: body) →
      TerminalBorderRank.suffixBorderRank body ≤ h+1) :
    letI : (UnifiedBlockPresentation.language S.ns (next S).1.1).Structure (List D) := stepModel S p s a
    ∀ (U : List D) (body : List (List D)), ((next S).1.2.candidate.original.dataNFA (Empty.elim : Empty → List D)).Accepts (U :: body) →
      TerminalBorderRank.suffixBorderRank body ≤ h := by
  letI := stepModel S p s a
  intro U body hC
  have hbound : ∀ w, ((cleanedCandidate S).1.cleaned.2.original.dataNFA (Sum.elim p ![s,a])).Accepts
      (Sum.elim p ![s,a] seed :: w) → TerminalBorderRank.suffixBorderRank w ≤ h+1 := by
    intro w hw
    change ((StoredCleanedNextCandidate.build (liftRows S).1 (liftCandidate S).1 last).1.cleaned.2.original.dataNFA
      (Sum.elim p ![s,a])).Accepts (s :: w) at hw
    simp only [StoredCleanedNextCandidate.build,StoredCleanupFamily.accepts,liftCandidate_dataNFA] at hw
    exact hb s w hw.1
  have hr := BlockCandidateTransport.candidate_rank_bound (liftRows S).1.original
    (cleanedCandidate S).1.cleaned.2.original seed last (Sum.elim p ![s,a]) (h+1) (by omega) hbound (U :: body)
  change ((StoredNextCandidate.build S.ns (cleanedCandidate S).1.cleaned.1).1.row.original.dataNFA
    (Empty.elim : Empty → List D)).Accepts (U :: body) at hC
  rw [StoredNextCandidate.original_accepts] at hC
  simpa using hr hC

/-! ### Cost -/

theorem branches_length_le (ns : Fin k → Nat) (N : Nat) (hn : ∀ i, ns i ≤ N) :
    (UnifiedBlockPresentation.branches ns).length ≤ k*(2*N^4) := by
  rw [← StoredBranchEnumeration.branchEntries_value]
  simp only [StoredBranchEnumeration.branchEntries,CountedListConstruction.flatMap_value,
    CountedFinEnumeration.value,List.length_flatMap]
  have h := List.sum_le_card_nsmul ((List.finRange k).map
    (fun i => ((StoredBranchEnumeration.branchOf ns i).1).length)) (2*N^4) (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      rw [StoredBranchEnumeration.branchOf_length]
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hn i) 4))
  simpa [List.length_map,List.length_finRange,smul_eq_mul] using h

def familyEntryCost (k N : Nat) := 2+k*(2*N^4)+614*(N+1)^3
def familyBudget (k N : Nat) := 2+StoredForwardTableBuild.tabBudget (k*(2*N^4)) (familyEntryCost k N)

theorem family_bound (ns : Fin k → Nat) (c : Nat) (T : StoredBranchEnumeration.Table ns) (N : Nat)
    (hn : ∀ i, ns i ≤ N) : (family ns c T).2 ≤ familyBudget k N := by
  have hc : T.count ≤ k*(2*N^4) := T.count_eq.le.trans (branches_length_le ns N hn)
  have he (j : Fin T.count) : (familyEntry ns c T j).2 ≤ familyEntryCost k N := by
    have hr := StoredBranchEnumeration.read_bound T j
    have hb := StoredBranchEnumeration.rowOf_bound ns c (StoredBranchEnumeration.read T j).1
    have hm : 614*(ns (StoredBranchEnumeration.read T j).1.1+1)^3 ≤ 614*(N+1)^3 := by
      gcongr; exact hn _
    simp only [familyEntry,familyEntryCost]; omega
  have ht := StoredRelationTuple.tabulate_bound _ _ he
  have hmono : StoredForwardTableBuild.tabBudget T.count (familyEntryCost k N) ≤
      StoredForwardTableBuild.tabBudget (k*(2*N^4)) (familyEntryCost k N) := by
    unfold StoredForwardTableBuild.tabBudget; gcongr
  simp only [family,familyEntries,familyBudget]; omega

def budget (k N c F B K : Nat) :=
  7+StoredRowTransport.budget c 1 F K+StoredFamilyTransport.budget k N 1 B K+
    (4+k*(2+StoredCleanupBound.stepUpper (c*2^((3*N+1)*k)) N B K)+604*(c*2^((3*N+1)*k)+1)^4)+
    (3+StoredBranchEnumeration.branchBudget k N+k*(2*N^4))+familyBudget k N

/-- Total counted cost of one stored next-rank step, from stored input of
`k` rows with at most `N` states, `B` nodes and arity `K`, and a candidate of
`c` states with `F` nodes. -/
theorem next_bound (S : Problem R P) (N F B K : Nat) (hn : ∀ i, S.ns i ≤ N)
    (hC : StoredRowTransport.Bounds S.candidate F K)
    (hrows : ∀ i, StoredRowTransport.Bounds (StoredRelationArrayPackage.read S.rows i).1 B K) :
    (next S).2 ≤ budget S.k N S.c F B K := by
  have hf : ∀ p : P, (inject p).2 ≤ 1 := fun _ => le_rfl
  have hl := StoredRowTransport.bound inject S.candidate 1 F K hf hC
  have hr := StoredFamilyTransport.bound inject S.rows N 1 B K hf hn hrows
  have hcl := StoredCleanedNextCandidate.bound (liftRows S).1 (liftCandidate S).1 last N B K hn
    (fun i => StoredFamilyTransport.preserves inject S.rows B K hrows i)
  have hb := StoredBranchEnumeration.build_bound S.ns N hn
  have hlen : (StoredBranchEnumeration.branchEntries S.ns).1.length ≤ S.k*(2*N^4) := by
    rw [StoredBranchEnumeration.branchEntries_value]; exact branches_length_le S.ns N hn
  have hfam := family_bound S.ns (cleanedCandidate S).1.cleaned.1 (StoredBranchEnumeration.build S.ns).1 N hn
  simp only [next,cleanedCandidate,liftRows,liftCandidate,budget] at *
  omega

end NSSE.StoredNextProblem
