import NSSE.StoredRowTransport

/-! Actual parameter transport and array columns connected to raw run closure.
The semantic view retains the explicit proved reindexing of raw states. -/
namespace NSSE.StoredGuardedArrayRun
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {n q T : Nat}

def liftName (p : P) : Params P q T × Nat := (.inl p,1)
def closed (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (T : Nat) (positive : Bool) : Data R (Params P q T) 0 × Nat :=
  let a := StoredRowTransport.build liftName A
  let f := StoredRawSkippedRun.closed a.1 e (.inl seed) (.inl last) first
    (StoredArrayColumns.build zero args T) (.inl one) T positive
  (f.1,1+a.2+f.2)
def budget (n q T B K : Nat) := 1+StoredRowTransport.budget n 1 B K+
  StoredRawSkippedRun.budget n T (StoredArrayColumns.budget q T) B K
theorem bound (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (positive : Bool) (B K : Nat)
    (h : StoredRowTransport.Bounds A B K) :
    (closed A e seed last first zero one args T positive).2 ≤ budget n q T B K := by
  have ha := StoredRowTransport.bound (liftName (q := q) (T := T)) A 1 B K (fun _ => le_rfl) h
  have hf := StoredRawSkippedRun.closed_bound (T := T) (StoredRowTransport.build liftName A).1 e (.inl seed) (.inl last) first
    (StoredArrayColumns.build zero args T) (.inl one) positive (StoredArrayColumns.budget q T) B K
    (StoredRowTransport.preserves liftName A B K h).toBounds (fun t _ => StoredArrayColumns.bound zero args t)
  simp only [closed,budget]; omega

def original (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) :
    ConvolutionShapes.WordAutomaton (UniformWordLowering.wordLanguage R) (Params P q T) (StoredRawStates.build n).1.count 2 :=
  let a := RowParameterTransport.mapRow (Sum.inl : P → Params P q T) A.original
  let table := (StoredRawStates.build n).1
  { initial := fun i => (a.raw e (.inl seed) (.inl last) first).initial (Fin.cast table.count_eq i)
    final := fun i => (a.raw e (.inl seed) (.inl last) first).final (Fin.cast table.count_eq i)
    silent := fun _ _ => ⊥
    step := fun s i j => (a.raw e (.inl seed) (.inl last) first).step s (Fin.cast table.count_eq i) (Fin.cast table.count_eq j) }
theorem raw_value (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) :
    StoredRawAutomaton.original (StoredRowTransport.build (liftName (q := q) (T := T)) A).1
      (StoredRawStates.build n).1 e (.inl seed) (.inl last) first = original A e seed last first := by
  simp only [StoredRawAutomaton.original,StoredRowTransport.value,liftName,original]
theorem value (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (positive : Bool) :
    denote (closed A e seed last first zero one args T positive).1 =
      DynamicColumnRunFormula.compile (SkipEmptyColumns.automaton (original A e seed last first))
        (fun t i => flags zero q T t (StoredRelationTuple.read args i).1)
        (fun t i => letters zero q T t (StoredRelationTuple.read args i).1) (.inl one) T positive := by
  simp only [closed,StoredRawSkippedRun.closed_value,raw_value]
  congr 1
  · funext t i; exact StoredArrayColumns.flags_value zero args t i
  · funext t i; exact StoredArrayColumns.letters_value zero args t i

/-- Semantic transport only; no counted executable uses this view. -/
def reindex {m n : Nat} (h : m=n)
    (a : ConvolutionShapes.WordAutomaton (UniformWordLowering.wordLanguage R) P n 2) :
    ConvolutionShapes.WordAutomaton (UniformWordLowering.wordLanguage R) P m 2 where
  initial i := a.initial (Fin.cast h i)
  final i := a.final (Fin.cast h i)
  silent i j := a.silent (Fin.cast h i) (Fin.cast h j)
  step s i j := a.step s (Fin.cast h i) (Fin.cast h j)
theorem skip_reindex {m n : Nat} (h : m=n)
    (a : ConvolutionShapes.WordAutomaton (UniformWordLowering.wordLanguage R) P n 2) :
    SkipEmptyColumns.automaton (reindex h a) = reindex h (SkipEmptyColumns.automaton a) := by
  subst m; rfl
theorem compile_reindex {m n : Nat} (h : m=n)
    (a : ConvolutionShapes.WordAutomaton (UniformWordLowering.wordLanguage R) P n 2)
    (fs ls : Nat → Fin 2 → P) (one : P) (T : Nat) (positive : Bool) :
    DynamicColumnRunFormula.compile (reindex h a) fs ls one T positive =
      DynamicColumnRunFormula.compile a fs ls one T positive := by
  subst m; rfl
theorem original_reindex (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool) :
    original (q := q) (T := T) A e seed last first =
      reindex (StoredRawStates.build n).1.count_eq
        ((RowParameterTransport.mapRow (Sum.inl : P → Params P q T) A.original).raw e (.inl seed) (.inl last) first) := rfl

theorem original_value (A : Row R P n) (e : SymbolicGuardedBlocks.Ends n) (seed last : P) (first : Bool)
    (zero one : P) (args : StoredArrayColumns.Arguments q) (positive : Bool) :
    denote (closed A e seed last first zero one args T positive).1 =
      FiniteArrayHFormula.compile A.original e seed last first zero one q T
        (fun i => (StoredRelationTuple.read args i).1) positive := by
  rw [value,original_reindex,skip_reindex,compile_reindex]
  rfl
end NSSE.StoredGuardedArrayRun
