import NSSE.StoredIdentityMarkers

/-! Counted dispatch over all original block relation constructors. -/
namespace NSSE.StoredBlockArrayPackage
open FirstOrder FirstOrder.Language StoredRelationalFormula StoredRelationalRow FiniteWordCoordinates
variable {R : Nat → Type} {P : Type} {n q T : Nat}

def duplicate (args : StoredRelationTuple.Data (Fin q) 1) : StoredArrayColumns.Arguments q × Nat :=
  let a := StoredRelationTuple.read args 0
  (⟨[a.1,a.1],rfl⟩,5+a.2)
theorem duplicate_read (args : StoredRelationTuple.Data (Fin q) 1) (i : Fin 2) :
    (StoredRelationTuple.read (duplicate args).1 i).1 = (StoredRelationTuple.read args 0).1 := by
  fin_cases i <;> rfl
theorem duplicate_bound (args : StoredRelationTuple.Data (Fin q) 1) : (duplicate args).2 ≤ 6 := by
  have h := StoredRelationTuple.read_bound args 0
  simp only [duplicate]; omega

def build (A : Row R P n) (seed last zero one : P) (q T : Nat) :
    {a : Nat} → BlockRelationPresentation.Rel n a → StoredRelationTuple.Data (Fin q) a → Bool →
      StoredRelationalClosure.Package R (Params P q T) × Nat
  | _, .block s t, args, positive =>
    let a := StoredIdentityMarkers.build A
    let b := duplicate args
    let f := StoredGuardedArrayPackage.build a.1 ⟨s,t,s,t⟩ last last false zero one b.1 T positive
    (f.1,3+a.2+b.2+f.2)
  | _, .guarded e first, args, positive =>
    let f := StoredGuardedArrayPackage.build A e seed last first zero one args T positive
    (f.1,1+f.2)
  | _, .initial s, _, positive =>
    let f := StoredArrayParameterAtoms.initialPackage A seed s q T positive
    (f.1,1+f.2)
  | _, .final s, _, positive =>
    let f := StoredArrayParameterAtoms.finalPackage A s q T positive
    (f.1,1+f.2)

theorem value (A : Row R P n) (seed last zero one : P) {a : Nat}
    (r : BlockRelationPresentation.Rel n a) (args : StoredRelationTuple.Data (Fin q) a) (positive : Bool) :
    (build A seed last zero one q T r args positive).1.original.toFormula =
      (ArrayAtomExistentialPackages.block A.original A.qfree seed last zero one q T r
        (fun i => (StoredRelationTuple.read args i).1) positive).toFormula := by
  cases r with
  | block s t =>
    simp only [build,StoredGuardedArrayPackage.value,StoredIdentityMarkers.value,duplicate_read]
    rfl
  | guarded e first =>
    simp only [build,StoredGuardedArrayPackage.value]
    rfl
  | initial s =>
    simp only [build,StoredArrayParameterAtoms.initialPackage_value A seed last zero one]
    rfl
  | final s =>
    simp only [build,StoredArrayParameterAtoms.finalPackage_value A seed last zero one]
    rfl

theorem endpoint_bounds (A : Row R P n) (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    StoredArrayParameterAtoms.Bounds A B K :=
  ⟨h.initial,h.final,h.data,h.initial_arity,h.final_arity,h.data_arity⟩

def budget (n q T B K : Nat) := 12+StoredIdentityMarkers.budget n+
  StoredGuardedArrayPackage.budget n q T (B+3) K+StoredGuardedArrayPackage.budget n q T B K+
  StoredArrayParameterAtoms.initialBudget n B K+StoredArrayParameterAtoms.atomBudget (1+n*(8+2*B)) K+
  n+StoredArrayParameterAtoms.atomBudget B K

theorem bound (A : Row R P n) (seed last zero one : P) {a : Nat}
    (r : BlockRelationPresentation.Rel n a) (args : StoredRelationTuple.Data (Fin q) a) (positive : Bool)
    (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    (build A seed last zero one q T r args positive).2 ≤ budget n q T B K := by
  cases r with
  | block s t =>
    have ha := StoredIdentityMarkers.bound A
    have hb := duplicate_bound args
    have hf := StoredGuardedArrayPackage.bound (T := T) (StoredIdentityMarkers.build A).1 ⟨s,t,s,t⟩ last last false zero one
      (duplicate args).1 positive (B+3) K (StoredIdentityMarkers.preserves A B K h)
    simp only [build,budget]; omega
  | guarded e first =>
    have hf := StoredGuardedArrayPackage.bound (T := T) A e seed last first zero one args positive B K h
    simp only [build,budget]; omega
  | initial s =>
    have hf := StoredArrayParameterAtoms.initialPackage_bound (q := q) (T := T) A seed s positive B K (endpoint_bounds A B K h)
    simp only [build,budget]; omega
  | final s =>
    have hf := StoredArrayParameterAtoms.finalPackage_bound (q := q) (T := T) A s positive B K (endpoint_bounds A B K h)
    simp only [build,budget]; omega

def sizeBudget (n T B : Nat) := StoredGuardedArrayShape.sizeBudget n T (B+3)+
  StoredGuardedArrayShape.sizeBudget n T B+5+B+n*(8+2*B)
theorem shape (A : Row R P n) (seed last zero one : P) {a : Nat}
    (r : BlockRelationPresentation.Rel n a) (args : StoredRelationTuple.Data (Fin q) a) (positive : Bool)
    (B K : Nat) (h : StoredRowTransport.Bounds A B K) :
    StoredRelationalElimination.size (build A seed last zero one q T r args positive).1 ≤ sizeBudget n T B ∧
    arity (build A seed last zero one q T r args positive).1.body ≤ K := by
  cases r with
  | block s t =>
    have hs := StoredGuardedArrayPackage.shape (T := T) (StoredIdentityMarkers.build A).1 ⟨s,t,s,t⟩ last last false zero one
      (duplicate args).1 positive (B+3) K (StoredIdentityMarkers.preserves A B K h)
    exact ⟨by have := hs.1; simp only [build,sizeBudget]; omega,hs.2⟩
  | guarded e first =>
    have hs := StoredGuardedArrayPackage.shape (T := T) A e seed last first zero one args positive B K h
    exact ⟨by have := hs.1; simp only [build,sizeBudget]; omega,hs.2⟩
  | initial s =>
    have hs := StoredArrayParameterAtoms.initialPackage_shape (q := q) (T := T) A seed s positive B K (endpoint_bounds A B K h)
    exact ⟨by have := hs.1; simp only [build,sizeBudget]; omega,hs.2⟩
  | final s =>
    have hs := StoredArrayParameterAtoms.finalPackage_shape (q := q) (T := T) A s positive B K (endpoint_bounds A B K h)
    exact ⟨by have := hs.1; simp only [build,sizeBudget]; omega,hs.2⟩

theorem correct (A : Row R P n) (seed last zero one : P) {a : Nat}
    (r : BlockRelationPresentation.Rel n a) (args : StoredRelationTuple.Data (Fin q) a) (positive : Bool)
    {D : Type} [(UniformWordLowering.wordLanguage R).Structure D] (p : Params P q T → D) :
    Formula.Realize (build A seed last zero one q T r args positive).1.original.toFormula p ↔
      Formula.Realize (FiniteArrayBlockFormula.compile A.original seed last zero one q T r
        (fun i => (StoredRelationTuple.read args i).1) positive) p := by
  rw [value]
  exact ArrayAtomExistentialPackages.block_correct A.original A.qfree seed last zero one q T r _ positive p
end NSSE.StoredBlockArrayPackage
