import NSSE.ExistentialFormulaPackage

/-! # Explicit existential-prefix packages for the actual array atom compilers -/

namespace NSSE.ArrayAtomExistentialPackages

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks FiniteWordCoordinates
open ExistentialFormulaPackage ExactReachabilityTable ConvolutionShapes

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w} {n : Nat}

structure RowQF (R : Row L P n) : Prop extends ExactGuardedRunFormula.RowQF R where
  initial : ∀ s, (R.initial s).IsQF
  final : ∀ s, (R.final s).IsQF

def guarded (R : Row L P n) (h : ExactGuardedRunFormula.RowQF R)
    (e : Ends n) (seed last : P) (first : Bool) (zero one : P)
    (q T : Nat) (args : Fin 2 → Fin q) (positive : Bool) : Package L (Params P q T) := by
  let R' := RowParameterTransport.mapRow (Sum.inl : P → Params P q T) R
  let A := SkipEmptyColumns.automaton (R'.raw e (.inl seed) (.inl last) first)
  let fs := fun t i => flags zero q T t (args i)
  let ls := fun t i => letters zero q T t (args i)
  exact ⟨(T+1)*(states n).length,
    matrix A.initial (DynamicColumnRunFormula.steps A fs ls (.inl one)) (.inl one) T ⊓
      signed positive (output A.final (.inl one) T),
    DynamicColumnRunFormula.compileH_matrix_qf R' (FiniteArrayHFormula.mapRow_qf Sum.inl R h)
      e (.inl seed) (.inl last) first fs ls (.inl one) T positive⟩

theorem guarded_formula (R : Row L P n) (h : ExactGuardedRunFormula.RowQF R)
    (e : Ends n) (seed last : P) (first : Bool) (zero one : P)
    (q T : Nat) (args : Fin 2 → Fin q) (positive : Bool) :
    (guarded R h e seed last first zero one q T args positive).toFormula =
      FiniteArrayHFormula.compile R e seed last first zero one q T args positive := rfl

theorem identity_qf (R : Row L P n) (h : ExactGuardedRunFormula.RowQF R) :
    ExactGuardedRunFormula.RowQF (BlockRelationPresentation.identityMarkers R) := by
  constructor
  · exact h.data
  · intro s t
    change (BlockRelationPresentation.identityGuard (L := L) (P := P) s t).IsQF
    unfold BlockRelationPresentation.identityGuard
    split
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot
  · intro s t
    change (BlockRelationPresentation.identityGuard (L := L) (P := P) s t).IsQF
    unfold BlockRelationPresentation.identityGuard
    split
    · exact BoundedFormula.IsQF.top
    · exact BoundedFormula.isQF_bot
  · exact BoundedFormula.IsQF.top

theorem initial_qf (R : Row L P n) (h : RowQF R) (seed : P) (s : Fin n) :
    (BlockRelationPresentation.initialFormula R seed s).IsQF := by
  apply any_qf
  intro z
  exact (h.initial z).inf (relabel_qf _ (h.data z s) _)

def block (R : Row L P n) (h : RowQF R) (seed last zero one : P) (q T : Nat) :
    {a : Nat} → BlockRelationPresentation.Rel n a → (Fin a → Fin q) → Bool → Package L (Params P q T)
  | _, .block s t, args, positive => guarded (BlockRelationPresentation.identityMarkers R)
      (identity_qf R h.toRowQF) ⟨s,t,s,t⟩ last last false zero one q T (fun _ => args 0) positive
  | _, .guarded e first, args, positive => guarded R h.toRowQF e seed last first zero one q T args positive
  | _, .initial s, _, positive => Package.atom (signed positive ((BlockRelationPresentation.initialFormula R seed s).relabel Sum.inl))
      (signed_qf _ _ (relabel_qf _ (initial_qf R h seed s) _))
  | _, .final s, _, positive => Package.atom (signed positive ((R.final s).relabel Sum.inl))
      (signed_qf _ _ (relabel_qf _ (h.final s) _))

theorem block_correct (R : Row L P n) (h : RowQF R) (seed last zero one : P) (q T : Nat)
    {a : Nat} (r : BlockRelationPresentation.Rel n a) (args : Fin a → Fin q) (positive : Bool)
    {D : Type*} [L.Structure D] (p : Params P q T → D) :
    (block R h seed last zero one q T r args positive).toFormula.Realize p ↔
      (FiniteArrayBlockFormula.compile R seed last zero one q T r args positive).Realize p := by
  cases r with
  | block s t => rfl
  | guarded e first => rfl
  | initial s => exact Package.atom_correct p _ (signed_qf _ _ (relabel_qf _ (initial_qf R h seed s) _))
  | final s => exact Package.atom_correct p _ (signed_qf _ _ (relabel_qf _ (h.final s) _))

def relation {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) (q T : Nat) :
    {a : Nat} → UnifiedBlockPresentation.Rel ns c a → (Fin a → Fin q) → Bool → Package L (Params P q T)
  | _, .row i r, args, positive => block (rows i) (hr i) seed last zero one q T r args positive
  | _, .candidate r, args, positive => block C hc seed last zero one q T r args positive
  | _, .noA, args, positive => Package.atom (FiniteArrayAbsenceFormula.compile last zero one q T (args 0) positive)
      (signed_qf _ _ (FiniteArrayAbsenceFormula.matrix_qf _ _ _ _ _ _))

theorem relation_correct {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (hr : ∀ i, RowQF (rows i)) (hc : RowQF C) (seed last zero one : P) (q T : Nat)
    {a : Nat} (r : UnifiedBlockPresentation.Rel ns c a) (args : Fin a → Fin q) (positive : Bool)
    {D : Type*} [L.Structure D] (p : Params P q T → D) :
    (relation rows C hr hc seed last zero one q T r args positive).toFormula.Realize p ↔
      (FiniteArrayRelationCompiler.compile rows C seed last zero one q T r args positive).Realize p := by
  cases r with
  | row i r => exact block_correct (rows i) (hr i) seed last zero one q T r args positive p
  | candidate r => exact block_correct C hc seed last zero one q T r args positive p
  | noA => exact Package.atom_correct p _ (signed_qf _ _ (FiniteArrayAbsenceFormula.matrix_qf _ _ _ _ _ _))

def equality (zero one : P) (q T : Nat) (i j : Fin q) (positive : Bool) : Package L (Params P q T) :=
  Package.atom (FiniteArrayEqualityFormula.compile zero one q T i j positive)
    (signed_qf _ _ (FiniteArrayEqualityFormula.matrix_qf _ _ _ _ _ _))

theorem equality_correct (zero one : P) (q T : Nat) (i j : Fin q) (positive : Bool)
    {D : Type*} [L.Structure D] (p : Params P q T → D) :
    (equality (L := L) zero one q T i j positive).toFormula.Realize p ↔
      (FiniteArrayEqualityFormula.compile (L := L) zero one q T i j positive).Realize p :=
  Package.atom_correct p _ (signed_qf _ _ (FiniteArrayEqualityFormula.matrix_qf _ _ _ _ _ _))

end NSSE.ArrayAtomExistentialPackages
