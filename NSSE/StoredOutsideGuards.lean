import NSSE.StoredOutsideStates

/-! Actual outside-controller labels as stored formulas of the unified block
language.  Every label is a constant-size Boolean combination of one row atom,
so each construction cost and each formula size is an absolute constant. -/
namespace NSSE.StoredOutsideGuards
open FirstOrder FirstOrder.Language StoredRelationalFormula
open SymbolicGuardedBlocks SymbolicOutsideController
variable {k c : Nat} (ns : Fin k → Nat) (i : Fin k)

abbrev Hom (ns : Fin k → Nat) (c : Nat) (i : Fin k) := UnifiedBlockPresentation.rowHom ns c i

def blockAtom (q r : Fin (ns i)) : Data (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) 0 :=
  .rel (.row i (.block q r)) ⟨[.inl (.inr 0)],rfl⟩
def initialAtom (q : Fin (ns i)) : Data (UnifiedBlockPresentation.Rel ns c) Empty 0 :=
  .rel (.row i (.initial q)) ⟨[],rfl⟩
def finalAtom (q : Fin (ns i)) : Data (UnifiedBlockPresentation.Rel ns c) Empty 0 :=
  .rel (.row i (.final q)) ⟨[],rfl⟩
def guardAtom (e : Ends (ns i)) (first : Bool) :
    Data (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 2) 0 :=
  .rel (.row i (.guarded e first)) ⟨[.inl (.inr 0),.inl (.inr 1)],rfl⟩

theorem blockAtom_value (q r : Fin (ns i)) : denote (blockAtom ns (c := c) i q r) =
    (Hom ns c i).onFormula (SymbolicOutsideController.blockAtom q r) := by
  change BoundedFormula.rel _ _ = BoundedFormula.rel _ _
  congr 1
  funext j; fin_cases j; rfl
theorem initialAtom_value (q : Fin (ns i)) : denote (initialAtom ns (c := c) i q) =
    (Hom ns c i).onFormula (SymbolicOutsideController.initialAtom q) := by
  change BoundedFormula.rel _ _ = BoundedFormula.rel _ _
  congr 1
  funext j; exact j.elim0
theorem finalAtom_value (q : Fin (ns i)) : denote (finalAtom ns (c := c) i q) =
    (Hom ns c i).onFormula (SymbolicOutsideController.finalAtom q) := by
  change BoundedFormula.rel _ _ = BoundedFormula.rel _ _
  congr 1
  funext j; exact j.elim0
theorem guardAtom_value (e : Ends (ns i)) (first : Bool) :
    denote (guardAtom ns (c := c) i e first) =
      (Hom ns c i).onFormula (SymbolicOutsideController.guardAtom e first) := by
  change BoundedFormula.rel _ _ = BoundedFormula.rel _ _
  congr 1
  funext j; fin_cases j <;> rfl

/-- The stored form of a decided constant test. -/
def flag {P : Type} (h : Prop) [Decidable h] :
    Data (UnifiedBlockPresentation.Rel ns c) P 0 × Nat :=
  (if h then .imp .falsum .falsum else .falsum,3)

theorem flag_value {P : Type} (h : Prop) [Decidable h] :
    denote (flag ns (c := c) (P := P) h).1 =
      (Hom ns c i).onFormula (SymbolicOutsideController.test (n := ns i) (X := P) h) := by
  by_cases hh : h
  · simp only [flag,SymbolicOutsideController.test,if_pos hh]; rfl
  · simp only [flag,SymbolicOutsideController.test,if_neg hh]; rfl

theorem flag_nodes {P : Type} (h : Prop) [Decidable h] :
    nodes (flag ns (c := c) (P := P) h).1 ≤ 3 := by
  simp only [flag]; split <;> simp only [nodes] <;> omega
theorem flag_arity {P : Type} (h : Prop) [Decidable h] :
    arity (flag ns (c := c) (P := P) h).1 = 0 := by
  simp only [flag]
  split
  · simp only [arity]; omega
  · simp only [arity]

def initial : ControlState (ns i) → Data (UnifiedBlockPresentation.Rel ns c) Empty 0 × Nat
  | .before b q =>
      let a := flag ns (c := c) (b = true)
      (StoredArrayEquality.conj a.1 (initialAtom ns i q),9+a.2)
  | _ => (.falsum,3)

def final : ControlState (ns i) → Data (UnifiedBlockPresentation.Rel ns c) Empty 0 × Nat
  | .after q => (finalAtom ns i q,4)
  | _ => (.falsum,3)

def data (e : Ends (ns i)) (first : Bool) :
    ControlState (ns i) → ControlState (ns i) →
      Data (UnifiedBlockPresentation.Rel ns c) (Empty ⊕ Fin 1) 0 × Nat
  | .before _ q, .before b r =>
      let a := flag ns (c := c) (b = false)
      (StoredArrayEquality.conj a.1 (blockAtom ns i q r),9+a.2)
  | .before b q, .waitLeft =>
      let a := flag ns (c := c) (q = e.leftStart ∧ b = first)
      (a.1,1+a.2)
  | .middle q, .middle r => (blockAtom ns i q r,4)
  | .middle q, .waitRight =>
      let a := flag ns (c := c) (q = e.rightStart)
      (a.1,1+a.2)
  | .after q, .after r => (blockAtom ns i q r,4)
  | _, _ => (.falsum,3)

def left (e : Ends (ns i)) :
    ControlState (ns i) → ControlState (ns i) →
      Data (UnifiedBlockPresentation.Rel ns c) Empty 0 × Nat
  | .waitLeft, .middle r => let a := flag ns (c := c) (r = e.leftEnd); (a.1,1+a.2)
  | _, _ => (.falsum,3)

def right (e : Ends (ns i)) :
    ControlState (ns i) → ControlState (ns i) →
      Data (UnifiedBlockPresentation.Rel ns c) Empty 0 × Nat
  | .waitRight, .after r => let a := flag ns (c := c) (r = e.rightEnd); (a.1,1+a.2)
  | _, _ => (.falsum,3)

theorem initial_value (s : ControlState (ns i)) : denote (initial ns (c := c) i s).1 =
    (Hom ns c i).onFormula (SymbolicOutsideController.initialGuard s) := by
  cases s with
  | before b q =>
      change denote (StoredArrayEquality.conj (flag ns (c := c) (b = true)).1 (initialAtom ns i q)) = _
      simp only [StoredArrayEquality.conj,denote,flag_value ns i,initialAtom_value ns i,
        SymbolicOutsideController.initialGuard]
      rfl
  | _ => rfl

theorem final_value (s : ControlState (ns i)) : denote (final ns (c := c) i s).1 =
    (Hom ns c i).onFormula (SymbolicOutsideController.finalGuard s) := by
  cases s with
  | after q => exact finalAtom_value ns i q
  | _ => rfl

theorem data_value (e : Ends (ns i)) (first : Bool) (s t : ControlState (ns i)) :
    denote (data ns (c := c) i e first s t).1 =
      (Hom ns c i).onFormula (SymbolicOutsideController.dataGuard e first s t) := by
  cases s <;> cases t <;>
    simp only [data,StoredArrayEquality.conj,denote,flag_value ns i,blockAtom_value ns i,
      SymbolicOutsideController.dataGuard]
  all_goals rfl

theorem left_value (e : Ends (ns i)) (s t : ControlState (ns i)) :
    denote (left ns (c := c) i e s t).1 =
      (Hom ns c i).onFormula (SymbolicOutsideController.leftGuard e s t) := by
  cases s <;> cases t <;>
    simp only [left,flag_value ns i,SymbolicOutsideController.leftGuard]
  all_goals rfl

theorem right_value (e : Ends (ns i)) (s t : ControlState (ns i)) :
    denote (right ns (c := c) i e s t).1 =
      (Hom ns c i).onFormula (SymbolicOutsideController.rightGuard e s t) := by
  cases s <;> cases t <;>
    simp only [right,flag_value ns i,SymbolicOutsideController.rightGuard]
  all_goals rfl

/-- Every stored label costs at most a fixed constant number of steps. -/
def budget : Nat := 12
/-- Every stored label has at most nine syntax nodes. -/
def sizeBudget : Nat := 9

theorem initial_bound (s : ControlState (ns i)) : (initial ns (c := c) i s).2 ≤ budget := by
  cases s <;> simp only [initial,flag,budget] <;> omega
theorem final_bound (s : ControlState (ns i)) : (final ns (c := c) i s).2 ≤ budget := by
  cases s <;> simp only [final,budget] <;> omega
theorem data_bound (e : Ends (ns i)) (first : Bool) (s t : ControlState (ns i)) :
    (data ns (c := c) i e first s t).2 ≤ budget := by
  cases s <;> cases t <;> simp only [data,flag,budget] <;> omega
theorem left_bound (e : Ends (ns i)) (s t : ControlState (ns i)) :
    (left ns (c := c) i e s t).2 ≤ budget := by
  cases s <;> cases t <;> simp only [left,flag,budget] <;> omega
theorem right_bound (e : Ends (ns i)) (s t : ControlState (ns i)) :
    (right ns (c := c) i e s t).2 ≤ budget := by
  cases s <;> cases t <;> simp only [right,flag,budget] <;> omega

theorem initial_shape (s : ControlState (ns i)) :
    nodes (initial ns (c := c) i s).1 ≤ sizeBudget ∧ arity (initial ns (c := c) i s).1 ≤ 2 := by
  constructor <;> cases s <;>
    simp only [initial,StoredArrayEquality.conj,initialAtom,flag,sizeBudget] <;>
    first | (split <;> simp only [nodes,arity] <;> omega) | (simp only [nodes,arity]; omega)
theorem final_shape (s : ControlState (ns i)) :
    nodes (final ns (c := c) i s).1 ≤ sizeBudget ∧ arity (final ns (c := c) i s).1 ≤ 2 := by
  constructor <;> cases s <;>
    simp only [final,finalAtom,sizeBudget,nodes,arity] <;> omega
theorem data_shape (e : Ends (ns i)) (first : Bool) (s t : ControlState (ns i)) :
    nodes (data ns (c := c) i e first s t).1 ≤ sizeBudget ∧
      arity (data ns (c := c) i e first s t).1 ≤ 2 := by
  constructor <;> cases s <;> cases t <;>
    simp only [data,StoredArrayEquality.conj,blockAtom,flag,sizeBudget] <;>
    first | (split <;> simp only [nodes,arity] <;> omega) | (simp only [nodes,arity]; omega)
theorem left_shape (e : Ends (ns i)) (s t : ControlState (ns i)) :
    nodes (left ns (c := c) i e s t).1 ≤ sizeBudget ∧ arity (left ns (c := c) i e s t).1 ≤ 2 := by
  constructor <;> cases s <;> cases t <;>
    simp only [left,flag,sizeBudget] <;>
    first | (split <;> simp only [nodes,arity] <;> omega) | (simp only [nodes,arity]; omega)
theorem right_shape (e : Ends (ns i)) (s t : ControlState (ns i)) :
    nodes (right ns (c := c) i e s t).1 ≤ sizeBudget ∧ arity (right ns (c := c) i e s t).1 ≤ 2 := by
  constructor <;> cases s <;> cases t <;>
    simp only [right,flag,sizeBudget] <;>
    first | (split <;> simp only [nodes,arity] <;> omega) | (simp only [nodes,arity]; omega)
theorem guardAtom_shape (e : Ends (ns i)) (first : Bool) :
    nodes (guardAtom ns (c := c) i e first) ≤ sizeBudget ∧
      arity (guardAtom ns (c := c) i e first) ≤ 2 := by
  simp only [guardAtom,nodes,arity,sizeBudget]; exact ⟨by omega,le_rfl⟩

theorem initial_qf (e : Ends (ns i)) (first : Bool) (s : ControlState (ns i)) :
    (denote (initial ns (c := c) i s).1).IsQF := by
  rw [initial_value]
  obtain ⟨j,hj⟩ := SymbolicOutsideController.stateAt_surjective (ns i) s
  simpa only [SymbolicOutsideController.compile,hj] using
    RankNextQuantifierFree.onFormula_qf (Hom ns c i) _
      ((RankNextQuantifierFree.outside_qf e first).initial j)
theorem final_qf (e : Ends (ns i)) (first : Bool) (s : ControlState (ns i)) :
    (denote (final ns (c := c) i s).1).IsQF := by
  rw [final_value]
  obtain ⟨j,hj⟩ := SymbolicOutsideController.stateAt_surjective (ns i) s
  simpa only [SymbolicOutsideController.compile,hj] using
    RankNextQuantifierFree.onFormula_qf (Hom ns c i) _
      ((RankNextQuantifierFree.outside_qf e first).final j)
theorem data_qf (e : Ends (ns i)) (first : Bool) (s t : ControlState (ns i)) :
    (denote (data ns (c := c) i e first s t).1).IsQF := by
  rw [data_value]
  obtain ⟨j,hj⟩ := SymbolicOutsideController.stateAt_surjective (ns i) s
  obtain ⟨l,hl⟩ := SymbolicOutsideController.stateAt_surjective (ns i) t
  simpa only [SymbolicOutsideController.compile,hj,hl] using
    RankNextQuantifierFree.onFormula_qf (Hom ns c i) _
      ((RankNextQuantifierFree.outside_qf e first).data j l)
theorem left_qf (e : Ends (ns i)) (first : Bool) (s t : ControlState (ns i)) :
    (denote (left ns (c := c) i e s t).1).IsQF := by
  rw [left_value]
  obtain ⟨j,hj⟩ := SymbolicOutsideController.stateAt_surjective (ns i) s
  obtain ⟨l,hl⟩ := SymbolicOutsideController.stateAt_surjective (ns i) t
  simpa only [SymbolicOutsideController.compile,hj,hl] using
    RankNextQuantifierFree.onFormula_qf (Hom ns c i) _
      ((RankNextQuantifierFree.outside_qf e first).left j l)
theorem right_qf (e : Ends (ns i)) (first : Bool) (s t : ControlState (ns i)) :
    (denote (right ns (c := c) i e s t).1).IsQF := by
  rw [right_value]
  obtain ⟨j,hj⟩ := SymbolicOutsideController.stateAt_surjective (ns i) s
  obtain ⟨l,hl⟩ := SymbolicOutsideController.stateAt_surjective (ns i) t
  simpa only [SymbolicOutsideController.compile,hj,hl] using
    RankNextQuantifierFree.onFormula_qf (Hom ns c i) _
      ((RankNextQuantifierFree.outside_qf e first).right j l)
theorem guard_qf (e : Ends (ns i)) (first : Bool) :
    (denote (guardAtom ns (c := c) i e first)).IsQF := by
  rw [guardAtom_value]
  exact RankNextQuantifierFree.onFormula_qf (Hom ns c i) _
    (RankNextQuantifierFree.outside_qf e first).guard
end NSSE.StoredOutsideGuards
