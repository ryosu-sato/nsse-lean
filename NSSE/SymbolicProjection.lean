import NSSE.SymbolicComplement

/-!
# Exact symbolic projection, including erased columns and hidden tails

A finite projection plan either erases a column shape or selects the visible
coordinates of that shape. The compiler existentially binds old current
letters, not the shared parameters, and turns fully hidden columns into
silent edges. It preserves the exact homomorphic image of ALL accepted words.
-/

namespace NSSE.SymbolicProjection

open FirstOrder FirstOrder.Language SymbolicReachability SymbolicAutomata

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w}

/-- Existential image of one column guard under a coordinate map. All old
letters are bound; the visible coordinates are equated to their selected values. -/
def projectGuard {a b : Nat} (pick : Fin b → Fin a)
    (f : L.Formula (P ⊕ Fin a)) : L.Formula (P ⊕ Fin b) :=
  closeColumn (f.relabel (Sum.map Sum.inl id) ⊓
    SymbolicComplement.all b (fun j => Term.equal
      (Term.var (Sum.inl (Sum.inr j))) (Term.var (Sum.inr (pick j)))))

theorem realize_projectGuard {D : Type*} [L.Structure D]
    (p : P → D) {a b : Nat} (pick : Fin b → Fin a)
    (f : L.Formula (P ⊕ Fin a)) (ys : Fin b → D) :
    (projectGuard pick f).Realize (Sum.elim p ys) ↔
      ∃ xs : Fin a → D, f.Realize (Sum.elim p xs) ∧ ys = xs ∘ pick := by
  simp only [projectGuard, realize_closeColumn, Formula.realize_inf,
    Formula.realize_relabel, SymbolicComplement.realize_all,
    Formula.realize_equal, Term.realize_var, Sum.elim_inl, Sum.elim_inr]
  apply exists_congr
  intro xs
  have hv : Sum.elim (Sum.elim p ys) xs ∘ Sum.map Sum.inl id = Sum.elim p xs := by
    funext z
    cases z <;> rfl
  rw [hv]
  exact and_congr_right (fun _ => ⟨fun h => funext h, fun h => congrFun h⟩)

/-- One shape is hidden entirely, or retained with explicitly selected coordinates. -/
inductive Action {m' : Nat} (arity' : Fin m' → Nat) (k : Nat)
  | erase : Action arity' k
  | keep (target : Fin m') (pick : Fin (arity' target) → Fin k) : Action arity' k

abbrev Plan {m m' : Nat} (arity : Fin m → Nat) (arity' : Fin m' → Nat) :=
  (s : Fin m) → Action arity' (arity s)

namespace Action

variable {m' k : Nat} {arity' : Fin m' → Nat}

def map (act : Action arity' k) {D : Type*} (xs : Fin k → D) : Option (Column D arity') :=
  match act with
  | .erase => none
  | .keep t pick => some ⟨t, xs ∘ pick⟩

def silentGuard (act : Action arity' k) (f : L.Formula (P ⊕ Fin k)) : L.Formula P :=
  match act with
  | .erase => closeColumn f
  | .keep _ _ => ⊥

def dataGuard (act : Action arity' k) (f : L.Formula (P ⊕ Fin k))
    (t : Fin m') : L.Formula (P ⊕ Fin (arity' t)) :=
  match act with
  | .erase => ⊥
  | .keep target pick => if h : target = t then h ▸ projectGuard pick f else ⊥

theorem realize_silentGuard (act : Action arity' k) (f : L.Formula (P ⊕ Fin k))
    {D : Type*} [L.Structure D] (p : P → D) :
    (act.silentGuard f).Realize p ↔
      ∃ xs : Fin k → D, act.map xs = none ∧ f.Realize (Sum.elim p xs) := by
  cases act <;> simp [silentGuard, map, realize_closeColumn]

theorem realize_dataGuard (act : Action arity' k) (f : L.Formula (P ⊕ Fin k))
    {D : Type*} [L.Structure D] (p : P → D) (c : Column D arity') :
    (act.dataGuard f c.1).Realize (Sum.elim p c.2) ↔
      ∃ xs : Fin k → D, act.map xs = some c ∧ f.Realize (Sum.elim p xs) := by
  rcases c with ⟨t, ys⟩
  cases act with
  | erase => simp [dataGuard, map]
  | keep target pick =>
      by_cases h : target = t
      · subst t
        simp only [dataGuard, ↓reduceDIte, realize_projectGuard, map, Option.some.injEq,
          Sigma.mk.inj_iff, heq_eq_eq, true_and]
        apply exists_congr
        intro xs
        exact ⟨fun ⟨hf, hy⟩ => ⟨hy.symm, hf⟩, fun ⟨hy, hf⟩ => ⟨hf, hy.symm⟩⟩
      · simp [dataGuard, h, map, Sigma.mk.inj_iff]

end Action

variable {n m m' : Nat} {arity : Fin m → Nat} {arity' : Fin m' → Nat}

def mapColumn (plan : Plan arity arity') {D : Type*} (c : Column D arity) :
    Option (Column D arity') := (plan c.1).map c.2

def mapTraceLetter (plan : Plan arity arity') {D : Type*} :
    Option (Column D arity) → Option (Column D arity')
  | none => none
  | some c => mapColumn plan c

def compile (plan : Plan arity arity') (A : Automaton L P n m arity) :
    Automaton L P n m' arity' where
  initial := A.initial
  final := A.final
  silent q r := A.silent q r ⊔ any m (fun s => (plan s).silentGuard (A.step s q r))
  step t q r := any m (fun s => (plan s).dataGuard (A.step s q r) t)

theorem compile_step (plan : Plan arity arity') (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) (q r : Fin n)
    (b : Option (Column D arity')) :
    ((compile plan A).interpret p).step q b r ↔
      ∃ a, mapTraceLetter plan a = b ∧ (A.interpret p).step q a r := by
  cases b with
  | none =>
      change (A.silent q r ⊔ any m (fun s =>
        (plan s).silentGuard (A.step s q r))).Realize p ↔ _
      simp only [Formula.realize_sup, realize_any, Action.realize_silentGuard]
      constructor
      · rintro (h | ⟨s, xs, he, h⟩)
        · exact ⟨none, rfl, h⟩
        · exact ⟨some ⟨s, xs⟩, he, h⟩
      · rintro ⟨a, he, h⟩
        rcases a with _ | ⟨s, xs⟩
        · exact Or.inl h
        · exact Or.inr ⟨s, xs, he, h⟩
  | some c =>
      change (any m _).Realize (Sum.elim p c.2) ↔ _
      simp only [realize_any, Action.realize_dataGuard]
      constructor
      · rintro ⟨s, xs, he, h⟩
        exact ⟨some ⟨s, xs⟩, he, h⟩
      · rintro ⟨a, he, h⟩
        rcases a with _ | ⟨s, xs⟩
        · cases he
        · exact ⟨s, xs, he, h⟩

section TraceImages

variable {α β Q : Type*}

def imageNFA (A : NSSE.NFA α Q) (f : α → β) : NSSE.NFA β Q where
  start := A.start
  accept := A.accept
  step q b r := ∃ a, f a = b ∧ A.step q a r

theorem image_run (A : NSSE.NFA α Q) (f : α → β) {q r : Q} {w : List α}
    (h : A.Runs q w r) : (imageNFA A f).Runs q (w.map f) r := by
  induction h with
  | nil q => exact .nil q
  | @cons q r s a w ha _ ih => exact .cons ⟨a, rfl, ha⟩ ih

theorem image_run_iff (A : NSSE.NFA α Q) (f : α → β) (q r : Q) (w : List β) :
    (imageNFA A f).Runs q w r ↔ ∃ v, v.map f = w ∧ A.Runs q v r := by
  constructor
  · intro h
    induction h with
    | nil q => exact ⟨[], rfl, .nil q⟩
    | @cons q r s b w hb _ ih =>
        obtain ⟨a, rfl, ha⟩ := hb
        obtain ⟨v, rfl, hv⟩ := ih
        exact ⟨a :: v, rfl, .cons ha hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact image_run A f hv

theorem image_accepts (A : NSSE.NFA α Q) (f : α → β) (w : List β) :
    (imageNFA A f).Accepts w ↔ ∃ v, v.map f = w ∧ A.Accepts v := by
  constructor
  · rintro ⟨q, r, hq, hr, hf⟩
    obtain ⟨v, rfl, hv⟩ := (image_run_iff A f q r w).mp hr
    exact ⟨v, rfl, q, r, hq, hv, hf⟩
  · rintro ⟨v, rfl, q, r, hq, hr, hf⟩
    exact ⟨q, r, hq, image_run A f hr, hf⟩

end TraceImages

theorem compile_interpret (plan : Plan arity arity') (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) :
    (compile plan A).interpret p = imageNFA (A.interpret p) (mapTraceLetter plan) := by
  unfold Automaton.interpret imageNFA
  congr 1
  funext q b r
  exact propext (compile_step plan A p q r b)

theorem erase_mapTrace (plan : Plan arity arity') {D : Type*}
    (trace : List (Option (Column D arity))) :
    (trace.map (mapTraceLetter plan)).filterMap id =
      (trace.filterMap id).filterMap (mapColumn plan) := by
  induction trace with
  | nil => rfl
  | cons a trace ih =>
      cases a with
      | none => simpa [mapTraceLetter] using ih
      | some c =>
          cases h : mapColumn plan c <;> simp [mapTraceLetter, h, ih]

/-- Exact existential image of the entire accepted language. No length
comparison between hidden and visible words is a premise. -/
theorem compile_correct (plan : Plan arity arity') (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) (w : List (Column D arity')) :
    (compile plan A).Accepts p w ↔
      ∃ v, A.Accepts p v ∧ v.filterMap (mapColumn plan) = w := by
  unfold Automaton.Accepts
  rw [compile_interpret]
  constructor
  · rintro ⟨trace, he, ha⟩
    obtain ⟨old, rfl, hold⟩ := (image_accepts (A.interpret p) (mapTraceLetter plan) trace).mp ha
    exact ⟨old.filterMap id, ⟨old, rfl, hold⟩, (erase_mapTrace plan old).symm.trans he⟩
  · rintro ⟨v, ⟨old, rfl, hold⟩, he⟩
    refine ⟨old.map (mapTraceLetter plan), (erase_mapTrace plan old).trans he, ?_⟩
    exact (image_accepts (A.interpret p) (mapTraceLetter plan) _).mpr ⟨old, rfl, hold⟩

theorem nonemptyFormula_correct (plan : Plan arity arity') (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) :
    (compile plan A).nonemptyFormula.Realize p ↔ A.nonemptyFormula.Realize p := by
  rw [Automaton.realize_nonemptyFormula, Automaton.realize_nonemptyFormula]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, _⟩ := (compile_correct plan A p w).mp hw
    exact ⟨v, hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v.filterMap (mapColumn plan), (compile_correct plan A p _).mpr ⟨v, hv, rfl⟩⟩

/-- Project away every tape/column. The result has no data-column shapes. -/
def forgetAll (A : Automaton L P n m arity) : Automaton L P n 0 Fin.elim0 :=
  compile (fun _ => .erase) A

/-- All hidden words, of arbitrary length, contribute to the EMPTY visible
word through epsilon paths; they are not dropped by a zero-tape special case. -/
theorem forgetAll_correct (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) :
    (forgetAll A).Accepts p [] ↔ ∃ v, A.Accepts p v := by
  rw [forgetAll, compile_correct]
  simp [mapColumn, Action.map]

end NSSE.SymbolicProjection
