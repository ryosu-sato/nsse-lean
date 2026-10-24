import NSSE.Automata
import NSSE.SymbolicReachability

/-!
# Symbolic automata: shared-parameter nonemptiness and epsilon elimination

States and column shapes are explicitly numbered. Each shape specifies its
number of current letters; its guard is real first-order syntax with those
letters and a fixed tuple of free parameters. Initial, final, and silent
transitions have parameter-only guards. Structures may be infinite.
-/

namespace NSSE.SymbolicAutomata

open FirstOrder FirstOrder.Language SymbolicReachability

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w}

structure Automaton (L : FirstOrder.Language.{u, v}) (P : Type w)
    (n m : Nat) (arity : Fin m → Nat) where
  initial : Fin n → L.Formula P
  final : Fin n → L.Formula P
  silent : Fin n → Fin n → L.Formula P
  step : (s : Fin m) → Fin n → Fin n → L.Formula (P ⊕ Fin (arity s))

abbrev Column (D : Type*) {m : Nat} (arity : Fin m → Nat) :=
  (s : Fin m) × (Fin (arity s) → D)

variable {n m : Nat} {arity : Fin m → Nat}

namespace Automaton

def interpret (A : Automaton L P n m arity) {D : Type*} [L.Structure D]
    (p : P → D) : NSSE.NFA (Option (Column D arity)) (Fin n) where
  start q := (A.initial q).Realize p
  accept q := (A.final q).Realize p
  step q a r := match a with
    | none => (A.silent q r).Realize p
    | some ⟨s, xs⟩ => (A.step s q r).Realize (Sum.elim p xs)

/-- A trace records silent edges explicitly; its visible word erases them. -/
def Accepts (A : Automaton L P n m arity) {D : Type*} [L.Structure D]
    (p : P → D) (w : List (Column D arity)) : Prop :=
  ∃ trace, trace.filterMap id = w ∧ (A.interpret p).Accepts trace

/-- Existentially close only CURRENT letters; the parameters P stay free. -/
def edge (A : Automaton L P n m arity) (q r : Fin n) : L.Formula P :=
  A.silent q r ⊔ any m (fun s => closeColumn (A.step s q r))

def nonemptyFormula (A : Automaton L P n m arity) : L.Formula P :=
  any n (fun q => any n (fun r =>
    A.initial q ⊓ (reach A.edge q r ⊓ A.final r)))

theorem realize_edge (A : Automaton L P n m arity) {D : Type*} [L.Structure D]
    (p : P → D) (q r : Fin n) :
    (A.edge q r).Realize p ↔ ∃ a, (A.interpret p).step q a r := by
  simp only [edge, Formula.realize_sup, realize_any, realize_closeColumn]
  constructor
  · rintro (h | ⟨s, xs, h⟩)
    · exact ⟨none, h⟩
    · exact ⟨some ⟨s, xs⟩, h⟩
  · rintro ⟨a, h⟩
    rcases a with _ | ⟨s, xs⟩
    · exact Or.inl h
    · exact Or.inr ⟨s, xs, h⟩

end Automaton

section Paths

variable {α Q : Type*}

theorem exists_run_iff (A : NSSE.NFA α Q) (q r : Q) :
    (∃ w, A.Runs q w r) ↔
      Relation.ReflTransGen (fun a b => ∃ x, A.step a x b) q r := by
  constructor
  · rintro ⟨w, h⟩
    induction h with
    | nil => exact .refl
    | @cons q r s a w hstep _ ih => exact .head ⟨a, hstep⟩ ih
  · intro h
    induction h with
    | refl => exact ⟨[], .nil q⟩
    | @tail r s _ hstep ih =>
        obtain ⟨w, hw⟩ := ih
        obtain ⟨a, ha⟩ := hstep
        exact ⟨w ++ [a], hw.append A (.cons ha (.nil s))⟩

def Silent (A : NSSE.NFA (Option α) Q) (q r : Q) : Prop :=
  Relation.ReflTransGen (fun a b => A.step a none b) q r

theorem silent_trace (A : NSSE.NFA (Option α) Q) {q r : Q}
    (h : Silent A q r) :
    ∃ trace, trace.filterMap id = [] ∧ A.Runs q trace r := by
  induction h with
  | refl => exact ⟨[], rfl, .nil q⟩
  | @tail r s _ hrs ih =>
      obtain ⟨trace, he, hr⟩ := ih
      refine ⟨trace ++ [none], ?_, hr.append A (.cons hrs (.nil s))⟩
      simp [List.filterMap_append, he]

/-- Semantic normalization: initial silent closure, then a letter followed
by silent closure. The formula construction below realizes this automaton. -/
def normalize (A : NSSE.NFA (Option α) Q) : NSSE.NFA α Q where
  start q := ∃ r, A.start r ∧ Silent A r q
  accept := A.accept
  step q a r := ∃ s, A.step q (some a) s ∧ Silent A s r

theorem normalize_run_of_trace (A : NSSE.NFA (Option α) Q)
    {q r : Q} {trace : List (Option α)} (h : A.Runs q trace r) :
    ∃ s, Silent A q s ∧ (normalize A).Runs s (trace.filterMap id) r := by
  induction h with
  | nil q => exact ⟨q, .refl, .nil q⟩
  | @cons q r s a trace hstep _ ih =>
      obtain ⟨t, hrt, hrun⟩ := ih
      cases a with
      | none => exact ⟨t, .head hstep hrt, hrun⟩
      | some a => exact ⟨q, .refl, .cons ⟨r, hstep, hrt⟩ hrun⟩

theorem trace_of_normalize_run (A : NSSE.NFA (Option α) Q)
    {q r : Q} {w : List α} (h : (normalize A).Runs q w r) :
    ∃ trace, trace.filterMap id = w ∧ A.Runs q trace r := by
  induction h with
  | nil q => exact ⟨[], rfl, .nil q⟩
  | @cons q r s a w hstep _ ih =>
      obtain ⟨t, hqt, htr⟩ := hstep
      obtain ⟨eps, heps, hreps⟩ := silent_trace A htr
      obtain ⟨rest, hrest, hrrest⟩ := ih
      refine ⟨some a :: (eps ++ rest), ?_, .cons hqt (hreps.append A hrrest)⟩
      simp [List.filterMap_append, heps, hrest]

theorem normalize_accepts_iff (A : NSSE.NFA (Option α) Q) (w : List α) :
    (normalize A).Accepts w ↔
      ∃ trace, trace.filterMap id = w ∧ A.Accepts trace := by
  constructor
  · rintro ⟨q, r, ⟨s, hs, hsq⟩, hrun, hr⟩
    obtain ⟨eps, heps, hreps⟩ := silent_trace A hsq
    obtain ⟨rest, hrest, hrrest⟩ := trace_of_normalize_run A hrun
    refine ⟨eps ++ rest, ?_, s, r, hs, hreps.append A hrrest, hr⟩
    simp [List.filterMap_append, heps, hrest]
  · rintro ⟨trace, rfl, q, r, hq, hrun, hr⟩
    obtain ⟨s, hqs, hs⟩ := normalize_run_of_trace A hrun
    exact ⟨s, r, ⟨q, hq, hqs⟩, hs, hr⟩

end Paths

namespace Automaton

theorem realize_nonemptyFormula (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) :
    A.nonemptyFormula.Realize p ↔ ∃ w, A.Accepts p w := by
  simp only [nonemptyFormula, realize_any, Formula.realize_inf, realize_reach]
  have he : (fun q r => (A.edge q r).Realize p) =
      (fun q r => ∃ a, (A.interpret p).step q a r) := by
    funext q r
    exact propext (A.realize_edge p q r)
  rw [he]
  constructor
  · rintro ⟨q, r, hq, hrun, hr⟩
    obtain ⟨trace, ht⟩ := (exists_run_iff (A.interpret p) q r).mpr hrun
    exact ⟨trace.filterMap id, trace, rfl, q, r, hq, ht, hr⟩
  · rintro ⟨w, trace, _, q, r, hq, hrun, hr⟩
    exact ⟨q, r, hq, (exists_run_iff (A.interpret p) q r).mp ⟨trace, hrun⟩, hr⟩

/-- Guard-level epsilon elimination, preserving the same numbered state set. -/
def epsilonFree (A : Automaton L P n m arity) : Automaton L P n m arity where
  initial r := any n (fun q => A.initial q ⊓ reach A.silent q r)
  final := A.final
  silent _ _ := ⊥
  step s q r := any n (fun t => A.step s q t ⊓
    (reach A.silent t r).relabel Sum.inl)

/-- Ordinary data interpretation, used after epsilon elimination. -/
def dataInterpret (A : Automaton L P n m arity) {D : Type*} [L.Structure D]
    (p : P → D) : NSSE.NFA (Column D arity) (Fin n) where
  start q := (A.initial q).Realize p
  accept q := (A.final q).Realize p
  step q c r := (A.step c.1 q r).Realize (Sum.elim p c.2)

theorem epsilonFree_dataInterpret (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) :
    A.epsilonFree.dataInterpret p = normalize (A.interpret p) := by
  unfold dataInterpret epsilonFree normalize interpret
  congr 1
  · funext q
    apply propext
    simp only [realize_any, Formula.realize_inf, realize_reach, Silent]
  · funext q c r
    apply propext
    simp only [realize_any, Formula.realize_inf, Formula.realize_relabel,
      Function.comp_def, Sum.elim_inl, realize_reach, Silent]

/-- All visible words are preserved, including the empty word and arbitrary
parameter-labelled silent prefixes, interleavings, and suffixes. -/
theorem epsilonFree_correct (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D) (w : List (Column D arity)) :
    (A.epsilonFree.dataInterpret p).Accepts w ↔ A.Accepts p w := by
  rw [A.epsilonFree_dataInterpret p]
  exact normalize_accepts_iff (A.interpret p) w

theorem data_run_of_noSilent (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D)
    (hno : ∀ q r, ¬ (A.silent q r).Realize p)
    {q r : Fin n} {trace : List (Option (Column D arity))}
    (h : (A.interpret p).Runs q trace r) :
    (A.dataInterpret p).Runs q (trace.filterMap id) r := by
  induction h with
  | nil q => exact .nil q
  | @cons q r s a trace hstep _ ih =>
      cases a with
      | none => exact (hno q r hstep).elim
      | some c => exact .cons hstep ih

theorem some_trace_of_data_run (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D)
    {q r : Fin n} {w : List (Column D arity)}
    (h : (A.dataInterpret p).Runs q w r) :
    (A.interpret p).Runs q (w.map some) r := by
  induction h with
  | nil q => exact .nil q
  | cons hstep _ ih => exact .cons hstep ih

theorem accepts_iff_data_of_noSilent (A : Automaton L P n m arity)
    {D : Type*} [L.Structure D] (p : P → D)
    (hno : ∀ q r, ¬ (A.silent q r).Realize p) (w : List (Column D arity)) :
    A.Accepts p w ↔ (A.dataInterpret p).Accepts w := by
  constructor
  · rintro ⟨trace, rfl, q, r, hq, hrun, hr⟩
    exact ⟨q, r, hq, A.data_run_of_noSilent p hno hrun, hr⟩
  · rintro ⟨q, r, hq, hrun, hr⟩
    refine ⟨w.map some, ?_, q, r, hq, A.some_trace_of_data_run p hrun, hr⟩
    simp

end Automaton

end NSSE.SymbolicAutomata
