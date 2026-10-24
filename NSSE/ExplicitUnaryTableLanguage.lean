import NSSE.CountedRankEvaluationTower

/-! # Function-free unary language with materialized Boolean relation tables -/

namespace NSSE.ExplicitUnaryTableLanguage

open FirstOrder FirstOrder.Language

/-- A concrete linear list lookup; out-of-range entries denote false. -/
def lookup : List Bool → Nat → Bool × Nat
  | [], _ => (false,1)
  | b::_, 0 => (b,1)
  | _::bs, i+1 => let r := lookup bs i; (r.1,r.2+1)

theorem lookup_value (bs : List Bool) (i : Nat) : (lookup bs i).1 = (bs[i]?).getD false := by
  induction bs generalizing i with
  | nil => rfl
  | cons b bs ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [lookup, List.getElem?_cons_succ] using ih i

theorem lookup_steps (bs : List Bool) (i : Nat) : (lookup bs i).2 = min i bs.length+1 := by
  induction bs generalizing i with
  | nil => simp [lookup]
  | cons b bs ih =>
    cases i with
    | zero => simp [lookup]
    | succ i => simp [lookup, ih, Nat.succ_min_succ, Nat.add_assoc]

inductive Rel : Nat → Type
  | unary : List Bool → Rel 1

def language : FirstOrder.Language.{0,0} := UniformWordLowering.wordLanguage Rel

instance model (d : Nat) : language.Structure (Fin d) where
  funMap f := nomatch f
  RelMap r xs := match r with | .unary bs => (lookup bs (xs 0).val).1 = true

def relationDecision (d : Nat) : FiniteRankDecision.RelationDecision language (Fin d) :=
  by
  intro n r
  change Rel n at r
  cases r with
  | unary bs =>
    intro xs
    exact inferInstanceAs (Decidable ((lookup bs (xs 0).val).1 = true))

def tabulate {d : Nat} (f : Fin d → Bool) : List Bool := List.ofFn f

theorem tabulate_length {d : Nat} (f : Fin d → Bool) : (tabulate f).length = d := List.length_ofFn

theorem tabulate_correct {d : Nat} (f : Fin d → Bool) (x : Fin d) : (lookup (tabulate f) x.val).1 = f x := by
  rw [lookup_value]
  simp [tabulate]

theorem lookup_bound {d : Nat} (bs : List Bool) (x : Fin d) : (lookup bs x.val).2 ≤ d := by
  rw [lookup_steps]
  have := Nat.min_le_left x.val bs.length
  have := x.isLt
  omega

theorem tabulate_steps {d : Nat} (f : Fin d → Bool) (x : Fin d) :
    (lookup (tabulate f) x.val).2 = x.val+1 := by
  rw [lookup_steps, tabulate_length, Nat.min_eq_left (Nat.le_of_lt x.isLt)]

def truth {P : Type*} (b : Bool) : language.Formula P := if b then ⊤ else ⊥

def unary {P : Type*} (bs : List Bool) : language.Formula (P ⊕ Fin 1) :=
  Relations.formula₁ (.unary bs) (.var (.inr 0))

theorem truth_correct {d : Nat} {P : Type*} (b : Bool) (p : P → Fin d) :
    (truth b).Realize p ↔ b = true := by cases b <;> simp [truth]

theorem unary_correct {d : Nat} {P : Type*} (f : Fin d → Bool) (p : P → Fin d) (x : Fin d) :
    (unary (tabulate f)).Realize (Sum.elim p (fun _ => x)) ↔ f x = true := by
  change (lookup (tabulate f) x.val).1 = true ↔ _
  rw [tabulate_correct]

theorem truth_qf {P : Type*} (b : Bool) : (truth (P := P) b).IsQF := by
  cases b
  · exact BoundedFormula.isQF_bot
  · exact BoundedFormula.IsQF.top

theorem unary_qf {P : Type*} (bs : List Bool) : (unary (P := P) bs).IsQF :=
  BoundedFormula.IsAtomic.isQF (.rel _ _)

theorem truth_nodes {P : Type*} (b : Bool) :
    ExactReachabilitySize.nodes (truth (P := P) b) ≤ 3 := by
  cases b
  · change 1 ≤ 3; omega
  · change 3 ≤ 3; omega

theorem unary_nodes {P : Type*} (bs : List Bool) :
    ExactReachabilitySize.nodes (unary (P := P) bs) = 1 := rfl

end NSSE.ExplicitUnaryTableLanguage
