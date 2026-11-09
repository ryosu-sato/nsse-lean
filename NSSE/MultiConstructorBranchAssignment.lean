import NSSE.MultiConstructorBranchLocal

/-! Exact branch/assignment correspondence using the original raw token
fold and literal factor equality. The selected head stream is computed
without consulting branch acceptance or a model. -/
namespace NSSE.MultiConstructorBranchAssignment
open MultiConstructorConstraints MultiConstructorRawTrace MultiConstructorTrees
open MultiConstructorBranch MultiConstructorBranchTrace MultiConstructorBranchLocal
open P0DZBranch P0DZTrace P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

def value (C : Parameters arity n) (w : List (Fin D)) (s : Bool) (k : Nat) : Label H :=
  if k < w.length then .node (output C (walk C (branch C D).initial (w.take k)))
  else if s then C.endY else C.endX

theorem label_exact (C : Parameters arity n) (w : List (Fin D))
    (hc : Complete (branch C D) w) (s : Bool) (k : Nat) :
    labelAt (branch C D) w s k = value C w s k := by
  by_cases hk : k < w.length
  · obtain ⟨q,hq⟩ := complete_prefix (branch C D) w hc k hk
    rw [value,if_pos hk]
    rw [label_proper _ _ k hk q hq s,proper_walk C (w.take k) (branch C D).initial q hq]
    rfl
  · obtain ⟨t,ht⟩ := complete_terminal (branch C D) w hc
    rw [value,if_neg hk]
    unfold labelAt stateAt
    rw [if_neg hk,ht]
    rfl

def Rays (C : Parameters arity n) (w : List (Fin D)) : Prop :=
  ∀ a, a ≤ w.length → ∀ b, b ≤ w.length →
    (∃ u ∈ (rawWord C (initial C.input C.left C.right) (w.take a)).1,
     ∃ v ∈ (rawWord C (initial C.input C.left C.right) (w.take b)).2, Support C.input u v) →
    ∀ l, l ≤ w.length → a+l ≤ w.length → b+l ≤ w.length → WordMatch w a b l →
      Agree (value C w false (a+l)) (value C w true (b+l))

theorem safe_iff (C : Parameters arity n) (w : List (Fin D))
    (hc : Complete (branch C D) w) : Safe (branch C D) w ↔ Rays C w := by
  constructor
  · intro hs a ha b hb hborn l hl hal hbl hm
    have hh := hs a ha b hb false true (Or.inr (by decide))
      ((bornAt_exact C w hc a b ha hb).mpr hborn) l hl hal hbl hm
    simpa only [label_exact C w hc] using hh
  · intro hr a ha b hb s t _ hborn
    obtain ⟨q,r,hq,hr',hbirth⟩ := hborn
    have hs : s = false := hbirth.1
    have ht : t = true := hbirth.2.1
    subst s; subst t
    have hb' : bornAt (branch C D) w a false b true := ⟨q,r,hq,hr',hbirth⟩
    intro l hl hal hbl hm
    have hh := hr a ha b hb ((bornAt_exact C w hc a b ha hb).mp hb') l hl hal hbl hm
    simpa only [label_exact C w hc] using hh

def Assignment (C : Parameters arity n) (w : List (Fin D)) : Prop :=
  LocalRun C (branch C D).initial w ∧ Rays C w

theorem accepted_iff (C : Parameters arity n) (w : List (Fin D)) :
    Accepted (branch C D) w ↔ Assignment C w := by
  constructor
  · rintro ⟨hc,hs⟩
    exact ⟨(complete_iff C w).mp hc,(safe_iff C w hc).mp hs⟩
  · rintro ⟨hl,hr⟩
    have hc := (complete_iff C w).mpr hl
    exact ⟨hc,(safe_iff C w hc).mpr hr⟩

theorem inspect_correct (C : Parameters arity n) (w : List (Fin D)) :
    P0DZDecision.inspect (branch C D) (birthDecision C D) w = true ↔ Assignment C w :=
  (P0DZDecision.inspect_correct _ _ w).trans (accepted_iff C w)

def assignmentDecision (C : Parameters arity n) (w : List (Fin D)) : Decidable (Assignment C w) :=
  decidable_of_iff (P0DZDecision.inspect (branch C D) (birthDecision C D) w = true)
    (inspect_correct C w)

end NSSE.MultiConstructorBranchAssignment
