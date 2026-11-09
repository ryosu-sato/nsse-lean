import NSSE.MultiVarianceBranchTrace

/-! Exact all-physical-rail assignment semantics of the concrete signed
branch. Matching factors are RAW child indices. Both temporal orders,
same-side rays and zero-offset cross-side births are quantified. -/
namespace NSSE.MultiVarianceBranchAssignment
open MultiConstructorTrees (Label)
open MultiVarianceEncoding MultiVarianceSpineTokens MultiVarianceBranch
open MultiVarianceBranchLocal MultiVarianceBranchTrace
open P0DZBranch P0DZTrace P0ProperWords
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}
variable (pol : Polarity arity)

def value (C : Parameters arity n) (w : List (Fin D)) (s : Bool) (k : Nat) : Label H :=
  if k < w.length then .node (output C (walk pol C (branch pol C D).initial (w.take k)))
  else if s then C.endY else C.endX

theorem label_exact (C : Parameters arity n) (w : List (Fin D))
    (hc : Complete (branch pol C D) w) (s : Bool) (k : Nat) :
    labelAt (branch pol C D) w s k = value pol C w s k := by
  by_cases hk : k < w.length
  · obtain ⟨q,hq⟩ := complete_prefix (branch pol C D) w hc k hk
    rw [value,if_pos hk]
    rw [label_proper _ _ k hk q hq s,proper_walk pol C (w.take k) (branch pol C D).initial q hq]
    rfl
  · obtain ⟨t,ht⟩ := complete_terminal (branch pol C D) w hc
    rw [value,if_neg hk]
    unfold labelAt stateAt
    rw [if_neg hk,ht]
    rfl

def Rays (C : Parameters arity n) (w : List (Fin D)) : Prop :=
  ∀ a, a ≤ w.length → ∀ b, b ≤ w.length → ∀ s t,
    RawBirth (walk pol C (branch pol C D).initial (w.take a)).1 s
      (walk pol C (branch pol C D).initial (w.take b)).1 t →
    ∀ l, l ≤ w.length → a+l ≤ w.length → b+l ≤ w.length → WordMatch w a b l →
      Agree (value pol C w s (a+l)) (value pol C w t (b+l))

theorem safe_iff (C : Parameters arity n) (w : List (Fin D))
    (hc : Complete (branch pol C D) w) : Safe (branch pol C D) w ↔ Rays pol C w := by
  constructor
  · intro hs a ha b hb s t hborn l hl hal hbl hm
    have hd : a ≠ b ∨ s ≠ t := by
      by_cases hab : a=b
      · subst b
        right
        intro hst
        subst t
        exact no_same_vertex_birth _ s hborn
      · exact Or.inl hab
    have hh := hs a ha b hb s t hd
      ((bornAt_exact pol C w hc a b ha hb s t).mpr hborn) l hl hal hbl hm
    simpa only [label_exact pol C w hc] using hh
  · intro hr a ha b hb s t _ hborn l hl hal hbl hm
    have hh := hr a ha b hb s t ((bornAt_exact pol C w hc a b ha hb s t).mp hborn)
      l hl hal hbl hm
    simpa only [label_exact pol C w hc] using hh

def Assignment (C : Parameters arity n) (w : List (Fin D)) : Prop :=
  LocalRun pol C (branch pol C D).initial w ∧ Rays pol C w

theorem accepted_iff (C : Parameters arity n) (w : List (Fin D)) :
    Accepted (branch pol C D) w ↔ Assignment pol C w := by
  constructor
  · rintro ⟨hc,hs⟩
    exact ⟨(complete_iff pol C w).mp hc,(safe_iff pol C w hc).mp hs⟩
  · rintro ⟨hl,hr⟩
    have hc := (complete_iff pol C w).mpr hl
    exact ⟨hc,(safe_iff pol C w hc).mpr hr⟩

theorem inspect_correct (C : Parameters arity n) (w : List (Fin D)) :
    P0DZDecision.inspect (branch pol C D) (birthDecision pol C D) w = true ↔ Assignment pol C w :=
  (P0DZDecision.inspect_correct _ _ w).trans (accepted_iff pol C w)

def assignmentDecision (C : Parameters arity n) (w : List (Fin D)) : Decidable (Assignment pol C w) :=
  decidable_of_iff (P0DZDecision.inspect (branch pol C D) (birthDecision pol C D) w = true)
    (inspect_correct pol C w)

end NSSE.MultiVarianceBranchAssignment
