import NSSE.CommonCutSmallTuple
import NSSE.UnifiedBlockPresentation

/-! # Bounded atomic diagrams for the actual unified block presentation -/

namespace NSSE.UnifiedBlockSmallTuple

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks GuardedBlockRelation
open UnifiedBlockPresentation

universe u v w
variable {L : FirstOrder.Language.{u,v}} {P : Type w}

structure Test where
  states : Nat
  row : Row L P states
  ends : Ends states
  first : Bool

def tests {n : Nat} (R : Row L P n) : List (Test (L := L) (P := P)) :=
  (endpoints n).flatMap fun e => [⟨n,R,e,false⟩, ⟨n,R,e,true⟩]

theorem mem_tests {n : Nat} (R : Row L P n) (e : Ends n) (first : Bool) :
    ⟨n,R,e,first⟩ ∈ tests R := by
  apply List.mem_flatMap.mpr
  refine ⟨e, mem_endpoints _ _, ?_⟩
  cases first <;> simp

def allTests {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) : List (Test (L := L) (P := P)) :=
  tests C ++ (List.finRange k).flatMap (fun i => tests (rows i))

theorem candidate_mem {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (e : Ends c) (first : Bool) :
    ⟨c,C,e,first⟩ ∈ allTests rows C :=
  List.mem_append_left _ (mem_tests C e first)

theorem row_mem {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (i : Fin k) (e : Ends (ns i)) (first : Bool) :
    ⟨ns i,rows i,e,first⟩ ∈ allTests rows C := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i, mem_tests _ _ _⟩

def testStates (ts : List (Test (L := L) (P := P))) (i : Fin ts.length) : Nat :=
  (ts.get i).states

def bound {k c : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (q : Nat) : Nat :=
  (q*q+1) * 2 ^ CombinedSuffixSummary.exponent (b := 1) (testStates (allTests rows C))

theorem block_preserved {D : Type*} [L.Structure D] {n q : Nat}
    (R : Row L P n) (seed last : P) (p : P → D) (v w : Fin q → List D)
    (hH : ∀ e first i j, R.LiteralH e seed last first p (v i) (v j) ↔
      R.LiteralH e seed last first p (w i) (w j))
    (hD : ∀ i s t, (R.dataNFA p).Runs s (v i) t ↔ (R.dataNFA p).Runs s (w i) t) :
    letI := BlockRelationPresentation.model R seed last p
    ∀ a (rel : BlockRelationPresentation.Rel n a) (args : Fin a → Fin q),
      Structure.RelMap (L := BlockRelationPresentation.language n) rel (v ∘ args) ↔
        Structure.RelMap (L := BlockRelationPresentation.language n) rel (w ∘ args) := by
  letI := BlockRelationPresentation.model R seed last p
  intro a rel args
  cases rel with
  | block s t =>
    have hv : v ∘ args = ![v (args 0)] := by funext i; fin_cases i; rfl
    have hw : w ∘ args = ![w (args 0)] := by funext i; fin_cases i; rfl
    rw [hv, hw, BlockRelationPresentation.block_interpret, BlockRelationPresentation.block_interpret,
      runs_append_singleton, runs_append_singleton]
    simp only [hD]
  | guarded e first =>
    have hv : v ∘ args = ![v (args 0),v (args 1)] := by funext i; fin_cases i <;> rfl
    have hw : w ∘ args = ![w (args 0),w (args 1)] := by funext i; fin_cases i <;> rfl
    rw [hv, hw, BlockRelationPresentation.guarded_interpret, BlockRelationPresentation.guarded_interpret]
    exact hH e first (args 0) (args 1)
  | initial s =>
    have he : v ∘ args = w ∘ args := by funext i; exact Fin.elim0 i
    rw [he]
  | final s =>
    have he : v ∘ args = w ∘ args := by funext i; exact Fin.elim0 i
    rw [he]

theorem exists_small_diagram {D : Type*} [L.Structure D] {k c q : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) (p : P → D) (w : Fin q → List D) :
    letI := model rows C seed last p
    ∃ v : Fin q → List D,
      (∀ i, (v i).length ≤ bound rows C q) ∧
      (∀ i j, v i = v j ↔ w i = w j) ∧
      (∀ a (rel : Rel ns c a) (args : Fin a → Fin q),
        Structure.RelMap (L := language ns c) rel (v ∘ args) ↔
          Structure.RelMap (L := language ns c) rel (w ∘ args)) := by
  letI := model rows C seed last p
  let ts := allTests rows C
  obtain ⟨v, hv, he, hH, hD, hN⟩ := CommonCutSmallTuple.exists_small_literal_tuple (testStates ts)
    (fun a => (ts.get a).row) (fun a => (ts.get a).ends)
    seed last (fun a => (ts.get a).first) p ![p last] w
  have htH (t : Test (L := L) (P := P)) (ht : t ∈ ts) :
      ∀ i j, t.row.LiteralH t.ends seed last t.first p (v i) (v j) ↔
        t.row.LiteralH t.ends seed last t.first p (w i) (w j) := by
    obtain ⟨a, ha⟩ := List.mem_iff_get.mp ht
    have hh := hH a
    change ∀ i j, (ts.get a).row.LiteralH (ts.get a).ends seed last (ts.get a).first p (v i) (v j) ↔
      (ts.get a).row.LiteralH (ts.get a).ends seed last (ts.get a).first p (w i) (w j) at hh
    rw [ha] at hh
    exact hh
  have htD (t : Test (L := L) (P := P)) (ht : t ∈ ts) :
      ∀ i s r, (t.row.dataNFA p).Runs s (v i) r ↔ (t.row.dataNFA p).Runs s (w i) r := by
    obtain ⟨a, ha⟩ := List.mem_iff_get.mp ht
    have hh := hD a
    change ∀ i s r, ((ts.get a).row.dataNFA p).Runs s (v i) r ↔
      ((ts.get a).row.dataNFA p).Runs s (w i) r at hh
    rw [ha] at hh
    exact hh
  refine ⟨v, hv, he, ?_⟩
  intro a rel args
  cases rel with
  | row i r =>
    apply block_preserved (rows i) seed last p v w
    · intro e first
      exact htH ⟨_,rows i,e,first⟩ (row_mem rows C i e first)
    · intro j s t
      exact htD ⟨_,rows i,⟨s,t,s,t⟩,false⟩ (row_mem rows C i _ false) j s t
  | candidate r =>
    apply block_preserved C seed last p v w
    · intro e first
      exact htH ⟨_,C,e,first⟩ (candidate_mem rows C e first)
    · intro j s t
      exact htD ⟨_,C,⟨s,t,s,t⟩,false⟩ (candidate_mem rows C _ false) j s t
  | noA =>
    have h₁ : v ∘ args = ![v (args 0)] := by funext i; fin_cases i; rfl
    have h₂ : w ∘ args = ![w (args 0)] := by funext i; fin_cases i; rfl
    rw [h₁,h₂,noA_interpret,noA_interpret]
    exact hN 0 (args 0)

end NSSE.UnifiedBlockSmallTuple
