import NSSE.RowLanguageTransport
import NSSE.SeparatorFreePresentation

/-! # One automatic word structure for an entire finite row family and candidate -/

namespace NSSE.UnifiedBlockPresentation

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UniformWordLowering
open ConvolutionShapes GuardedRowFiring RowLanguageTransport

universe u v w
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {k c : Nat} {ns : Fin k → Nat}

inductive Rel (ns : Fin k → Nat) (c : Nat) : Nat → Type
  | row (i : Fin k) {a : Nat} (r : BlockRelationPresentation.Rel (ns i) a) : Rel ns c a
  | candidate {a : Nat} (r : BlockRelationPresentation.Rel c a) : Rel ns c a
  | noA : Rel ns c 1

abbrev language (ns : Fin k → Nat) (c : Nat) := wordLanguage (Rel ns c)

def rowHom (ns : Fin k → Nat) (c : Nat) (i : Fin k) :
    BlockRelationPresentation.language (ns i) →ᴸ language ns c where
  onFunction := fun {_} f => nomatch f
  onRelation := fun {_} r => .row i r

def candidateHom (ns : Fin k → Nat) (c : Nat) :
    BlockRelationPresentation.language c →ᴸ language ns c where
  onFunction := fun {_} f => nomatch f
  onRelation := fun {_} r => .candidate r

def relationAutomaton (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P) :
    {a : Nat} → Rel ns c a → Compiled L P a
  | _, .row i r => BlockRelationPresentation.relationAutomaton (rows i) seed last r
  | _, .candidate r => BlockRelationPresentation.relationAutomaton C seed last r
  | _, .noA => ⟨_, SeparatorFreePresentation.compile (L := L) last⟩

def presentation (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P) :
    Presentation L P (Rel ns c) where
  states r := (relationAutomaton rows C seed last r).1
  automaton r := (relationAutomaton rows C seed last r).2

def model (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) : (language ns c).Structure (List D) :=
  UniformWordLowering.model (presentation rows C seed last) p (reverseEquiv D)

theorem row_expansion (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) (i : Fin k) :
    letI := model rows C seed last p
    letI := BlockRelationPresentation.model (rows i) seed last p
    (rowHom ns c i).IsExpansionOn (List D) := by
  letI := model rows C seed last p
  letI := BlockRelationPresentation.model (rows i) seed last p
  exact {
    map_onFunction := fun {_} f _ => nomatch f
    map_onRelation := fun {_} _ _ => rfl }

theorem candidate_expansion (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) :
    letI := model rows C seed last p
    letI := BlockRelationPresentation.model C seed last p
    (candidateHom ns c).IsExpansionOn (List D) := by
  letI := model rows C seed last p
  letI := BlockRelationPresentation.model C seed last p
  exact {
    map_onFunction := fun {_} f _ => nomatch f
    map_onRelation := fun {_} _ _ => rfl }

theorem noA_interpret (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c) (seed last : P)
    {D : Type*} [L.Structure D] (p : P → D) (U : List D) :
    letI := model rows C seed last p
    FirstOrder.Language.Structure.RelMap (L := language ns c) .noA ![U] ↔ p last ∉ U := by
  change tupleAccepts (SeparatorFreePresentation.compile (L := L) last) p
    ((reverseEquiv D) ∘ ![U]) ↔ _
  have ht : (reverseEquiv D) ∘ ![U] = ![U.reverse] := by funext i; fin_cases i; rfl
  rw [ht, SeparatorFreePresentation.compile_correct]

def compileRow (ns : Fin k → Nat) (c : Nat) (i : Fin k) (e : Ends (ns i)) (first : Bool) :
    Row (language ns c) Empty (SymbolicOutsideController.states (ns i)).length :=
  mapRow (rowHom ns c i) (SymbolicOutsideController.compile e first)

/-- Each row's certified firing transport now takes place inside the SAME
presented structure, alongside every other row and the candidate predicates. -/
theorem positive_fires_iff_shared (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] (p : P → D) (i : Fin k)
    (bs : List (List D)) (hNoA : TerminalCutGeometry.NoA (p last) bs) :
    PositiveFires (rows i) p (p seed) (TerminalBorderRank.decodeBlocks (p last) bs) ↔
      letI := model rows C seed last p
      ∃ e : Ends (ns i), ∃ first : Bool,
        Fires (compileRow ns c i e first) (Empty.elim : Empty → List D) (bs.head?.getD []) bs.tail := by
  letI := model rows C seed last p
  letI := BlockRelationPresentation.model (rows i) seed last p
  letI := row_expansion rows C seed last p i
  rw [positive_fires_iff_new (rows i) seed last p bs hNoA]
  simp only [compileRow, fires_map]

theorem avoids_family_iff_shared (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] (p : P → D)
    (bs : List (List D)) (hNoA : TerminalCutGeometry.NoA (p last) bs) :
    (∀ i, ¬ PositiveFires (rows i) p (p seed) (TerminalBorderRank.decodeBlocks (p last) bs)) ↔
      letI := model rows C seed last p
      ∀ i, ∀ e : Ends (ns i), ∀ first : Bool,
        ¬ Fires (compileRow ns c i e first) (Empty.elim : Empty → List D) (bs.head?.getD []) bs.tail := by
  letI := model rows C seed last p
  simp only [positive_fires_iff_shared rows C seed last p _ bs hNoA, not_exists]

/-- All endpoint contexts are generated by finite syntax, including n=0. -/
def endpoints (n : Nat) : List (Ends n) :=
  (List.finRange n).flatMap fun r0 => (List.finRange n).flatMap fun r1 =>
    (List.finRange n).flatMap fun t0 => (List.finRange n).map fun t1 => ⟨r0, r1, t0, t1⟩

theorem mem_endpoints (n : Nat) (e : Ends n) : e ∈ endpoints n := by
  cases e with
  | mk r0 r1 t0 t1 => simp [endpoints]

abbrev Branch (ns : Fin k → Nat) := (i : Fin k) × (Ends (ns i) × Bool)

def branches (ns : Fin k → Nat) : List (Branch ns) :=
  (List.finRange k).flatMap fun i => (endpoints (ns i)).flatMap fun e =>
    [⟨i, e, false⟩, ⟨i, e, true⟩]

theorem mem_branches (ns : Fin k → Nat) (b : Branch ns) : b ∈ branches ns := by
  rcases b with ⟨i, e, b⟩
  apply List.mem_flatMap.mpr
  refine ⟨i, by simp, List.mem_flatMap.mpr ⟨e, mem_endpoints _ _, ?_⟩⟩
  cases b <;> simp

def branchAt (ns : Fin k → Nat) (i : Fin (branches ns).length) : Branch ns :=
  (branches ns).get i

theorem branchAt_surjective (ns : Fin k → Nat) : Function.Surjective (branchAt ns) := by
  intro b
  exact List.mem_iff_get.mp (mem_branches ns b)

def familyStates (ns : Fin k → Nat) (i : Fin (branches ns).length) : Nat :=
  (SymbolicOutsideController.states (ns (branchAt ns i).1)).length

/-- The actual Fin-indexed finite family accepted by the next recursion. -/
def familyRows (ns : Fin k → Nat) (c : Nat) (i : Fin (branches ns).length) :
    Row (language ns c) Empty (familyStates ns i) :=
  compileRow ns c (branchAt ns i).1 (branchAt ns i).2.1 (branchAt ns i).2.2

theorem avoids_enumerated_family (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) {D : Type*} [L.Structure D] (p : P → D)
    (bs : List (List D)) (hNoA : TerminalCutGeometry.NoA (p last) bs) :
    (∀ i, ¬ PositiveFires (rows i) p (p seed) (TerminalBorderRank.decodeBlocks (p last) bs)) ↔
      letI := model rows C seed last p
      ∀ i : Fin (branches ns).length,
        ¬ Fires (familyRows ns c i) (Empty.elim : Empty → List D) (bs.head?.getD []) bs.tail := by
  letI := model rows C seed last p
  rw [avoids_family_iff_shared rows C seed last p bs hNoA]
  constructor
  · intro h i
    exact h (branchAt ns i).1 (branchAt ns i).2.1 (branchAt ns i).2.2
  · intro h i e first
    obtain ⟨b, hb⟩ := branchAt_surjective ns ⟨i, e, first⟩
    have hh := h b
    dsimp only [familyRows, familyStates] at hh
    rw [hb] at hh
    exact hh

end NSSE.UnifiedBlockPresentation
