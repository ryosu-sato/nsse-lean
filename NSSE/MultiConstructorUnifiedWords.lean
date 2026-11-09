import NSSE.MultiConstructorBranchAssignment
import Mathlib.Data.Fintype.Pi

/-! Selector-independent unified words on actual original token traces.
Heads are indexed only by proper positions, so epsilon remains meaningful
even for an empty constructor signature. -/
namespace NSSE.MultiConstructorUnifiedWords
open MultiConstructorConstraints MultiConstructorSupportDecision MultiConstructorTokens
open MultiConstructorRawTrace MultiConstructorRawValidity MultiConstructorTrees
open P0ProperWords P0DZBranch
variable {H : Type*} [DecidableEq H] {arity : H → Nat} {n D : Nat}

deriving instance Fintype for Label

def row (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (k : Nat) : Row n :=
  (w.take k).foldl (fun s i => step phi s i.val) (initial phi x y)

def value (w : List (Fin D)) (heads : Fin w.length → H) (ex ey : Label H)
    (s : Bool) (k : Nat) : Label H :=
  if hk : k < w.length then .node (heads ⟨k,hk⟩) else if s then ey else ex

def Local (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) : Prop :=
  ∀ k : Fin w.length, Valid phi (row phi x y w k.val) ∧
    Compatible phi (row phi x y w k.val) (heads k) ∧ w[k.val].val < arity (heads k)

def Final (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (ex ey : Label H) : Prop :=
  Valid phi (row phi x y w w.length) ∧ UpperDomain phi (row phi x y w w.length) ex ∧
    LowerDomain phi (row phi x y w w.length) ey ∧ ex ≠ ey

def Born (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (a b : Nat) : Prop :=
  ∃ u ∈ (row phi x y w a).1, ∃ v ∈ (row phi x y w b).2, Support phi u v

def Rays (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : Label H) : Prop :=
  ∀ a b l : Fin (w.length+1), Born phi x y w a.val b.val →
    a.val+l.val ≤ w.length → b.val+l.val ≤ w.length → WordMatch w a.val b.val l.val →
      Agree (value w heads ex ey false (a.val+l.val)) (value w heads ex ey true (b.val+l.val))

def Assignment (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : Label H) : Prop :=
  Local phi x y w heads ∧ Final phi x y w ex ey ∧ Rays phi x y w heads ex ey

def Witness (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) : Prop :=
  ∃ heads ex ey, Assignment phi x y w heads ex ey

def bornDecision (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (a b : Nat) :
    Decidable (Born phi x y w a b) := by
  letI := supportDecision phi
  unfold Born
  infer_instance

def localDecision (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) : Decidable (Local phi x y w heads) := by
  letI := validDecision phi
  letI := compatibleDecision phi
  unfold Local
  infer_instance

def finalDecision (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) (ex ey : Label H) :
    Decidable (Final phi x y w ex ey) := by
  letI := validDecision phi
  letI := upperDomainDecision phi
  letI := lowerDomainDecision phi
  unfold Final
  infer_instance

def raysDecision (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : Label H) : Decidable (Rays phi x y w heads ex ey) := by
  letI := bornDecision phi x y w
  unfold Rays WordMatch
  infer_instance

def assignmentDecision (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D))
    (heads : Fin w.length → H) (ex ey : Label H) : Decidable (Assignment phi x y w heads ex ey) := by
  letI := localDecision phi x y w heads
  letI := finalDecision phi x y w ex ey
  letI := raysDecision phi x y w heads ex ey
  unfold Assignment
  infer_instance

def witnessDecision [Fintype H] (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) :
    Decidable (Witness phi x y w) := by
  letI := assignmentDecision phi x y w
  unfold Witness
  infer_instance

def inspect [Fintype H] (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) : Bool :=
  @decide (Witness phi x y w) (witnessDecision phi x y w)

theorem inspect_correct [Fintype H] (phi : Constraints arity n) (x y : Fin n) (w : List (Fin D)) :
    inspect phi x y w = true ↔ Witness phi x y w := by
  unfold inspect
  simp only [decide_eq_true_eq]

end NSSE.MultiConstructorUnifiedWords
