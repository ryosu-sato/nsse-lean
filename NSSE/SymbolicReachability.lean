import Mathlib.ModelTheory.Semantics
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Relation

/-!
# Effective first-order reachability with shared parameters

All constructions below operate on actual first-order syntax. They do not
inspect a structure, a parameter valuation, or satisfiability of a guard.
Finite state elimination gives reflexive/transitive reachability, including
zero-length paths. Only explicitly designated column variables are bound.
-/

namespace NSSE.SymbolicReachability

open FirstOrder FirstOrder.Language

universe u v w z
variable {L : FirstOrder.Language.{u, v}} {P : Type w} {Q : Type z}

/-- An explicitly enumerated disjunction; no choice of a finite enumeration. -/
def any (n : Nat) (f : Fin n → L.Formula P) : L.Formula P :=
  ((List.finRange n).map f).foldr (· ⊔ ·) ⊥

/-- Bind the indicated current-column variables, leaving every parameter free. -/
def closeColumn {k : Nat} (f : L.Formula (P ⊕ Fin k)) : L.Formula P :=
  (BoundedFormula.relabel (fun x => x) f).exs

section Semantics

variable {D : Type*} [L.Structure D] (p : P → D)

@[simp] theorem realize_any (n : Nat) (f : Fin n → L.Formula P) :
    (any n f).Realize p ↔ ∃ i, (f i).Realize p := by
  unfold any Formula.Realize
  simp only [BoundedFormula.realize_foldr_sup, List.mem_map]
  constructor
  · rintro ⟨_, ⟨i, _, rfl⟩, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨f i, ⟨i, List.mem_finRange i, rfl⟩, h⟩

@[simp] theorem realize_closeColumn {k : Nat} (f : L.Formula (P ⊕ Fin k)) :
    (closeColumn f).Realize p ↔ ∃ xs : Fin k → D, f.Realize (Sum.elim p xs) := by
  unfold closeColumn
  rw [BoundedFormula.realize_exs]
  apply exists_congr
  intro xs
  rw [BoundedFormula.realize_relabel]
  simpa only [Function.comp_def, Fin.castAdd_zero] using
    Formula.boundedFormula_realize_eq_realize f (Sum.elim p xs) (xs ∘ Fin.natAdd k)

end Semantics

/-- One finite Floyd--Warshall state elimination, as Boolean formula syntax. -/
def via (W : Q → Q → L.Formula P) (k : Q) (a b : Q) : L.Formula P :=
  W a b ⊔ (W a k ⊓ W k b)

def eliminate (W : Q → Q → L.Formula P) : List Q → Q → Q → L.Formula P
  | [] => W
  | k :: ks => via (eliminate W ks) k

section Elimination

variable {D : Type*} [L.Structure D] {p : P → D}

def ClosedAt (W : Q → Q → L.Formula P) (p : P → D) (k : Q) : Prop :=
  ∀ a b, (W a k).Realize p → (W k b).Realize p → (W a b).Realize p

theorem via_includes (W : Q → Q → L.Formula P) (k a b : Q)
    (h : (W a b).Realize p) : (via W k a b).Realize p := by
  simp only [via, Formula.realize_sup, Formula.realize_inf]
  exact Or.inl h

theorem via_closed (W : Q → Q → L.Formula P) (k : Q) :
    ClosedAt (via W k) p k := by
  intro a b ha hb
  simp only [via, Formula.realize_sup, Formula.realize_inf] at ha hb ⊢
  exact Or.inr ⟨ha.elim id And.left, hb.elim id And.right⟩

theorem via_preserves_closed (W : Q → Q → L.Formula P) (k t : Q)
    (h : ClosedAt W p t) : ClosedAt (via W k) p t := by
  intro a b ha hb
  simp only [via, Formula.realize_sup, Formula.realize_inf] at ha hb ⊢
  rcases ha with ha | ⟨hak, hkt⟩ <;> rcases hb with hb | ⟨htk, hkb⟩
  · exact Or.inl (h a b ha hb)
  · exact Or.inr ⟨h a k ha htk, hkb⟩
  · exact Or.inr ⟨hak, h k b hkt hb⟩
  · exact Or.inr ⟨hak, hkb⟩

theorem eliminate_includes (W : Q → Q → L.Formula P) (ks : List Q) (a b : Q)
    (h : (W a b).Realize p) : (eliminate W ks a b).Realize p := by
  induction ks with
  | nil => exact h
  | cons k ks ih => exact via_includes _ k a b ih

theorem eliminate_preserves_closed (W : Q → Q → L.Formula P) (ks : List Q) (t : Q)
    (h : ClosedAt W p t) : ClosedAt (eliminate W ks) p t := by
  induction ks with
  | nil => exact h
  | cons k ks ih => exact via_preserves_closed _ k t ih

theorem eliminate_closed (W : Q → Q → L.Formula P) (ks : List Q) (t : Q)
    (ht : t ∈ ks) : ClosedAt (eliminate W ks) p t := by
  induction ks with
  | nil => simp at ht
  | cons k ks ih =>
      rcases List.mem_cons.mp ht with rfl | ht
      · exact via_closed _ t
      · exact via_preserves_closed _ k t (ih ht)

theorem eliminate_sound (W : Q → Q → L.Formula P) (ks : List Q)
    (R : Q → Q → Prop) (htrans : Transitive R)
    (hW : ∀ a b, (W a b).Realize p → R a b) :
    ∀ a b, (eliminate W ks a b).Realize p → R a b := by
  induction ks with
  | nil => exact hW
  | cons k ks ih =>
      intro a b hab
      simp only [eliminate, via, Formula.realize_sup, Formula.realize_inf] at hab
      rcases hab with hab | ⟨hak, hkb⟩
      · exact ih a b hab
      · exact htrans (ih a k hak) (ih k b hkb)

end Elimination

def reflexiveEdges {n : Nat} (W : Fin n → Fin n → L.Formula P)
    (a b : Fin n) : L.Formula P :=
  (if a = b then ⊤ else ⊥) ⊔ W a b

/-- Complete finite path closure, including the identity path. -/
def reach {n : Nat} (W : Fin n → Fin n → L.Formula P) :
    Fin n → Fin n → L.Formula P :=
  eliminate (reflexiveEdges W) (List.finRange n)

section Reachability

variable {D : Type*} [L.Structure D] (p : P → D)

@[simp] theorem realize_reflexiveEdges {n : Nat}
    (W : Fin n → Fin n → L.Formula P) (a b : Fin n) :
    (reflexiveEdges W a b).Realize p ↔ a = b ∨ (W a b).Realize p := by
  by_cases h : a = b <;> simp [reflexiveEdges, h]

theorem realize_reach {n : Nat} (W : Fin n → Fin n → L.Formula P)
    (a b : Fin n) :
    (reach W a b).Realize p ↔
      Relation.ReflTransGen (fun q r => (W q r).Realize p) a b := by
  constructor
  · apply eliminate_sound (reflexiveEdges W) (List.finRange n)
      (Relation.ReflTransGen (fun q r => (W q r).Realize p))
    · exact fun _ _ _ h₁ h₂ => h₁.trans h₂
    · intro q r h
      rcases (realize_reflexiveEdges p W q r).mp h with rfl | h
      · exact .refl
      · exact .single h
  · intro h
    induction h with
    | refl =>
        apply eliminate_includes
        exact (realize_reflexiveEdges p W a a).mpr (Or.inl rfl)
    | @tail b c _ hbc ih =>
        apply eliminate_closed (reflexiveEdges W) (List.finRange n) b
          (List.mem_finRange b) a c ih
        apply eliminate_includes
        exact (realize_reflexiveEdges p W b c).mpr (Or.inr hbc)

end Reachability

end NSSE.SymbolicReachability
