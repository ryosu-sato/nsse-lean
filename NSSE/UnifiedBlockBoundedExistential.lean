import NSSE.UnifiedBlockSmallTuple
import Mathlib.ModelTheory.Complexity

/-! # Bounded witnesses for existential formulas of the actual block language -/

namespace NSSE.UnifiedBlockBoundedExistential

open FirstOrder FirstOrder.Language SymbolicGuardedBlocks UnifiedBlockPresentation

universe u v w r t

def variableOf {R : Nat → Type r} {α : Type t} :
    (UniformWordLowering.wordLanguage R).Term α → α
  | .var a => a
  | .func f _ => nomatch f

theorem realize_variableOf {R : Nat → Type r} {α : Type t} {M : Type*}
    [(UniformWordLowering.wordLanguage R).Structure M] (v : α → M)
    (t : (UniformWordLowering.wordLanguage R).Term α) :
    t.realize v = v (variableOf t) := by
  cases t with
  | var a => rfl
  | func f _ => cases f

/-- Exact atomic diagrams preserve arbitrary Boolean combinations, including
negative relation and equality occurrences. No positivity assumption is used. -/
theorem qf_diagram {R : Nat → Type r} {α : Type t} {M : Type*}
    [(UniformWordLowering.wordLanguage R).Structure M] {n q : Nat}
    (v w : Fin q → M)
    (he : ∀ i j, v i = v j ↔ w i = w j)
    (hr : ∀ a (rel : R a) (args : Fin a → Fin q),
      Structure.RelMap (L := UniformWordLowering.wordLanguage R) rel (v ∘ args) ↔
        Structure.RelMap (L := UniformWordLowering.wordLanguage R) rel (w ∘ args))
    (idx : α ⊕ Fin n → Fin q)
    (φ : (UniformWordLowering.wordLanguage R).BoundedFormula α n) (hφ : φ.IsQF) :
    φ.Realize (fun a => v (idx (.inl a))) (fun i => v (idx (.inr i))) ↔
      φ.Realize (fun a => w (idx (.inl a))) (fun i => w (idx (.inr i))) := by
  have ht (z : Fin q → M) (s : (UniformWordLowering.wordLanguage R).Term (α ⊕ Fin n)) :
      s.realize (Sum.elim (fun a => z (idx (.inl a))) (fun i => z (idx (.inr i)))) =
        z (idx (variableOf s)) := by
    rw [realize_variableOf]
    cases variableOf s <;> rfl
  induction hφ with
  | falsum => rfl
  | of_isAtomic h =>
    cases h with
    | equal s t =>
      simp only [BoundedFormula.realize_bdEqual, ht]
      exact he _ _
    | rel rel ts =>
      simp only [BoundedFormula.realize_rel, ht]
      exact hr _ rel (fun i => idx (variableOf (ts i)))
  | imp _ _ ih₁ ih₂ =>
    exact imp_congr ih₁ ih₂

variable {L : FirstOrder.Language.{u,v}} {P : Type w}

/-- Closed existential matrices have bounded witnesses in the actual model.
Scalar parameters of the presentation are held fixed. -/
theorem exists_bounded_iff {D : Type*} [L.Structure D] {k c q : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) (p : P → D)
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    letI := model rows C seed last p
    (∃ w : Fin q → List D, φ.Realize Empty.elim w) ↔
      ∃ v : Fin q → List D,
        (∀ i, (v i).length ≤ UnifiedBlockSmallTuple.bound rows C q) ∧
        φ.Realize Empty.elim v := by
  letI := model rows C seed last p
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, he, hr⟩ := UnifiedBlockSmallTuple.exists_small_diagram rows C seed last p w
    refine ⟨v, hv, ?_⟩
    have hh := qf_diagram v w he hr (Sum.elim Empty.elim id) φ hφ
    have ev : (fun a : Empty => v ((Sum.elim Empty.elim id) (.inl a))) = Empty.elim := by
      funext a; cases a
    have ew : (fun a : Empty => w ((Sum.elim Empty.elim id) (.inl a))) = Empty.elim := by
      funext a; cases a
    rw [ev, ew] at hh
    exact hh.mpr hw
  · rintro ⟨v, _, hv⟩
    exact ⟨v, hv⟩

/-- Syntactic existential closure, rather than a supplied witness interface. -/
theorem exs_bounded_iff {D : Type*} [L.Structure D] {k c q : Nat} {ns : Fin k → Nat}
    (rows : (i : Fin k) → Row L P (ns i)) (C : Row L P c)
    (seed last : P) (p : P → D)
    (φ : (language ns c).BoundedFormula Empty q) (hφ : φ.IsQF) :
    letI := model rows C seed last p
    φ.exs.Realize (Empty.elim : Empty → List D) ↔
      ∃ v : Fin q → List D,
        (∀ i, (v i).length ≤ UnifiedBlockSmallTuple.bound rows C q) ∧
        φ.Realize Empty.elim v := by
  letI := model rows C seed last p
  rw [BoundedFormula.realize_exs]
  exact exists_bounded_iff rows C seed last p φ hφ

end NSSE.UnifiedBlockBoundedExistential
